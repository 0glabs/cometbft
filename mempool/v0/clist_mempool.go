package v0

import (
	"bytes"
	"errors"
	"fmt"
	"math"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/config"
	"github.com/cometbft/cometbft/libs/clist"
	"github.com/cometbft/cometbft/libs/log"
	cmtmath "github.com/cometbft/cometbft/libs/math"
	cmtsync "github.com/cometbft/cometbft/libs/sync"
	"github.com/cometbft/cometbft/mempool"
	"github.com/cometbft/cometbft/p2p"
	"github.com/cometbft/cometbft/proxy"
	"github.com/cometbft/cometbft/types"
)

const pendingQueuePreallocationSize int = 10

// CListMempool is an ordered in-memory pool for transactions before they are
// proposed in a consensus round. Transaction validity is checked using the
// CheckTx abci message before the transaction is added to the pool. The
// mempool uses a concurrent list structure for storing transactions that can
// be efficiently accessed by multiple concurrent readers.
type CListMempool struct {
	// Atomic integers
	height   int64 // the last block Update()'d to
	txsBytes int64 // total size of mempool, in bytes

	// notify listeners (ie. consensus) when txs are available
	notifiedTxsAvailable bool
	txsAvailable         chan struct{} // fires once for each height, when the mempool is not empty

	config *config.MempoolConfig

	// Exclusive mutex for Update method to prevent concurrent execution of
	// CheckTx or ReapMaxBytesMaxGas(ReapMaxTxs) methods.
	updateMtx cmtsync.RWMutex
	preCheck  mempool.PreCheckFunc
	postCheck mempool.PostCheckFunc

	txs          *clist.CList // concurrent linked-list of good txs
	proxyAppConn proxy.AppConnMempool

	// Track whether we're rechecking txs.
	// These are not protected by a mutex and are expected to be mutated in
	// serial (ie. by abci responses which are called in serial).
	recheckCursor *clist.CElement // next expected response
	recheckEnd    *clist.CElement // re-checking stops here
	isRechecking  atomic.Bool     // true iff the rechecking process has begun and is not yet finished
	recheckFull   atomic.Bool     // whether rechecking TXs cannot be completed before a new block is decided

	// Map for quick access to txs to record sender in CheckTx.
	// txsMap: txKey -> CElement
	txsMap sync.Map

	// Keep a cache of already-seen txs.
	// This reduces the pressure on the proxyApp.
	cache mempool.TxCache

	logger  log.Logger
	metrics *mempool.Metrics

	pending pendingPool
	removed removedPool
}

var _ mempool.Mempool = &CListMempool{}

// CListMempoolOption sets an optional parameter on the mempool.
type CListMempoolOption func(*CListMempool)

// NewCListMempool returns a new mempool with the given configuration and
// connection to an application.
func NewCListMempool(
	cfg *config.MempoolConfig,
	proxyAppConn proxy.AppConnMempool,
	height int64,
	options ...CListMempoolOption,
) *CListMempool {

	mp := &CListMempool{
		config:        cfg,
		proxyAppConn:  proxyAppConn,
		txs:           clist.New(),
		height:        height,
		recheckCursor: nil,
		recheckEnd:    nil,
		logger:        log.NewNopLogger(),
		metrics:       mempool.NopMetrics(),
	}

	if cfg.CacheSize > 0 {
		mp.cache = mempool.NewLRUTxCache(cfg.CacheSize)
	} else {
		mp.cache = mempool.NopTxCache{}
	}

	proxyAppConn.SetResponseCallback(mp.globalCb)

	for _, option := range options {
		option(mp)
	}

	return mp
}

// NOTE: not thread safe - should only be called once, on startup
func (mem *CListMempool) EnableTxsAvailable() {
	mem.txsAvailable = make(chan struct{}, 1)
}

// SetLogger sets the Logger.
func (mem *CListMempool) SetLogger(l log.Logger) {
	mem.logger = l
}

// WithPreCheck sets a filter for the mempool to reject a tx if f(tx) returns
// false. This is ran before CheckTx. Only applies to the first created block.
// After that, Update overwrites the existing value.
func WithPreCheck(f mempool.PreCheckFunc) CListMempoolOption {
	return func(mem *CListMempool) { mem.preCheck = f }
}

// WithPostCheck sets a filter for the mempool to reject a tx if f(tx) returns
// false. This is ran after CheckTx. Only applies to the first created block.
// After that, Update overwrites the existing value.
func WithPostCheck(f mempool.PostCheckFunc) CListMempoolOption {
	return func(mem *CListMempool) { mem.postCheck = f }
}

// WithMetrics sets the metrics.
func WithMetrics(metrics *mempool.Metrics) CListMempoolOption {
	return func(mem *CListMempool) { mem.metrics = metrics }
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) Lock() {
	// Prepare for Update by setting recheckFull
	rechecking := mem.isRechecking.Load()
	recheckFull := mem.recheckFull.Swap(rechecking)
	if rechecking != recheckFull {
		mem.logger.Debug("the state of recheckFull has flipped")
	}

	mem.updateMtx.Lock()
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) Unlock() {
	mem.updateMtx.Unlock()
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) Size() int {
	return mem.txs.Len() - mem.removed.Size()
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) SizeBytes() int64 {
	return atomic.LoadInt64(&mem.txsBytes) - mem.removed.SizeBytes()
}

// Lock() must be help by the caller during execution.
func (mem *CListMempool) FlushAppConn() error {
	return mem.proxyAppConn.FlushSync()
}

// XXX: Unsafe! Calling Flush may leave mempool in inconsistent state.
func (mem *CListMempool) Flush() {
	mem.updateMtx.RLock()
	defer mem.updateMtx.RUnlock()

	_ = atomic.SwapInt64(&mem.txsBytes, 0)
	mem.cache.Reset()

	for e := mem.txs.Front(); e != nil; e = e.Next() {
		mem.txs.Remove(e)
		e.DetachPrev()
	}

	mem.txsMap.Range(func(key, _ interface{}) bool {
		mem.txsMap.Delete(key)
		return true
	})

	mem.removed.Flush()
	mem.pending.Flush()
}

// TxsFront returns the first transaction in the ordered list for peer
// goroutines to call .NextWait() on.
// FIXME: leaking implementation details!
//
// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) TxsFront() *clist.CElement {
	return mem.txs.Front()
}

// TxsWaitChan returns a channel to wait on transactions. It will be closed
// once the mempool is not empty (ie. the internal `mem.txs` has at least one
// element)
//
// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) TxsWaitChan() <-chan struct{} {
	return mem.txs.WaitChan()
}

// It blocks if we're waiting on Update() or Reap().
// cb: A callback from the CheckTx command.
//
//	It gets called from another goroutine.
//
// CONTRACT: Either cb will get called, or err returned.
//
// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) CheckTx(
	tx types.Tx,
	cb func(*abci.Response),
	txInfo mempool.TxInfo,
) error {

	mem.updateMtx.RLock()
	// use defer to unlock mutex because application (*local client*) might panic
	defer mem.updateMtx.RUnlock()

	txSize := len(tx)

	if txSize > mem.config.MaxTxBytes {
		return mempool.ErrTxTooLarge{
			Max:    mem.config.MaxTxBytes,
			Actual: txSize,
		}
	}

	memSize := mem.Size()
	txsBytes := mem.SizeBytes()
	recheckFull := mem.recheckFull.Load()

	if recheckFull {
		return mempool.ErrMempoolIsFull{
			NumTxs:      memSize,
			MaxTxs:      mem.config.Size,
			TxsBytes:    txsBytes,
			MaxTxsBytes: mem.config.MaxTxsBytes,
		}
	}

	if int64(txSize)+txsBytes > mem.config.MaxTxsBytes {
		return mempool.ErrMempoolIsFull{
			NumTxs:      memSize,
			MaxTxs:      mem.config.Size,
			TxsBytes:    txsBytes,
			MaxTxsBytes: mem.config.MaxTxsBytes,
		}
	}

	// Note: always allow to append new tx
	// if memSize >= mem.config.Size {
	// 	return mempool.ErrMempoolIsFull{
	// 		NumTxs:      memSize,
	// 		MaxTxs:      mem.config.Size,
	// 		TxsBytes:    txsBytes,
	// 		MaxTxsBytes: mem.config.MaxTxsBytes,
	// 	}
	// }

	if mem.preCheck != nil {
		if err := mem.preCheck(tx); err != nil {
			return mempool.ErrPreCheck{
				Reason: err,
			}
		}
	}

	// NOTE: proxyAppConn may error if tx buffer is full
	if err := mem.proxyAppConn.Error(); err != nil {
		return err
	}

	if !mem.cache.Push(tx) { // if the transaction already exists in the cache
		// Record a new sender for a tx we've already seen.
		// Note it's possible a tx is still in the cache but no longer in the mempool
		// (eg. after committing a block, txs are removed from mempool but not cache),
		// so we only record the sender for txs still in the mempool.
		if e, ok := mem.txsMap.Load(tx.Key()); ok {
			memTx := e.(*clist.CElement).Value.(*mempoolTx)
			memTx.senders.LoadOrStore(txInfo.SenderID, true)
			// TODO: consider punishing peer for dups,
			// its non-trivial since invalid txs can become valid,
			// but they can spam the same tx with little cost to them atm.
		}
		return mempool.ErrTxInCache
	}

	reqRes := mem.proxyAppConn.CheckTxAsync(abci.RequestCheckTx{Tx: tx}) // NOTE: app mempool insert
	// Note: execute 'mem.reqResCb(tx, txInfo.SenderID, txInfo.SenderP2PID, cb)' immediately
	// mem.logger.Info("Debug>> mempool status: CheckTx", "txSize", memSize, "txBytes", txsBytes, "gid", getGoroutineID())
	reqRes.SetCallback(mem.reqResCb(tx, txInfo.SenderID, txInfo.SenderP2PID, cb))

	return nil
}

// Global callback that will be called after every ABCI response.
// Having a single global callback avoids needing to set a callback for each request.
// However, processing the checkTx response requires the peerID (so we can track which txs we heard from who),
// and peerID is not included in the ABCI request, so we have to set request-specific callbacks that
// include this information. If we're not in the midst of a recheck, this function will just return,
// so the request specific callback can do the work.
//
// When rechecking, we don't need the peerID, so the recheck callback happens
// here.
func (mem *CListMempool) globalCb(req *abci.Request, res *abci.Response) {
	if mem.recheckCursor == nil {
		return
	}

	mem.metrics.RecheckTimes.Add(1)
	mem.resCbRecheck(req, res)

	// update metrics
	mem.metrics.Size.Set(float64(mem.Size()))
}

// Request specific callback that should be set on individual reqRes objects
// to incorporate local information when processing the response.
// This allows us to track the peer that sent us this tx, so we can avoid sending it back to them.
// NOTE: alternatively, we could include this information in the ABCI request itself.
//
// External callers of CheckTx, like the RPC, can also pass an externalCb through here that is called
// when all other response processing is complete.
//
// Used in CheckTx to record PeerID who sent us the tx.
func (mem *CListMempool) reqResCb(
	tx []byte,
	peerID uint16,
	peerP2PID p2p.ID,
	externalCb func(*abci.Response),
) func(res *abci.Response) {
	return func(res *abci.Response) {
		if mem.recheckCursor != nil {
			// this should never happen
			panic("recheck cursor is not nil in reqResCb")
		}

		mem.resCbFirstTime(tx, peerID, peerP2PID, res) // Note: mempool insert

		// update metrics
		mem.metrics.Size.Set(float64(mem.Size()))
		mem.metrics.SizeBytes.Set(float64(mem.SizeBytes()))

		// passed in by the caller of CheckTx, eg. the RPC
		if externalCb != nil {
			externalCb(res)
		}
	}
}

// Called from:
//   - resCbFirstTime (lock not held) if tx is valid
func (mem *CListMempool) addTx(memTx *mempoolTx) {
	e := mem.txs.PushBack(memTx)
	mem.txsMap.Store(memTx.tx.Key(), e)
	atomic.AddInt64(&mem.txsBytes, int64(len(memTx.tx)))
	mem.metrics.TxSizeBytes.Observe(float64(len(memTx.tx)))

	mem.pending.Add(memTx)
}

// Called from:
//   - Update (lock held) if tx was committed
//   - resCbRecheck (lock not held) if tx was invalidated
func (mem *CListMempool) removeTx(tx types.Tx, elem *clist.CElement, removeFromCache bool) {
	removed := mem.txs.Remove(elem)
	memTx := removed.(*mempoolTx)

	elem.DetachPrev()
	mem.txsMap.Delete(tx.Key())
	atomic.AddInt64(&mem.txsBytes, int64(-len(tx)))

	if removeFromCache {
		mem.cache.Remove(tx)
	}

	mem.pending.Remove(memTx)
}

// RemoveTxByKey removes a transaction from the mempool by its TxKey index.
func (mem *CListMempool) RemoveTxByKey(txKey types.TxKey) error {
	if e, ok := mem.txsMap.Load(txKey); ok {
		memTx := e.(*clist.CElement).Value.(*mempoolTx)
		if memTx != nil {
			mem.removeTx(memTx.tx, e.(*clist.CElement), false)
			return nil
		}
		return errors.New("transaction not found")
	}
	return errors.New("invalid transaction found")
}

func (mem *CListMempool) isFull(txSize int) error {
	memSize := mem.Size()
	txsBytes := mem.SizeBytes()
	recheckFull := mem.recheckFull.Load()

	if memSize >= mem.config.Size || int64(txSize)+txsBytes > mem.config.MaxTxsBytes || recheckFull {
		return mempool.ErrMempoolIsFull{
			NumTxs:      memSize,
			MaxTxs:      mem.config.Size,
			TxsBytes:    txsBytes,
			MaxTxsBytes: mem.config.MaxTxsBytes,
		}
	}

	return nil
}

// callback, which is called after the app checked the tx for the first time.
//
// The case where the app checks the tx for the second and subsequent times is
// handled by the resCbRecheck callback.
func (mem *CListMempool) resCbFirstTime(
	tx []byte,
	peerID uint16,
	peerP2PID p2p.ID,
	res *abci.Response,
) {
	// mem.logger.Info("Debug>> mempool status: resCbFirstTime", "txSize", mem.Size(), "txBytes", mem.SizeBytes(), "gid", getGoroutineID())
	switch r := res.Value.(type) {
	case *abci.Response_CheckTx:
		var postCheckErr error
		if mem.postCheck != nil {
			postCheckErr = mem.postCheck(tx, r.CheckTx)
		}
		if (r.CheckTx.Code == abci.CodeTypeOK) && postCheckErr == nil {
			// Check mempool isn't full again to reduce the chance of exceeding the
			// limits.
			memSize := mem.Size()
			txsBytes := mem.SizeBytes()
			recheckFull := mem.recheckFull.Load()

			if recheckFull {
				// remove from cache (mempool might have a space later)
				mem.cache.Remove(tx)
				mem.logger.Error(mempool.ErrMempoolIsFull{
					NumTxs:      memSize,
					MaxTxs:      mem.config.Size,
					TxsBytes:    txsBytes,
					MaxTxsBytes: mem.config.MaxTxsBytes,
				}.Error())
				return
			}

			if int64(len(tx))+txsBytes > mem.config.MaxTxsBytes {
				// remove from cache (mempool might have a space later)
				mem.cache.Remove(tx)
				mem.logger.Error(mempool.ErrMempoolIsFull{
					NumTxs:      memSize,
					MaxTxs:      mem.config.Size,
					TxsBytes:    txsBytes,
					MaxTxsBytes: mem.config.MaxTxsBytes,
				}.Error())
				return
			}

			// Check transaction not already in the mempool
			if e, ok := mem.txsMap.Load(types.Tx(tx).Key()); ok {
				memTx := e.(*clist.CElement).Value.(*mempoolTx)
				memTx.senders.LoadOrStore(peerID, true)
				mem.logger.Debug(
					"transaction already there, not adding it again",
					"tx", types.Tx(tx).Hash(),
					"res", r,
					"height", mem.height,
					"total", mem.Size(),
				)
				return
			}

			// make new mempoolTx
			memTx := &mempoolTx{
				height:    mem.height,
				gasWanted: r.CheckTx.GasWanted,
				tx:        tx,

				signerAddress: r.CheckTx.SignerAddress,
				nonce:         r.CheckTx.Nonce,
				gasPrice:      r.CheckTx.GasPrice,
				gasLimit:      r.CheckTx.GasLimit,
				txType:        r.CheckTx.Type,
			}
			memTx.senders.Store(peerID, true)

			if err := mem.tryToAppnedTx(memTx); err == nil {
				mem.logger.Debug(
					"added good transaction",
					"tx", types.Tx(tx).Hash(),
					"res", r,
					"height", memTx.height,
					"total", mem.Size(),
				)

				mem.notifyTxsAvailable()
			} else {
				mem.logger.Error(err.Error())
			}
		} else {
			// ignore bad transaction
			mem.logger.Debug(
				"rejected bad transaction",
				"tx", types.Tx(tx).Hash(),
				"peerID", peerP2PID,
				"res", r,
				"err", postCheckErr,
			)
			mem.metrics.FailedTxs.Add(1)

			if !mem.config.KeepInvalidTxsInCache {
				// remove from cache (it might be good later)
				mem.cache.Remove(tx)
			}
		}

	default:
		// ignore other messages
	}
}

func (mem *CListMempool) tryToAppnedTx(memTx *mempoolTx) error {
	mem.pending.CleanUp(memTx.signerAddress)
	// lastNonce, err := mem.pending.GetLastNonce(memTx.signerAddress)
	// if err != nil {
	// 	mem.logger.Error("failed to get last nonce", "err", err.Error())
	// 	return err
	// }

	// if lastNonce > 0 {
	// 	if memTx.nonce != lastNonce+1 {
	// 		return fmt.Errorf("invalid nonce; got %d, expected %d", memTx.nonce, lastNonce+1)
	// 	}
	// }

	mem.addTx(memTx)

	// find and drop, if mempool is full
	if mem.Size() > mem.config.Size {
		mem.markRemovableTxs()
	}

	if memTx.removed {
		// new add memTx marked as removed, it means add failed, return error with reason "mempool is full"
		// remove from cache (mempool might have a space later)
		if e, ok := mem.txsMap.Load(memTx.tx.Key()); ok {
			mem.removeTx(memTx.tx, e.(*clist.CElement), true)
		}
		return fmt.Errorf("gas price is too low")
	}

	return nil
}

// callback, which is called after the app rechecked the tx.
//
// The case where the app checks the tx for the first time is handled by the
// resCbFirstTime callback.
func (mem *CListMempool) resCbRecheck(req *abci.Request, res *abci.Response) {
	switch r := res.Value.(type) {
	case *abci.Response_CheckTx:
		tx := req.GetCheckTx().Tx
		memTx := mem.recheckCursor.Value.(*mempoolTx)

		// Search through the remaining list of tx to recheck for a transaction that matches
		// the one we received from the ABCI application.
		for {
			if bytes.Equal(tx, memTx.tx) {
				// We've found a tx in the recheck list that matches the tx that we
				// received from the ABCI application.
				// Break, and use this transaction for further checks.
				break
			}

			mem.logger.Error(
				"re-CheckTx transaction mismatch",
				"got", types.Tx(tx),
				"expected", memTx.tx,
			)

			if mem.recheckCursor == mem.recheckEnd {
				// we reached the end of the recheckTx list without finding a tx
				// matching the one we received from the ABCI application.
				// Return without processing any tx.
				mem.recheckCursor = nil
				mem.isRechecking.Store(false)
				mem.recheckFull.Store(false)
				return
			}

			mem.recheckCursor = mem.recheckCursor.Next()
			memTx = mem.recheckCursor.Value.(*mempoolTx)
		}

		var postCheckErr error
		if mem.postCheck != nil {
			postCheckErr = mem.postCheck(tx, r.CheckTx)
		}

		if (r.CheckTx.Code == abci.CodeTypeOK) && postCheckErr == nil {
			// Good, nothing to do.
		} else {
			// Tx became invalidated due to newly committed block.
			mem.logger.Debug("tx is no longer valid", "tx", types.Tx(tx).Hash(), "res", r, "err", postCheckErr)
			// NOTE: we remove tx from the cache because it might be good later
			mem.removeTx(tx, mem.recheckCursor, !mem.config.KeepInvalidTxsInCache)
		}
		if mem.recheckCursor == mem.recheckEnd {
			mem.recheckCursor = nil
			mem.isRechecking.Store(false)
			mem.recheckFull.Store(false)
		} else {
			mem.recheckCursor = mem.recheckCursor.Next()
		}
		if mem.recheckCursor == nil {
			// Done!
			mem.logger.Debug("done rechecking txs")

			// incase the recheck removed all txs
			if mem.Size() > 0 {
				mem.notifyTxsAvailable()
			}
		}
	default:
		// ignore other messages
	}
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) TxsAvailable() <-chan struct{} {
	return mem.txsAvailable
}

func (mem *CListMempool) notifyTxsAvailable() {
	if mem.Size() == 0 {
		panic("notified txs available but mempool is empty!")
	}
	if mem.txsAvailable != nil && !mem.notifiedTxsAvailable {
		// channel cap is 1, so this will send once
		mem.notifiedTxsAvailable = true
		select {
		case mem.txsAvailable <- struct{}{}:
		default:
		}
	}
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) ReapMaxBytesMaxGas(maxBytes, maxGas int64) types.Txs {
	mem.updateMtx.RLock()
	defer mem.updateMtx.RUnlock()

	var (
		totalGas    int64
		runningSize int64
	)

	// TODO: we will get a performance boost if we have a good estimate of avg
	// size per tx, and set the initial capacity based off of that.
	// txs := make([]types.Tx, 0, cmtmath.MinInt(mem.txs.Len(), max/mem.avgTxSize))
	txs := make([]types.Tx, 0, mem.txs.Len())
	for e := mem.txs.Front(); e != nil; e = e.Next() {
		memTx := e.Value.(*mempoolTx)

		// skip removed tx
		if memTx.removed {
			continue
		}

		txs = append(txs, memTx.tx)

		dataSize := types.ComputeProtoSizeForTxs([]types.Tx{memTx.tx})

		// Check total size requirement
		if maxBytes > -1 && runningSize+dataSize > maxBytes {
			return txs[:len(txs)-1]
		}

		runningSize += dataSize

		// Check total gas requirement.
		// If maxGas is negative, skip this check.
		// Since newTotalGas < masGas, which
		// must be non-negative, it follows that this won't overflow.
		newTotalGas := totalGas + memTx.gasWanted
		if maxGas > -1 && newTotalGas > maxGas {
			return txs[:len(txs)-1]
		}
		totalGas = newTotalGas
	}
	return txs
}

// Safe for concurrent use by multiple goroutines.
func (mem *CListMempool) ReapMaxTxs(max int) types.Txs {
	mem.updateMtx.RLock()
	defer mem.updateMtx.RUnlock()

	if max < 0 {
		max = mem.txs.Len()
	}

	txs := make([]types.Tx, 0, cmtmath.MinInt(mem.txs.Len(), max))
	for e := mem.txs.Front(); e != nil && len(txs) <= max; e = e.Next() {
		memTx := e.Value.(*mempoolTx)
		// skip removed tx
		if memTx.removed {
			continue
		}
		txs = append(txs, memTx.tx)
	}
	return txs
}

// Lock() must be help by the caller during execution.
func (mem *CListMempool) Update(
	height int64,
	txs types.Txs,
	deliverTxResponses []*abci.ResponseDeliverTx,
	preCheck mempool.PreCheckFunc,
	postCheck mempool.PostCheckFunc,
) error {
	// Set height
	mem.height = height
	mem.notifiedTxsAvailable = false

	if preCheck != nil {
		mem.preCheck = preCheck
	}
	if postCheck != nil {
		mem.postCheck = postCheck
	}

	for i, tx := range txs {
		if deliverTxResponses[i].Code == abci.CodeTypeOK {
			// Add valid committed tx to the cache (if missing).
			_ = mem.cache.Push(tx)
		} else if !mem.config.KeepInvalidTxsInCache {
			// Allow invalid transactions to be resubmitted.
			mem.cache.Remove(tx)
		}

		// Remove committed tx from the mempool.
		//
		// Note an evil proposer can drop valid txs!
		// Mempool before:
		//   100 -> 101 -> 102
		// Block, proposed by an evil proposer:
		//   101 -> 102
		// Mempool after:
		//   100
		// https://github.com/tendermint/tendermint/issues/3322.
		if e, ok := mem.txsMap.Load(tx.Key()); ok {
			mem.removeTx(tx, e.(*clist.CElement), false)
		}
	}

	// clean txs marked as removed
	if mem.removed.Size() > 0 {
		mem.cleanUpMarkedRemovedTxs()
	}

	// Either recheck non-committed txs to see if they became invalid
	// or just notify there're some txs left.
	if mem.Size() > 0 {
		if mem.config.Recheck {
			mem.logger.Debug("recheck txs", "numtxs", mem.Size(), "height", height)
			mem.recheckTxs()
			// At this point, mem.txs are being rechecked.
			// mem.recheckCursor re-scans mem.txs and possibly removes some txs.
			// Before mem.Reap(), we should wait for mem.recheckCursor to be nil.
		} else {
			mem.notifyTxsAvailable()
		}
	}

	// Update metrics
	mem.metrics.Size.Set(float64(mem.Size()))
	mem.metrics.SizeBytes.Set(float64(mem.SizeBytes()))

	mem.logger.Info("=====================================================================================================")
	return nil
}

func (mem *CListMempool) recheckTxs() {
	if mem.Size() == 0 {
		panic("recheckTxs is called, but the mempool is empty")
	}

	mem.recheckCursor = mem.txs.Front()
	mem.recheckEnd = mem.txs.Back()
	mem.isRechecking.Store(true)

	// Push txs to proxyAppConn
	// NOTE: globalCb may be called concurrently.
	for e := mem.txs.Front(); e != nil; e = e.Next() {
		memTx := e.Value.(*mempoolTx)

		// skip removed tx
		if memTx.removed {
			continue
		}

		mem.proxyAppConn.CheckTxAsync(abci.RequestCheckTx{
			Tx:   memTx.tx,
			Type: abci.CheckTxType_Recheck,
		})
	}

	mem.proxyAppConn.FlushAsync()
}

func (mem *CListMempool) cleanUpMarkedRemovedTxs() {
	mem.removed.lock.Lock()
	defer mem.removed.lock.Unlock()
	for i := range mem.removed.data {
		memTx := mem.removed.data[i]

		if e, ok := mem.txsMap.Load(memTx.tx.Key()); ok {
			elem := e.(*clist.CElement)
			mem.txs.Remove(elem)
			elem.DetachPrev()
			mem.txsMap.Delete(memTx.tx.Key())
			atomic.AddInt64(&mem.txsBytes, int64(-len(memTx.tx)))
		}
	}

	for i := range mem.removed.data {
		mem.pending.CleanUp(mem.removed.data[i].signerAddress)
	}

	mem.removed.data = nil
}

func (mem *CListMempool) markRemovableTxs() {
	mem.logger.Info(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", "gid", getGoroutineID(), "pendingSize", mem.pending.Size(), "removedSize", mem.removed.Size())
	mem.pending.lock.RLock()
	defer mem.pending.lock.RUnlock()
	totalPendingTxCnt := 0
	// Simulate the execution order based on reference nonce and gas price
	cursorGrp := make(map[string]int, len(mem.pending.data))
	for key := range mem.pending.data {
		cursorGrp[key] = 0
		totalPendingTxCnt += len(mem.pending.data[key])
	}
	totalPendingTxCnt -= mem.removed.Size()
	cnt := 0
	for cnt < totalPendingTxCnt {
		var highestGasPrice uint64
		var selectedMemTx *mempoolTx

		for sender, txs := range mem.pending.data {
			if cursor, exists := cursorGrp[sender]; exists {
				if cursor < len(txs) {
					thisTx := txs[cursor]
					if !thisTx.removed {
						if thisTx.txType == 0 {
							highestGasPrice = math.MaxUint64
							selectedMemTx = thisTx
						} else {
							if highestGasPrice == 0 || thisTx.gasPrice > highestGasPrice {
								highestGasPrice = thisTx.gasPrice
								selectedMemTx = thisTx
							}
						}
					} else {

					}
				}
			}
		}

		if selectedMemTx == nil {
			break
		}
		mem.logger.Info("tx selected", "sender", selectedMemTx.signerAddress, "nonce", selectedMemTx.nonce, "gid", getGoroutineID())

		if cnt >= mem.config.Size {
			txs := mem.pending.data[selectedMemTx.signerAddress]
			for i := cursorGrp[selectedMemTx.signerAddress]; i < len(txs); i++ {
				if !txs[i].removed {
					mem.removed.Add(txs[i])
					mem.logger.Info("tx marked removed", "sender", txs[i].signerAddress, "nonce", txs[i].nonce, "gid", getGoroutineID())
				}
				cursorGrp[selectedMemTx.signerAddress]++
				cnt++
			}
		} else {
			cursorGrp[selectedMemTx.signerAddress]++
			cnt++
		}
	}
	mem.logger.Info("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<", "gid", getGoroutineID(), "pendingSize", mem.pending.Size(), "removedSize", mem.removed.Size())
}

//--------------------------------------------------------------------------------

// mempoolTx is a transaction that successfully ran
type mempoolTx struct {
	height    int64    // height that this tx had been validated in
	gasWanted int64    // amount of gas this tx states it will require
	tx        types.Tx //

	// ids of peers who've sent us this tx (as a map for quick lookups).
	// senders: PeerID -> bool
	senders sync.Map

	// additonal data of tx
	signerAddress string
	nonce         uint64
	txType        int32
	gasPrice      uint64
	gasLimit      uint64

	removed bool
}

// Height returns the height for this transaction
func (memTx *mempoolTx) Height() int64 {
	return atomic.LoadInt64(&memTx.height)
}

// --------------------------------------------------------------------------------
type removedPool struct {
	lock sync.RWMutex
	data []*mempoolTx
}

// Safe for concurrent use by multiple goroutines.
func (rp *removedPool) Size() int {
	rp.lock.RLock()
	defer rp.lock.RUnlock()

	return len(rp.data)
}

// Safe for concurrent use by multiple goroutines.
func (rp *removedPool) SizeBytes() int64 {
	rp.lock.RLock()
	defer rp.lock.RUnlock()

	var size int64
	for _, tx := range rp.data {
		size += int64(len(tx.tx))
	}

	return size
}

func (rp *removedPool) Add(tx *mempoolTx) {
	rp.lock.Lock()
	defer rp.lock.Unlock()

	if !tx.removed {
		tx.removed = true
		if rp.data == nil {
			rp.data = make([]*mempoolTx, 0, pendingQueuePreallocationSize)
		}
		rp.data = append(rp.data, tx)
	}
}

func (rp *removedPool) Flush() {
	rp.lock.Lock()
	defer rp.lock.Unlock()
	rp.data = nil
}

// --------------------------------------------------------------------------------
type pendingPool struct {
	lock sync.RWMutex
	data map[string][]*mempoolTx
}

// Safe for concurrent use by multiple goroutines.
func (pp *pendingPool) Size() int {
	pp.lock.RLock()
	defer pp.lock.RUnlock()

	size := 0

	for _, txs := range pp.data {
		size += len(txs)
	}

	return size
}

func (pp *pendingPool) Add(tx *mempoolTx) {
	pp.lock.Lock()
	defer pp.lock.Unlock()

	if pp.data == nil {
		pp.data = make(map[string][]*mempoolTx)
	}

	sender := tx.signerAddress
	if _, exists := pp.data[sender]; !exists {
		pp.data[sender] = make([]*mempoolTx, 0, pendingQueuePreallocationSize)
	}
	pp.data[sender] = append(pp.data[sender], tx)

	if len(pp.data[sender]) > 1 {
		sort.Slice(pp.data[sender], func(i, j int) bool {
			return pp.data[sender][i].nonce < pp.data[sender][j].nonce
		})
	}
}

func (pp *pendingPool) Remove(tx *mempoolTx) {
	pp.lock.Lock()
	defer pp.lock.Unlock()

	sender := tx.signerAddress
	if _, exists := pp.data[sender]; exists {
		for i := range pp.data[sender] {
			if pp.data[sender][i] == tx {
				pp.data[sender] = append(pp.data[sender][:i], pp.data[sender][i+1:]...)
				break
			}
		}
	}
}

func (pp *pendingPool) CleanUp(sender string) {
	pp.lock.Lock()
	defer pp.lock.Unlock()

	if _, exists := pp.data[sender]; exists {
		txs := pp.data[sender]
		newTxs := make([]*mempoolTx, 0, len(txs))
		for i := range txs {
			if !txs[i].removed {
				newTxs = append(newTxs, txs[i])
			}
		}
		if len(newTxs) == 0 {
			delete(pp.data, sender)
		} else {
			pp.data[sender] = newTxs
		}
	}
}

// func (pp *pendingPool) GetLastNonce(sender string) (uint64, error) {
// 	pp.lock.RLock()
// 	defer pp.lock.RUnlock()

// 	if _, exists := pp.data[sender]; exists {
// 		if len(pp.data[sender]) > 0 {
// 			for i := len(pp.data[sender]) - 1; i >= 0; i-- {
// 				if !pp.data[sender][i].removed {
// 					return pp.data[sender][i].nonce, nil
// 				}
// 			}
// 			return 0, errors.New("invalid nonce")
// 		}
// 	}
// 	return 0, nil
// }

func (pp *pendingPool) Flush() {
	pp.lock.Lock()
	defer pp.lock.Unlock()
	pp.data = nil
}

func getGoroutineID() int {
	var buf [64]byte
	n := runtime.Stack(buf[:], false)
	stack := string(buf[:n])

	idField := strings.Fields(strings.TrimPrefix(stack, "goroutine "))[0]
	id, _ := strconv.Atoi(idField)
	return id
}
