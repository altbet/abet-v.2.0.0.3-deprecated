// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin developers
// Copyright (c) 2012-2013 The PPCoin developers
// Copyright (c) 2014-2015 The Dash developers
// Copyright (c) 2015-2017 The PIVX developers
// Copyright (c) 2017-2019 The Altbet Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "main.h"
#include "accumulators.h"
#include "addrman.h"
#include "alert.h"
#include "base58.h"
#include "chainparams.h"
#include "checkpoints.h"
#include "checkqueue.h"
#include "consensus/merkle.h"
#include "consensus/validation.h"
#include "init.h"
#include "kernel.h"
#include "masternode-budget.h"
#include "masternode-payments.h"
#include "masternodeman.h"
#include "merkleblock.h"
#include "net.h"
#include "obfuscation.h"
#include "pow.h"
#include "protocol.h"
#include "spork.h"
#include "sporkdb.h"
#include "swifttx.h"
#include "txdb.h"
#include "txmempool.h"
#include "ui_interface.h"
#include "util.h"
#include "utilmoneystr.h"
#include "validationinterface.h"

#include "accumulatormap.h"
#include "libzerocoin/Denominations.h"
#include "primitives/zerocoin.h"

#include <sstream>

#include <boost/algorithm/string/replace.hpp>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/thread.hpp>

using namespace boost;
using namespace std;
using namespace libzerocoin;

#if defined(NDEBUG)
#error "Altbet cannot be compiled without assertions."
#endif

// 6 comes from OPCODE (1) + vch.size() (1) + BIGNUM size (4)
#define SCRIPT_OFFSET 6
// For Script size (BIGNUM/Uint256 size)
#define BIGNUM_SIZE 4
/**
 * Global state
 */

CCriticalSection cs_main;

BlockMap mapBlockIndex;
map<uint256, uint256> mapProofOfStake;
set<pair<COutPoint, unsigned int> > setStakeSeen;

// maps any spent outputs in the past maxreorgdepth blocks to the height it was spent
// this means for incoming blocks, we can check that their stake output was not spent before
// the incoming block tried to use it as a staking input. We can also prevent block spam
// attacks because then we can check that either the staking input is available in the current
// active chain, or the staking input was spent in the past 100 blocks after the height
// of the incoming block.
map<COutPoint, int> mapStakeSpent;
map<unsigned int, unsigned int> mapHashedBlocks;
CChain chainActive;
CBlockIndex* pindexBestHeader = NULL;
int64_t nTimeBestReceived = 0;
CWaitableCriticalSection csBestBlock;
CConditionVariable cvBlockChange;
int nScriptCheckThreads = 0;
bool fImporting = false;
bool fReindex = false;
bool fTxIndex = true;
bool fAddrIndex = true;
bool fIsBareMultisigStd = true;
bool fCheckBlockIndex = false;
bool fVerifyingBlocks = false;
unsigned int nCoinCacheSize = 5000;
unsigned int nBytesPerSigOp = DEFAULT_BYTES_PER_SIGOP;
bool fAlerts = DEFAULT_ALERTS;

unsigned int nStakeMinAge = 1 * 60 * 60;
unsigned int StakeMinAgev2()
{
    if (chainActive.Height() > 192021)
        return 3 * 60 * 60;
    return nStakeMinAge;
}

int64_t nReserveBalance = 0;

/** Fees smaller than this (in uabet) are considered zero fee (for relaying and mining)
 * We are ~100 times smaller then bitcoin now (2015-06-23), set minRelayTxFee only 10 times higher
 * so it's still 10 times lower comparing to bitcoin.
 */
CFeeRate minRelayTxFee = CFeeRate(10000);

CTxMemPool mempool(::minRelayTxFee);

struct COrphanTx {
    CTransaction tx;
    NodeId fromPeer;
};
map<uint256, COrphanTx> mapOrphanTransactions;
map<uint256, set<uint256> > mapOrphanTransactionsByPrev;
map<uint256, int64_t> mapRejectedBlocks;
map<uint256, int64_t> mapZerocoinspends; //txid, time received


void EraseOrphansFor(NodeId peer);

static void CheckBlockIndex();

/** Constant stuff for coinbase transactions we create: */
CScript COINBASE_FLAGS;

const string strMessageMagic = "DarkNet Signed Message:\n";

// Internal stuff
namespace
{
struct CBlockIndexWorkComparator {
    bool operator()(CBlockIndex* pa, CBlockIndex* pb) const
    {
        // First sort by most total work, ...
        if (pa->nChainWork > pb->nChainWork) return false;
        if (pa->nChainWork < pb->nChainWork) return true;

        // ... then by earliest time received, ...
        if (pa->nSequenceId < pb->nSequenceId) return false;
        if (pa->nSequenceId > pb->nSequenceId) return true;

        // Use pointer address as tie breaker (should only happen with blocks
        // loaded from disk, as those all have id 0).
        if (pa < pb) return false;
        if (pa > pb) return true;

        // Identical blocks.
        return false;
    }
};

CBlockIndex* pindexBestInvalid;

/**
     * The set of all CBlockIndex entries with BLOCK_VALID_TRANSACTIONS (for itself and all ancestors) and
     * as good as our current tip or better. Entries may be failed, though.
     */
set<CBlockIndex*, CBlockIndexWorkComparator> setBlockIndexCandidates;
/** Number of nodes with fSyncStarted. */
int nSyncStarted = 0;
/** All pairs A->B, where A (or one if its ancestors) misses transactions, but B has transactions. */
multimap<CBlockIndex*, CBlockIndex*> mapBlocksUnlinked;

CCriticalSection cs_LastBlockFile;
std::vector<CBlockFileInfo> vinfoBlockFile;
int nLastBlockFile = 0;

/**
     * Every received block is assigned a unique and increasing identifier, so we
     * know which one to give priority in case of a fork.
     */
CCriticalSection cs_nBlockSequenceId;
/** Blocks loaded from disk are assigned id 0, so start the counter at 1. */
uint32_t nBlockSequenceId = 1;

/**
     * Sources of received blocks, to be able to send them reject messages or ban
     * them, if processing happens afterwards. Protected by cs_main.
     */
map<uint256, NodeId> mapBlockSource;

/** Blocks that are in flight, and that are in the queue to be downloaded. Protected by cs_main. */
struct QueuedBlock {
    uint256 hash;
    CBlockIndex* pindex;        //! Optional.
    int64_t nTime;              //! Time of "getdata" request in microseconds.
    int nValidatedQueuedBefore; //! Number of blocks queued with validated headers (globally) at the time this one is requested.
    bool fValidatedHeaders;     //! Whether this block has validated headers at the time of request.
};
map<uint256, pair<NodeId, list<QueuedBlock>::iterator> > mapBlocksInFlight;

/** Number of blocks in flight with validated headers. */
int nQueuedValidatedHeaders = 0;

/** Number of preferable block download peers. */
int nPreferredDownload = 0;

/** Dirty block index entries. */
set<CBlockIndex*> setDirtyBlockIndex;

/** Dirty block file entries. */
set<int> setDirtyFileInfo;
} // namespace

//////////////////////////////////////////////////////////////////////////////
//
// Registration of network node signals.
//

namespace
{
struct CBlockReject {
    unsigned int chRejectCode;
    string strRejectReason;
    uint256 hashBlock;
};

/**
 * Maintain validation-specific state about nodes, protected by cs_main, instead
 * by CNode's own locks. This simplifies asynchronous operation, where
 * processing of incoming data is done after the ProcessMessage call returns,
 * and we're no longer holding the node's locks.
 */
struct CNodeState {
    //! The peer's address
    CService address;
    //! Whether we have a fully established connection.
    bool fCurrentlyConnected;
    //! Accumulated misbehaviour score for this peer.
    int nMisbehavior;
    //! Whether this peer should be disconnected and banned (unless whitelisted).
    bool fShouldBan;
    //! String name of this peer (debugging/logging purposes).
    std::string name;
    //! List of asynchronously-determined block rejections to notify this peer about.
    std::vector<CBlockReject> rejects;
    //! The best known block we know this peer has announced.
    CBlockIndex* pindexBestKnownBlock;
    //! The hash of the last unknown block this peer has announced.
    uint256 hashLastUnknownBlock;
    //! The last full block we both have.
    CBlockIndex* pindexLastCommonBlock;
    //! Whether we've started headers synchronization with this peer.
    bool fSyncStarted;
    //! Since when we're stalling block download progress (in microseconds), or 0.
    int64_t nStallingSince;
    list<QueuedBlock> vBlocksInFlight;
    int nBlocksInFlight;
    //! Whether we consider this a preferred download peer.
    bool fPreferredDownload;
    //! Whether this peer can give us witnesses
    bool fHaveWitness;

    CNodeState()
    {
        fCurrentlyConnected = false;
        nMisbehavior = 0;
        fShouldBan = false;
        pindexBestKnownBlock = NULL;
        hashLastUnknownBlock = uint256(0);
        pindexLastCommonBlock = NULL;
        fSyncStarted = false;
        nStallingSince = 0;
        nBlocksInFlight = 0;
        fPreferredDownload = false;
        fHaveWitness = false;
    }
};

/** Map maintaining per-node state. Requires cs_main. */
map<NodeId, CNodeState> mapNodeState;

// Requires cs_main.
CNodeState* State(NodeId pnode)
{
    map<NodeId, CNodeState>::iterator it = mapNodeState.find(pnode);
    if (it == mapNodeState.end())
        return NULL;
    return &it->second;
}

int GetHeight()
{
    while (true) {
        TRY_LOCK(cs_main, lockMain);
        if (!lockMain) {
            MilliSleep(50);
            continue;
        }
        return chainActive.Height();
    }
}

void UpdatePreferredDownload(CNode* node, CNodeState* state)
{
    nPreferredDownload -= state->fPreferredDownload;

    // Whether this node should be marked as a preferred download node.
    state->fPreferredDownload = (!node->fInbound || node->fWhitelisted) && !node->fOneShot && !node->fClient;

    nPreferredDownload += state->fPreferredDownload;
}

void InitializeNode(NodeId nodeid, const CNode* pnode)
{
    LOCK(cs_main);
    CNodeState& state = mapNodeState.insert(std::make_pair(nodeid, CNodeState())).first->second;
    state.name = pnode->addrName;
    state.address = pnode->addr;
}

void FinalizeNode(NodeId nodeid)
{
    LOCK(cs_main);
    CNodeState* state = State(nodeid);

    if (state->fSyncStarted)
        nSyncStarted--;

    if (state->nMisbehavior == 0 && state->fCurrentlyConnected) {
        AddressCurrentlyConnected(state->address);
    }

    BOOST_FOREACH (const QueuedBlock& entry, state->vBlocksInFlight)
        mapBlocksInFlight.erase(entry.hash);
    EraseOrphansFor(nodeid);
    nPreferredDownload -= state->fPreferredDownload;

    mapNodeState.erase(nodeid);
}

// Requires cs_main.
void MarkBlockAsReceived(const uint256& hash)
{
    map<uint256, pair<NodeId, list<QueuedBlock>::iterator> >::iterator itInFlight = mapBlocksInFlight.find(hash);
    if (itInFlight != mapBlocksInFlight.end()) {
        CNodeState* state = State(itInFlight->second.first);
        nQueuedValidatedHeaders -= itInFlight->second.second->fValidatedHeaders;
        state->vBlocksInFlight.erase(itInFlight->second.second);
        state->nBlocksInFlight--;
        state->nStallingSince = 0;
        mapBlocksInFlight.erase(itInFlight);
    }
}

// Requires cs_main.
void MarkBlockAsInFlight(NodeId nodeid, const uint256& hash, CBlockIndex* pindex = NULL)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    // Make sure it's not listed somewhere already.
    MarkBlockAsReceived(hash);

    QueuedBlock newentry = {hash, pindex, GetTimeMicros(), nQueuedValidatedHeaders, pindex != NULL};
    nQueuedValidatedHeaders += newentry.fValidatedHeaders;
    list<QueuedBlock>::iterator it = state->vBlocksInFlight.insert(state->vBlocksInFlight.end(), newentry);
    state->nBlocksInFlight++;
    mapBlocksInFlight[hash] = std::make_pair(nodeid, it);
}

/** Check whether the last unknown block a peer advertized is not yet known. */
void ProcessBlockAvailability(NodeId nodeid)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    if (state->hashLastUnknownBlock != 0) {
        BlockMap::iterator itOld = mapBlockIndex.find(state->hashLastUnknownBlock);
        if (itOld != mapBlockIndex.end() && itOld->second->nChainWork > 0) {
            if (state->pindexBestKnownBlock == NULL || itOld->second->nChainWork >= state->pindexBestKnownBlock->nChainWork)
                state->pindexBestKnownBlock = itOld->second;
            state->hashLastUnknownBlock = uint256(0);
        }
    }
}

/** Update tracking information about which blocks a peer is assumed to have. */
void UpdateBlockAvailability(NodeId nodeid, const uint256& hash)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    ProcessBlockAvailability(nodeid);

    BlockMap::iterator it = mapBlockIndex.find(hash);
    if (it != mapBlockIndex.end() && it->second->nChainWork > 0) {
        // An actually better block was announced.
        if (state->pindexBestKnownBlock == NULL || it->second->nChainWork >= state->pindexBestKnownBlock->nChainWork)
            state->pindexBestKnownBlock = it->second;
    } else {
        // An unknown block was announced; just assume that the latest one is the best one.
        state->hashLastUnknownBlock = hash;
    }
}

/** Find the last common ancestor two blocks have.
 *  Both pa and pb must be non-NULL. */
CBlockIndex* LastCommonAncestor(CBlockIndex* pa, CBlockIndex* pb)
{
    if (pa->nHeight > pb->nHeight) {
        pa = pa->GetAncestor(pb->nHeight);
    } else if (pb->nHeight > pa->nHeight) {
        pb = pb->GetAncestor(pa->nHeight);
    }

    while (pa != pb && pa && pb) {
        pa = pa->pprev;
        pb = pb->pprev;
    }

    // Eventually all chain branches meet at the genesis block.
    assert(pa == pb);
    return pa;
}

/** Update pindexLastCommonBlock and add not-in-flight missing successors to vBlocks, until it has
 *  at most count entries. */
void FindNextBlocksToDownload(NodeId nodeid, unsigned int count, std::vector<CBlockIndex*>& vBlocks, NodeId& nodeStaller)
{
    if (count == 0)
        return;

    vBlocks.reserve(vBlocks.size() + count);
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    // Make sure pindexBestKnownBlock is up to date, we'll need it.
    ProcessBlockAvailability(nodeid);

    if (state->pindexBestKnownBlock == NULL || state->pindexBestKnownBlock->nChainWork < chainActive.Tip()->nChainWork) {
        // This peer has nothing interesting.
        return;
    }

    if (state->pindexLastCommonBlock == NULL) {
        // Bootstrap quickly by guessing a parent of our best tip is the forking point.
        // Guessing wrong in either direction is not a problem.
        state->pindexLastCommonBlock = chainActive[std::min(state->pindexBestKnownBlock->nHeight, chainActive.Height())];
    }

    // If the peer reorganized, our previous pindexLastCommonBlock may not be an ancestor
    // of their current tip anymore. Go back enough to fix that.
    state->pindexLastCommonBlock = LastCommonAncestor(state->pindexLastCommonBlock, state->pindexBestKnownBlock);
    if (state->pindexLastCommonBlock == state->pindexBestKnownBlock)
        return;

    std::vector<CBlockIndex*> vToFetch;
    CBlockIndex* pindexWalk = state->pindexLastCommonBlock;
    // Never fetch further than the best block we know the peer has, or more than BLOCK_DOWNLOAD_WINDOW + 1 beyond the last
    // linked block we have in common with this peer. The +1 is so we can detect stalling, namely if we would be able to
    // download that next block if the window were 1 larger.
    int nWindowEnd = state->pindexLastCommonBlock->nHeight + BLOCK_DOWNLOAD_WINDOW;
    int nMaxHeight = std::min<int>(state->pindexBestKnownBlock->nHeight, nWindowEnd + 1);
    NodeId waitingfor = -1;
    while (pindexWalk->nHeight < nMaxHeight) {
        // Read up to 128 (or more, if more blocks than that are needed) successors of pindexWalk (towards
        // pindexBestKnownBlock) into vToFetch. We fetch 128, because CBlockIndex::GetAncestor may be as expensive
        // as iterating over ~100 CBlockIndex* entries anyway.
        int nToFetch = std::min(nMaxHeight - pindexWalk->nHeight, std::max<int>(count - vBlocks.size(), 128));
        vToFetch.resize(nToFetch);
        pindexWalk = state->pindexBestKnownBlock->GetAncestor(pindexWalk->nHeight + nToFetch);
        vToFetch[nToFetch - 1] = pindexWalk;
        for (unsigned int i = nToFetch - 1; i > 0; i--) {
            vToFetch[i - 1] = vToFetch[i]->pprev;
        }

        // Iterate over those blocks in vToFetch (in forward direction), adding the ones that
        // are not yet downloaded and not in flight to vBlocks. In the mean time, update
        // pindexLastCommonBlock as long as all ancestors are already downloaded.
        BOOST_FOREACH (CBlockIndex* pindex, vToFetch) {
            if (!pindex->IsValid(BLOCK_VALID_TREE)) {
                // We consider the chain that this peer is on invalid.
                return;
            }
            if (pindex->nStatus & BLOCK_HAVE_DATA) {
                if (pindex->nChainTx)
                    state->pindexLastCommonBlock = pindex;
            } else if (mapBlocksInFlight.count(pindex->GetBlockHash()) == 0) {
                // The block is not already downloaded, and not yet in flight.
                if (pindex->nHeight > nWindowEnd) {
                    // We reached the end of the window.
                    if (vBlocks.size() == 0 && waitingfor != nodeid) {
                        // We aren't able to fetch anything, but we would be if the download window was one larger.
                        nodeStaller = waitingfor;
                    }
                    return;
                }
                vBlocks.push_back(pindex);
                if (vBlocks.size() == count) {
                    return;
                }
            } else if (waitingfor == -1) {
                // This is the first already-in-flight block.
                waitingfor = mapBlocksInFlight[pindex->GetBlockHash()].first;
            }
        }
    }
}

} // namespace

bool GetNodeStateStats(NodeId nodeid, CNodeStateStats& stats)
{
    LOCK(cs_main);
    CNodeState* state = State(nodeid);
    if (state == NULL)
        return false;
    stats.nMisbehavior = state->nMisbehavior;
    stats.nSyncHeight = state->pindexBestKnownBlock ? state->pindexBestKnownBlock->nHeight : -1;
    stats.nCommonHeight = state->pindexLastCommonBlock ? state->pindexLastCommonBlock->nHeight : -1;
    BOOST_FOREACH (const QueuedBlock& queue, state->vBlocksInFlight) {
        if (queue.pindex)
            stats.vHeightInFlight.push_back(queue.pindex->nHeight);
    }
    return true;
}

void RegisterNodeSignals(CNodeSignals& nodeSignals)
{
    nodeSignals.GetHeight.connect(&GetHeight);
    nodeSignals.ProcessMessages.connect(&ProcessMessages);
    nodeSignals.SendMessages.connect(&SendMessages);
    nodeSignals.InitializeNode.connect(&InitializeNode);
    nodeSignals.FinalizeNode.connect(&FinalizeNode);
}

void UnregisterNodeSignals(CNodeSignals& nodeSignals)
{
    nodeSignals.GetHeight.disconnect(&GetHeight);
    nodeSignals.ProcessMessages.disconnect(&ProcessMessages);
    nodeSignals.SendMessages.disconnect(&SendMessages);
    nodeSignals.InitializeNode.disconnect(&InitializeNode);
    nodeSignals.FinalizeNode.disconnect(&FinalizeNode);
}

CBlockIndex* FindForkInGlobalIndex(const CChain& chain, const CBlockLocator& locator)
{
    // Find the first block the caller has in the main chain
    BOOST_FOREACH (const uint256& hash, locator.vHave) {
        BlockMap::iterator mi = mapBlockIndex.find(hash);
        if (mi != mapBlockIndex.end()) {
            CBlockIndex* pindex = (*mi).second;
            if (chain.Contains(pindex))
                return pindex;
            if (pindex->GetAncestor(chain.Height()) == chain.Tip()) {
                return chain.Tip();
            }
        }
    }
    return chain.Genesis();
}

CCoinsViewCache* pcoinsTip = NULL;
CBlockTreeDB* pblocktree = NULL;
CZerocoinDB* zerocoinDB = NULL;
CSporkDB* pSporkDB = NULL;

//////////////////////////////////////////////////////////////////////////////
//
// mapOrphanTransactions
//

bool AddOrphanTx(const CTransaction& tx, NodeId peer)
{
    uint256 hash = tx.GetHash();
    if (mapOrphanTransactions.count(hash))
        return false;

    // Ignore big transactions, to avoid a
    // send-big-orphans memory exhaustion attack. If a peer has a legitimate
    // large transaction with a missing parent then we assume
    // it will rebroadcast it later, after the parent transaction(s)
    // have been mined or received.
    // 10,000 orphans, each of which is at most 5,000 bytes big is
    // at most 500 megabytes of orphans:
    unsigned int sz = tx.GetSerializeSize(SER_NETWORK, CTransaction::CURRENT_VERSION);
    if (sz > 5000) {
        LogPrint("mempool", "ignoring large orphan tx (size: %u, hash: %s)\n", sz, hash.ToString());
        return false;
    }

    mapOrphanTransactions[hash].tx = tx;
    mapOrphanTransactions[hash].fromPeer = peer;
    BOOST_FOREACH (const CTxIn& txin, tx.vin)
        mapOrphanTransactionsByPrev[txin.prevout.hash].insert(hash);

    LogPrint("mempool", "stored orphan tx %s (mapsz %u prevsz %u)\n", hash.ToString(),
        mapOrphanTransactions.size(), mapOrphanTransactionsByPrev.size());
    return true;
}

void static EraseOrphanTx(uint256 hash)
{
    map<uint256, COrphanTx>::iterator it = mapOrphanTransactions.find(hash);
    if (it == mapOrphanTransactions.end())
        return;
    BOOST_FOREACH (const CTxIn& txin, it->second.tx.vin) {
        map<uint256, set<uint256> >::iterator itPrev = mapOrphanTransactionsByPrev.find(txin.prevout.hash);
        if (itPrev == mapOrphanTransactionsByPrev.end())
            continue;
        itPrev->second.erase(hash);
        if (itPrev->second.empty())
            mapOrphanTransactionsByPrev.erase(itPrev);
    }
    mapOrphanTransactions.erase(it);
}

void EraseOrphansFor(NodeId peer)
{
    int nErased = 0;
    map<uint256, COrphanTx>::iterator iter = mapOrphanTransactions.begin();
    while (iter != mapOrphanTransactions.end()) {
        map<uint256, COrphanTx>::iterator maybeErase = iter++; // increment to avoid iterator becoming invalid
        if (maybeErase->second.fromPeer == peer) {
            EraseOrphanTx(maybeErase->second.tx.GetHash());
            ++nErased;
        }
    }
    if (nErased > 0) LogPrint("mempool", "Erased %d orphan tx from peer %d\n", nErased, peer);
}


unsigned int LimitOrphanTxSize(unsigned int nMaxOrphans)
{
    unsigned int nEvicted = 0;
    while (mapOrphanTransactions.size() > nMaxOrphans) {
        // Evict a random orphan:
        uint256 randomhash = GetRandHash();
        map<uint256, COrphanTx>::iterator it = mapOrphanTransactions.lower_bound(randomhash);
        if (it == mapOrphanTransactions.end())
            it = mapOrphanTransactions.begin();
        EraseOrphanTx(it->first);
        ++nEvicted;
    }
    return nEvicted;
}

bool IsStandardTx(const CTransaction& tx, string& reason)
{
    AssertLockHeld(cs_main);
    if (tx.nVersion > CTransaction::CURRENT_VERSION || tx.nVersion < 1) {
        reason = "version";
        return false;
    }

    // Treat non-final transactions as non-standard to prevent a specific type
    // of double-spend attack, as well as DoS attacks. (if the transaction
    // can't be mined, the attacker isn't expending resources broadcasting it)
    // Basically we don't want to propagate transactions that can't be included in
    // the next block.
    //
    // However, IsFinalTx() is confusing... Without arguments, it uses
    // chainActive.Height() to evaluate nLockTime; when a block is accepted, chainActive.Height()
    // is set to the value of nHeight in the block. However, when IsFinalTx()
    // is called within CBlock::AcceptBlock(), the height of the block *being*
    // evaluated is what is used. Thus if we want to know if a transaction can
    // be part of the *next* block, we need to call IsFinalTx() with one more
    // than chainActive.Height().
    //
    // Timestamps on the other hand don't get any special treatment, because we
    // can't know what timestamp the next block will have, and there aren't
    // timestamp applications where it matters.
    if (!IsFinalTx(tx, chainActive.Height() + 1)) {
        reason = "non-final";
        return false;
    }

    // Extremely large transactions with lots of inputs can cost the network
    // almost as much to process as they cost the sender in fees, because
    // computing signature hashes is O(ninputs*txsize). Limiting transactions
    // to MAX_STANDARD_TX_COST mitigates CPU exhaustion attacks.
    unsigned int sz = GetTransactionCost(tx);
    if (sz >= MAX_STANDARD_TX_COST) {
        reason = "tx-size";
        return false;
    }

    for (const CTxIn& txin : tx.vin) {
        if (txin.scriptSig.IsZerocoinSpend())
            continue;
        // Biggest 'standard' txin is a 15-of-15 P2SH multisig with compressed
        // keys. (remember the 520 byte limit on redeemScript size) That works
        // out to a (15*(33+1))+3=513 byte redeemScript, 513+1+15*(73+1)+3=1627
        // bytes of scriptSig, which we round off to 1650 bytes for some minor
        // future-proofing. That's also enough to spend a 20-of-20
        // CHECKMULTISIG scriptPubKey, though such a scriptPubKey is not
        // considered standard)
        if (txin.scriptSig.size() > 1650) {
            reason = "scriptsig-size";
            return false;
        }
        if (!txin.scriptSig.IsPushOnly()) {
            reason = "scriptsig-not-pushonly";
            return false;
        }
    }

    unsigned int nDataOut = 0;
    txnouttype whichType;
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        if (!::IsStandard(txout.scriptPubKey, whichType)) {
            reason = "scriptpubkey";
            return false;
        }

        if (whichType == TX_NULL_DATA)
            nDataOut++;
        else if ((whichType == TX_MULTISIG) && (!fIsBareMultisigStd)) {
            reason = "bare-multisig";
            return false;
        } else if (txout.IsDust(::minRelayTxFee)) {
            reason = "dust";
            return false;
        }
    }

    // only one OP_RETURN txout is permitted
    if (nDataOut > 1) {
        reason = "multi-op-return";
        return false;
    }

    return true;
}

bool IsFinalTx(const CTransaction& tx, int nBlockHeight, int64_t nBlockTime)
{
    AssertLockHeld(cs_main);
    // Time based nLockTime implemented in 0.1.6
    if (tx.nLockTime == 0)
        return true;
    if (nBlockHeight == 0)
        nBlockHeight = chainActive.Height();
    if (nBlockTime == 0)
        nBlockTime = GetAdjustedTime();
    if ((int64_t)tx.nLockTime < ((int64_t)tx.nLockTime < LOCKTIME_THRESHOLD ? (int64_t)nBlockHeight : nBlockTime))
        return true;
    BOOST_FOREACH (const CTxIn& txin, tx.vin)
        if (!txin.IsFinal())
            return false;
    return true;
}

/**
 * Check transaction inputs to mitigate two
 * potential denial-of-service attacks:
 *
 * 1. scriptSigs with extra data stuffed into them,
 *    not consumed by scriptPubKey (or P2SH script)
 * 2. P2SH scripts with a crazy number of expensive
 *    CHECKSIG/CHECKMULTISIG operations
 */
bool AreInputsStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase() || tx.IsZerocoinSpend())
        return true; // Coinbases don't use vin normally

    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);

        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        // get the scriptPubKey corresponding to this input:
        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions))
            return false;

        if (whichType == TX_SCRIPTHASH) {
            std::vector<std::vector<unsigned char> > stack;
            // convert the scriptSig into a stack, so we can inspect the redeemScript
            if (!EvalScript(stack, tx.vin[i].scriptSig, SCRIPT_VERIFY_NONE, BaseSignatureChecker(), SIGVERSION_BASE))
                return false;
            if (stack.empty())
                return false;
            CScript subscript(stack.back().begin(), stack.back().end());
            if (subscript.GetSigOpCount(true) > MAX_P2SH_SIGOPS) {
                return false;
            }
        }
    }

    return true;
}

int64_t GetVirtualTransactionSize(int64_t nCost)
{
    return (nCost + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR;
}

int64_t GetVirtualTransactionSize(const CTransaction& tx)
{
    return GetVirtualTransactionSize(GetTransactionCost(tx));
}

unsigned int GetLegacySigOpCount(const CTransaction& tx)
{
    unsigned int nSigOps = 0;
    BOOST_FOREACH (const CTxIn& txin, tx.vin) {
        nSigOps += txin.scriptSig.GetSigOpCount(false);
    }
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        nSigOps += txout.scriptPubKey.GetSigOpCount(false);
    }
    return nSigOps;
}

unsigned int GetP2SHSigOpCount(const CTransaction& tx, const CCoinsViewCache& inputs)
{
    if (tx.IsCoinBase() || tx.IsZerocoinSpend())
        return 0;

    unsigned int nSigOps = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prevout = inputs.GetOutputFor(tx.vin[i]);
        if (prevout.scriptPubKey.IsPayToScriptHash())
            nSigOps += prevout.scriptPubKey.GetSigOpCount(tx.vin[i].scriptSig);
    }
    return nSigOps;
}

int GetInputAge(CTxIn& vin)
{
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK(mempool.cs);
        CCoinsViewMemPool viewMempool(pcoinsTip, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        const CCoins* coins = view.AccessCoins(vin.prevout.hash);

        if (coins) {
            if (coins->nHeight < 0) return 0;
            return (chainActive.Tip()->nHeight + 1) - coins->nHeight;
        } else
            return -1;
    }
}

int64_t GetTransactionSigOpCost(const CTransaction& tx, const CCoinsViewCache& inputs, int flags)
{
    int64_t nSigOps = GetLegacySigOpCount(tx) * WITNESS_SCALE_FACTOR;

    if (tx.IsCoinBase() || tx.ContainsZerocoins())
        return nSigOps;

    if (flags & SCRIPT_VERIFY_P2SH) {
        nSigOps += GetP2SHSigOpCount(tx, inputs) * WITNESS_SCALE_FACTOR;
    }

    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prevout = inputs.GetOutputFor(tx.vin[i]);
        nSigOps += CountWitnessSigOps(tx.vin[i].scriptSig, prevout.scriptPubKey, i < tx.wit.vtxinwit.size() ? &tx.wit.vtxinwit[i].scriptWitness : NULL, flags);
    }
    return nSigOps;
}

int GetInputAgeIX(uint256 nTXHash, CTxIn& vin)
{
    int sigs = 0;
    int nResult = GetInputAge(vin);
    if (nResult < 0) nResult = 0;

    if (nResult < 6) {
        std::map<uint256, CTransactionLock>::iterator i = mapTxLocks.find(nTXHash);
        if (i != mapTxLocks.end()) {
            sigs = (*i).second.CountSignatures();
        }
        if (sigs >= SWIFTTX_SIGNATURES_REQUIRED) {
            return nSwiftTXDepth + nResult;
        }
    }

    return -1;
}

int GetIXConfirmations(uint256 nTXHash)
{
    int sigs = 0;

    std::map<uint256, CTransactionLock>::iterator i = mapTxLocks.find(nTXHash);
    if (i != mapTxLocks.end()) {
        sigs = (*i).second.CountSignatures();
    }
    if (sigs >= SWIFTTX_SIGNATURES_REQUIRED) {
        return nSwiftTXDepth;
    }

    return 0;
}

// ppcoin: total coin age spent in transaction, in the unit of coin-days.
// Only those coins meeting minimum age requirement counts. As those
// transactions not in main chain are not currently indexed so we
// might not find out about their coin age. Older transactions are
// guaranteed to be in main chain by sync-checkpoint. This rule is
// introduced to help nodes establish a consistent view of the coin
// age (trust score) of competing branches.
bool GetCoinAge(const CTransaction& tx, const unsigned int nTxTime, uint64_t& nCoinAge)
{
    uint256 bnCentSecond = 0; // coin age in the unit of cent-seconds
    nCoinAge = 0;

    CBlockIndex* pindex = NULL;
    BOOST_FOREACH (const CTxIn& txin, tx.vin) {
        // First try finding the previous transaction in database
        CTransaction txPrev;
        uint256 hashBlockPrev;
        if (!GetTransaction(txin.prevout.hash, txPrev, hashBlockPrev, true)) {
            LogPrintf("GetCoinAge: failed to find vin transaction \n");
            continue; // previous transaction not in main chain
        }

        BlockMap::iterator it = mapBlockIndex.find(hashBlockPrev);
        if (it != mapBlockIndex.end())
            pindex = it->second;
        else {
            LogPrintf("GetCoinAge() failed to find block index \n");
            continue;
        }

        // Read block header
        CBlockHeader prevblock = pindex->GetBlockHeader();

        if (prevblock.nTime + StakeMinAgev2() > nTxTime)
            continue; // only count coins meeting min age requirement

        if (nTxTime < prevblock.nTime) {
            LogPrintf("GetCoinAge: Timestamp Violation: txtime less than txPrev.nTime");
            return false; // Transaction timestamp violation
        }

        int64_t nValueIn = txPrev.vout[txin.prevout.n].nValue;
        bnCentSecond += uint256(nValueIn) * (nTxTime - prevblock.nTime);
    }

    uint256 bnCoinDay = bnCentSecond / COIN / (24 * 60 * 60);
    LogPrintf("coin age bnCoinDay=%s\n", bnCoinDay.ToString().c_str());
    nCoinAge = bnCoinDay.GetCompact();
    return true;
}

bool MoneyRange(CAmount nValueOut)
{
    return nValueOut >= 0 && nValueOut <= Params().MaxMoneyOut();
}

int GetZerocoinStartHeight()
{
    return Params().Zerocoin_StartHeight();
}

libzerocoin::ZerocoinParams* GetZerocoinParams(int nHeight)
{
    return nHeight > Params().Zerocoin_LastOldParams() ? Params().Zerocoin_Params() : Params().OldZerocoin_Params();
}

void FindMints(vector<CMintMeta> vMintsToFind, vector<CMintMeta>& vMintsToUpdate, vector<CMintMeta>& vMissingMints)
{
    // see which mints are in our public zerocoin database. The mint should be here if it exists, unless
    // something went wrong
    for (CMintMeta meta : vMintsToFind) {
        uint256 txHash;
        if (!zerocoinDB->ReadCoinMint(meta.hashPubcoin, txHash)) {
            vMissingMints.push_back(meta);
            continue;
        }

        // make sure the txhash and block height meta data are correct for this mint
        CTransaction tx;
        uint256 hashBlock;
        if (!GetTransaction(txHash, tx, hashBlock, true)) {
            LogPrintf("%s : cannot find tx %s\n", __func__, txHash.GetHex());
            vMissingMints.push_back(meta);
            continue;
        }

        if (!mapBlockIndex.count(hashBlock)) {
            LogPrintf("%s : cannot find block %s\n", __func__, hashBlock.GetHex());
            vMissingMints.push_back(meta);
            continue;
        }

        //see if this mint is spent
        uint256 hashTxSpend = 0;
        bool fSpent = zerocoinDB->ReadCoinSpend(meta.hashSerial, hashTxSpend);

        //if marked as spent, check that it actually made it into the chain
        CTransaction txSpend;
        uint256 hashBlockSpend;
        if (fSpent && !GetTransaction(hashTxSpend, txSpend, hashBlockSpend, true)) {
            LogPrintf("%s : cannot find spend tx %s\n", __func__, hashTxSpend.GetHex());
            meta.isUsed = false;
            vMintsToUpdate.push_back(meta);
            continue;
        }

        //The mint has been incorrectly labelled as spent in zerocoinDB and needs to be undone
        int nHeightTx = 0;
        uint256 hashSerial = meta.hashSerial;
        uint256 txidSpend;
        if (fSpent && !IsSerialInBlockchain(hashSerial, nHeightTx, txidSpend)) {
            LogPrintf("%s : cannot find block %s. Erasing coinspend from zerocoinDB.\n", __func__, hashBlockSpend.GetHex());
            meta.isUsed = false;
            vMintsToUpdate.push_back(meta);
            continue;
        }

        // is the denomination correct?
        for (auto& out : tx.vout) {
            if (!out.IsZerocoinMint())
                continue;
            PublicCoin pubcoin(meta.nVersion < libzerocoin::PrivateCoin::PUBKEY_VERSION ? Params().OldZerocoin_Params() : Params().Zerocoin_Params());
            CValidationState state;
            TxOutToPublicCoin(out, pubcoin, state);
            if (GetPubCoinHash(pubcoin.getValue()) == meta.hashPubcoin && pubcoin.getDenomination() != meta.denom) {
                LogPrintf("%s: found mismatched denom pubcoinhash = %s\n", __func__, meta.hashPubcoin.GetHex());
                meta.denom = pubcoin.getDenomination();
                vMintsToUpdate.emplace_back(meta);
            }
        }

        // if meta data is correct, then no need to update
        if (meta.txid == txHash && meta.nHeight == mapBlockIndex[hashBlock]->nHeight && meta.isUsed == fSpent)
            continue;

        //mark this mint for update
        meta.txid = txHash;
        meta.nHeight = mapBlockIndex[hashBlock]->nHeight;
        meta.isUsed = fSpent;
        LogPrintf("%s: found updates for pubcoinhash = %s\n", __func__, meta.hashPubcoin.GetHex());

        vMintsToUpdate.push_back(meta);
    }
}

bool GetZerocoinMint(const CBigNum& bnPubcoin, uint256& txHash)
{
    txHash = 0;
    return zerocoinDB->ReadCoinMint(bnPubcoin, txHash);
}

bool IsPubcoinInBlockchain(const uint256& hashPubcoin, uint256& txid)
{
    txid = 0;
    return zerocoinDB->ReadCoinMint(hashPubcoin, txid);
}

bool IsSerialKnown(const CBigNum& bnSerial)
{
    uint256 txHash = 0;
    return zerocoinDB->ReadCoinSpend(bnSerial, txHash);
}

bool IsSerialInBlockchain(const CBigNum& bnSerial, int& nHeightTx)
{
    uint256 txHash = 0;
    // if not in zerocoinDB then its not in the blockchain
    if (!zerocoinDB->ReadCoinSpend(bnSerial, txHash))
        return false;

    return IsTransactionInChain(txHash, nHeightTx);
}

bool IsSerialInBlockchain(const uint256& hashSerial, int& nHeightTx, uint256& txidSpend)
{
    CTransaction tx;
    return IsSerialInBlockchain(hashSerial, nHeightTx, txidSpend, tx);
}

bool IsSerialInBlockchain(const uint256& hashSerial, int& nHeightTx, uint256& txidSpend, CTransaction& tx)
{
    txidSpend = 0;
    // if not in zerocoinDB then its not in the blockchain
    if (!zerocoinDB->ReadCoinSpend(hashSerial, txidSpend))
        return false;
    return IsTransactionInChain(txidSpend, nHeightTx, tx);
}

bool RemoveSerialFromDB(const CBigNum& bnSerial)
{
    return zerocoinDB->EraseCoinSpend(bnSerial);
}

/** zerocoin transaction checks */
bool RecordMintToDB(PublicCoin publicZerocoin, const uint256& txHash)
{
    //Check the pubCoinValue didn't already store in the zerocoin database. todo: pubcoin memory map?
    //write the zerocoinmint to db if we don't already have it
    //note that many of the mint parameters are not set here because those params are private to the minter
    CZerocoinMint pubCoinTx;
    uint256 hashFromDB;
    if (zerocoinDB->ReadCoinMint(publicZerocoin.getValue(), hashFromDB)) {
        if (hashFromDB == txHash)
            return true;

        LogPrintf("RecordMintToDB: failed, we already have this public coin recorded\n");
        return false;
    }

    if (!zerocoinDB->WriteCoinMint(publicZerocoin, txHash)) {
        LogPrintf("RecordMintToDB: failed to record public coin to DB\n");
        return false;
    }

    return true;
}

bool TxOutToPublicCoin(const CTxOut txout, PublicCoin& pubCoin, CValidationState& state)
{
    CBigNum publicZerocoin;
    vector<unsigned char> vchZeroMint;
    vchZeroMint.insert(vchZeroMint.end(), txout.scriptPubKey.begin() + SCRIPT_OFFSET,
        txout.scriptPubKey.begin() + txout.scriptPubKey.size());
    publicZerocoin.setvch(vchZeroMint);

    CoinDenomination denomination = AmountToZerocoinDenomination(txout.nValue);
    LogPrint("zero", "%s ZCPRINT denomination %d pubcoin %s\n", __func__, denomination, publicZerocoin.GetHex());
    if (denomination == ZQ_ERROR)
        return state.DoS(100, error("TxOutToPublicCoin : txout.nValue is not correct"));

    PublicCoin checkPubCoin(Params().Zerocoin_Params(), publicZerocoin, denomination);
    pubCoin = checkPubCoin;

    return true;
}

bool BlockToPubcoinList(const CBlock& block, list<PublicCoin>& listPubcoins)
{
    for (const CTransaction tx : block.vtx) {
        if (!tx.IsZerocoinMint())
            continue;

        for (unsigned int i = 0; i < tx.vout.size(); i++) {
            const CTxOut txOut = tx.vout[i];
            if (!txOut.scriptPubKey.IsZerocoinMint())
                continue;

            CValidationState state;
            PublicCoin pubCoin(Params().Zerocoin_Params());
            if (!TxOutToPublicCoin(txOut, pubCoin, state))
                return false;

            listPubcoins.emplace_back(pubCoin);
        }
    }

    return true;
}

//return a list of zerocoin mints contained in a specific block
bool BlockToZerocoinMintList(const CBlock& block, std::list<CZerocoinMint>& vMints)
{
    for (const CTransaction tx : block.vtx) {
        if (!tx.IsZerocoinMint())
            continue;

        for (unsigned int i = 0; i < tx.vout.size(); i++) {
            const CTxOut txOut = tx.vout[i];
            if (!txOut.scriptPubKey.IsZerocoinMint())
                continue;

            CValidationState state;
            PublicCoin pubCoin(Params().Zerocoin_Params());
            if (!TxOutToPublicCoin(txOut, pubCoin, state))
                return false;

            CZerocoinMint mint = CZerocoinMint(pubCoin.getDenomination(), pubCoin.getValue(), 0, 0, false, 1, nullptr);
            mint.SetTxHash(tx.GetHash());
            vMints.push_back(mint);
        }
    }

    return true;
}

bool BlockToMintValueVector(const CBlock& block, const CoinDenomination denom, vector<CBigNum>& vValues)
{
    for (const CTransaction tx : block.vtx) {
        if (!tx.IsZerocoinMint())
            continue;

        for (const CTxOut txOut : tx.vout) {
            if (!txOut.scriptPubKey.IsZerocoinMint())
                continue;

            CValidationState state;
            PublicCoin coin(Params().Zerocoin_Params());
            if (!TxOutToPublicCoin(txOut, coin, state))
                return false;

            if (coin.getDenomination() != denom)
                continue;

            vValues.push_back(coin.getValue());
        }
    }

    return true;
}

//return a list of zerocoin spends contained in a specific block, list may have many denominations
std::list<libzerocoin::CoinDenomination> ZerocoinSpendListFromBlock(const CBlock& block)
{
    std::list<libzerocoin::CoinDenomination> vSpends;
    for (const CTransaction tx : block.vtx) {
        if (!tx.IsZerocoinSpend())
            continue;

        for (const CTxIn txin : tx.vin) {
            if (!txin.scriptSig.IsZerocoinSpend())
                continue;

            libzerocoin::CoinDenomination c = libzerocoin::IntToZerocoinDenomination(txin.nSequence);
            vSpends.push_back(c);
        }
    }
    return vSpends;
}

bool CheckZerocoinMint(const uint256& txHash, const CTxOut& txout, CValidationState& state, bool fCheckOnly)
{
    PublicCoin pubCoin(Params().Zerocoin_Params());
    if (!TxOutToPublicCoin(txout, pubCoin, state))
        return state.DoS(100, error("CheckZerocoinMint(): TxOutToPublicCoin() failed"));

    if (!pubCoin.validate())
        return state.DoS(100, error("CheckZerocoinMint() : PubCoin does not validate"));

    return true;
}

CoinSpend TxInToZerocoinSpend(const CTxIn& txin)
{
    // extract the spend from the txin
    std::vector<char, zero_after_free_allocator<char> > dataTxIn;
    dataTxIn.insert(dataTxIn.end(), txin.scriptSig.begin() + BIGNUM_SIZE, txin.scriptSig.end());

    CDataStream serializedCoinSpend(dataTxIn, SER_NETWORK, PROTOCOL_VERSION);
    return CoinSpend(Params().Zerocoin_Params(), GetZerocoinParams(chainActive.Height()), serializedCoinSpend);
}

bool ContextualCheckZerocoinMint(const CTransaction& tx, const PublicCoin& coin, const CBlockIndex* pindex)
{
    if (pindex->nHeight > Params().Zerocoin_LastOldParams() && Params().NetworkID() != CBaseChainParams::TESTNET) {
        //See if this coin has already been added to the blockchain
        uint256 txid;
        if (zerocoinDB->ReadCoinMint(coin.getValue(), txid))
            return error("%s: pubcoin %s was already accumulated in tx %s", __func__,
                coin.getValue().GetHex().substr(0, 10),
                txid.GetHex());
    }
    return true;
}

bool ContextualCheckZerocoinSpend(const CTransaction& tx, const CoinSpend& spend, CBlockIndex* pindex, const uint256& hashBlock)
{
    //Check to see if the zABET is properly signed
    if (pindex->nHeight > Params().Zerocoin_LastOldParams()) {
        if (!spend.HasValidSignature())
            return error("%s: V2 zABET spend does not have a valid signature", __func__);

        libzerocoin::SpendType expectedType = libzerocoin::SpendType::SPEND;
        if (tx.IsCoinStake())
            expectedType = libzerocoin::SpendType::STAKE;
        if (spend.getSpendType() != expectedType) {
            return error("%s: trying to spend zABET without the correct spend type. txid=%s", __func__,
                tx.GetHash().GetHex());
        }
    }

    //Reject serial's that are already in the blockchain
    int nHeightTx = 0;
    if (IsSerialInBlockchain(spend.getCoinSerialNumber(), nHeightTx))
        return error("%s : zABET spend with serial %s is already in block %d\n", __func__,
            spend.getCoinSerialNumber().GetHex(), nHeightTx);

    //Reject serial's that are not in the acceptable value range
    libzerocoin::ZerocoinParams* paramsToUse = spend.getVersion() < libzerocoin::PrivateCoin::PUBKEY_VERSION ? Params().OldZerocoin_Params() : Params().Zerocoin_Params();
    if (!spend.HasValidSerial(paramsToUse))
        return error("%s : zABET spend with serial %s from tx %s is not in valid range\n", __func__,
            spend.getCoinSerialNumber().GetHex(), tx.GetHash().GetHex());

    return true;
}

bool CheckZerocoinSpend(const CTransaction tx, bool fVerifySignature, CValidationState& state, int nHeight)
{
    //max needed non-mint outputs should be 2 - one for redemption address and a possible 2nd for change
    if (tx.vout.size() > 2) {
        int outs = 0;
        for (const CTxOut out : tx.vout) {
            if (out.IsZerocoinMint())
                continue;
            outs++;
        }
        if (outs > 2)
            return state.DoS(100, error("CheckZerocoinSpend(): over two non-mint outputs in a zerocoinspend transaction"));
    }

    //compute the txout hash that is used for the zerocoinspend signatures
    CMutableTransaction txTemp;
    for (const CTxOut out : tx.vout) {
        txTemp.vout.push_back(out);
    }
    uint256 hashTxOut = txTemp.GetHash();

    bool fValidated = false;
    set<CBigNum> serials;
    list<CoinSpend> vSpends;
    CAmount nTotalRedeemed = 0;
    for (const CTxIn& txin : tx.vin) {
        //only check txin that is a zcspend
        if (!txin.scriptSig.IsZerocoinSpend())
            continue;

        CoinSpend newSpend = TxInToZerocoinSpend(txin);
        vSpends.push_back(newSpend);

        //check that the denomination is valid
        if (newSpend.getDenomination() == ZQ_ERROR)
            return state.DoS(100, error("Zerocoinspend does not have the correct denomination"));

        //check that denomination is what it claims to be in nSequence
        if (newSpend.getDenomination() != txin.nSequence)
            return state.DoS(100, error("Zerocoinspend nSequence denomination does not match CoinSpend"));

        //make sure the txout has not changed
        if (newSpend.getTxOutHash() != hashTxOut)
            return state.DoS(100, error("Zerocoinspend does not use the same txout that was used in the SoK"));

        // Skip signature verification during initial block download
        if (fVerifySignature) {
            //see if we have record of the accumulator used in the spend tx
            CBigNum bnAccumulatorValue = 0;
            if (!zerocoinDB->ReadAccumulatorValue(newSpend.getAccumulatorChecksum(), bnAccumulatorValue)) {
                uint32_t nChecksum = newSpend.getAccumulatorChecksum();
                return state.DoS(100, error("%s: Zerocoinspend could not find accumulator associated with checksum %s", __func__, HexStr(BEGIN(nChecksum), END(nChecksum))));
            }

            Accumulator accumulator(GetZerocoinParams(nHeight), newSpend.getDenomination(), bnAccumulatorValue);

            //Check that the coin has been accumulated
            if (!newSpend.Verify(accumulator))
                return state.DoS(100, error("CheckZerocoinSpend(): zerocoin spend did not verify"));
        }

        if (serials.count(newSpend.getCoinSerialNumber()))
            return state.DoS(100, error("Zerocoinspend serial is used twice in the same tx"));
        serials.insert(newSpend.getCoinSerialNumber());

        //make sure that there is no over redemption of coins
        nTotalRedeemed += ZerocoinDenominationToAmount(newSpend.getDenomination());
        fValidated = true;
    }

    if (nTotalRedeemed < tx.GetValueOut()) {
        LogPrintf("redeemed = %s , spend = %s \n", FormatMoney(nTotalRedeemed), FormatMoney(tx.GetValueOut()));
        return state.DoS(100, error("Transaction spend more than was redeemed in zerocoins"));
    }

    return fValidated;
}

bool CheckTransaction(const CTransaction& tx, bool fZerocoinActive, bool fRejectBadUTXO, CValidationState& state, bool fWitnessEnabled)
{
    // Basic checks that don't depend on any context
    if (tx.vin.empty())
        return state.DoS(10, error("CheckTransaction() : vin empty"),
            REJECT_INVALID, "bad-txns-vin-empty");
    if (tx.vout.empty())
        return state.DoS(10, error("CheckTransaction() : vout empty"),
            REJECT_INVALID, "bad-txns-vout-empty");

    // Size limits (this doesn't take the witness into account, as that hasn't been checked for malleability)
    if (::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) > MAX_BLOCK_BASE_SIZE)
        return state.DoS(100, false, REJECT_INVALID, "bad-txns-oversize");

    // Check for negative or overflow output values
    CAmount nValueOut = 0;
    int nZCSpendCount = 0;
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        if (txout.nValue < 0)
            return state.DoS(100, error("CheckTransaction() : txout.nValue negative"),
                REJECT_INVALID, "bad-txns-vout-negative");
        if (txout.nValue > Params().MaxMoneyOut())
            return state.DoS(100, error("CheckTransaction() : txout.nValue too high"),
                REJECT_INVALID, "bad-txns-vout-toolarge");
        nValueOut += txout.nValue;
        if (!MoneyRange(nValueOut))
            return state.DoS(100, error("CheckTransaction() : txout total out of range"),
                REJECT_INVALID, "bad-txns-txouttotal-toolarge");
        if (fZerocoinActive && txout.IsZerocoinMint()) {
            if (!CheckZerocoinMint(tx.GetHash(), txout, state, true))
                return state.DoS(100, error("CheckTransaction() : invalid zerocoin mint"));
        }
        if (fZerocoinActive && txout.scriptPubKey.IsZerocoinSpend())
            nZCSpendCount++;
    }

    if (fZerocoinActive) {
        if (nZCSpendCount > Params().Zerocoin_MaxSpendsPerTransaction())
            return state.DoS(100, error("CheckTransaction() : there are more zerocoin spends than are allowed in one transaction"));

        if (tx.IsZerocoinSpend()) {
            //require that a zerocoinspend only has inputs that are zerocoins
            for (const CTxIn in : tx.vin) {
                if (!in.scriptSig.IsZerocoinSpend())
                    return state.DoS(100,
                        error("CheckTransaction() : zerocoinspend contains inputs that are not zerocoins"));
            }

            // Do not require signature verification if this is initial sync and a block over 24 hours old
            bool fVerifySignature = !IsInitialBlockDownload() && (GetTime() - chainActive.Tip()->GetBlockTime() < (60 * 60 * 24));
            if (!CheckZerocoinSpend(tx, fVerifySignature, state, chainActive.Height()))
                return state.DoS(100, error("CheckTransaction() : invalid zerocoin spend"));
        }
    }

	for (const CTxIn& txin : tx.vin) {
        // check if vin is known stolen/frozen fund (will disregard the tx/block)
        if ((txin.prevout.hash == uint256("0xff8789138a6ea9c2aaadb11bd739986d6fba97793db2f768e1783e5a4345d88c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0702a32587cd06c9ea68c37789b08a6684b09c57388496a80a2e170b3f73a359") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfe3a44e85838eb34e21938c968ba27b8edb6984be0ec251e1d70a628132872df") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xffd80ef108adf22a3b3eb89df1b81bc46a9ac6293827cac78049b68103bc8b1a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfe405e98795a3323d3a50c9b83db4fc1d77c86341358c3434d8dbf71a95bd7f6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfe51c325560e8a06c77297dc0a61cc5d286b05c01debd091ba98f0af98bb6c09") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xff3dca1a5036167d24aac69da72c01a783b653a1823189b04ead8e0ecee7dffd") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xffda8823e942a5618baf3a0ebf7372fb28cb70130bd8cd945a06df395dc9e18b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x179cf1dc3c911c372bd0760d2fa8d4439574747e0a0eb77f02b87b1c1285ea17") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x97ce018edcfe9454efc81e9ca2f9cd239effacaf4f5f201ad41372e21993dd6e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2292ba2ee7414a2cd7ac00443b608e547c7904e98918d77d11cd454a82ae8e40") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe032576a76cd9c9382f26297fb3db4cc371c9eea00acbc7f0a66f351ca1dd240") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3f695c5b8bd2c5eda3f2933cf0f0adb9d7ee636bd22a2fe2122ca960a63583b3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9730ec7bbef63983a7f340046912e31678b428287cfc807fc7d2f64e7a6610a8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0255f2835c49af406b1a58e2cf9f3dfbf07e7e9975b4b320819e8312459d4fcf") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6d46c5544db327dc640762c9dadd2cea202f9ffd53d50dfc8273ead5ac36b042") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaaeb70e8e6daa5c3ad4b585ae2396544bb7bb94239e0cf5d78f4c9694d493471") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x64cbf8d5ffd822f651788b2e9a4caedcc40ca60fe35f6951074c52321f7d6784") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7d21f020021e7ba828306820976891f45cdb5167b695f09df0aea21e6d8859ee") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7c57da9174f8ea30150912ec64306ef33a72d5277d104d537ff8bd0a86de95ca") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2e0290ced3cc7436c18da7ef4c6e2d6ce1d1d193279379c0c2a8fccb2522c080") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xbd048da3e04d7c212b09e6ddd2332c13bd9206e40594499f181a8f4fa0d3ebcd") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x09aba50a23c0046f023ddeddd20ae518ceaa12b570c478c76ca7d83adaa2a7e9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x989731b36ed78469d5bad5c9eefc030a455079c6f5b23d2274f8f7e5af2ed916") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x56336ae9d7603914389bab4784ae93a2c6a030c96e9a48c182691cdceb967597") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xafe40a5d8e24408cf8c282ef42be9d739020e9c53bdcf6c020654785c0d00dbb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x15b707af97b80b65324254aae333bc7fcf31c356e96b6a9fb5746e1ad37186df") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x26c71d5dce08db1070f4cc48074cbefec041c6fa280e9be17d10837543d0617f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3ffc5fc1fc28cf0501d58be7cc2e620f79ae33f8d9fdef4f4488a5dcfe788b16") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x69d679a58b6aadd261c947d426cac9dd3cf6f15f3649b383493787e27fb01cfb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe316b700fb3d58f04335b3bb7b8eb305c04d4c76d6c69c7ffd43b65cf2b602d9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xae8986f6c46382fae48b9b6ce3ff80302ef14441f28e4e11fa01f8c2db606278") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3da8c3ff218887f4815df67ac258c1ad97e21e5483b2cd361bcd3360901060ab") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x23674b1751d59eb8f5e371a99d4a1ec8b5046f03348a648ff0a4f7196c270cb2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9cb55562653e07d67ec4d9275c3e714467e7102fa23e2a5386c588dd32551d69") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x49c09ed1ded3ec74dc71da8bf510c79766ff9b8131e50e368cd758f32e7a71fc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x32f232d7fc31459f3edc4d769facf773495b510b6aa2dac3d0c0f6c1378111cf") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd4814ac005bb0e636d6d1bcb07bdf85098d35362f3933c99f67b502d41c9c5d1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0dd2be9efb1fdc793959f91cc70652b2a7e1f63b24e2416995503fd797badd7e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0e9191a7f233552eefd9f851ceb0aeb1641bb6a669629a28d0facdc60a962a68") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x672c68c558217bacd8632f97fad5c729a851123774eb8b7c25148ead453fb0f4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xff41807d7d75640fadab7e96beacb29176cd39f6782d88d602f1563731d4706c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc9438c07b7275a53c90fdba828eaa9b52d284685f0a0a2f810410c822ed722b4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7a6d2f61fe877e58d0a901cd45e1db932667f219bacaa889acad81cae62184b6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x749ddfea608490f611fd55258758d1154e2eb409904bbc2d7d3efd3516856250") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5c19dc724811e334aa1025b65ddce434d93467923532affd8c46753b0beebeb4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xebf99eac63a79fcb84af55e9deaf2351cdad9fdf571c308fbd62f99fad92ad1f") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x43a85da31bf219f9b0d025829df9d0dc46f62ef3e5310ad9bc98c897df8ffeb5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xdcc5e8435cb8eccba8fdb9610cb390ff23d02001be7ccce617035f8c17b5f4df") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x12a18c01b91a40b596db4432d2d97a6c586e5076eabfb7ea6a16fe1bd06fb44a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf4385d0f06df8af90b9eea57927e25d5178d292915d87ad8d9f8e6202bdbc09c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfbc1718ad2b5f039ee8cb08b3a5edb528039cee7909b08f5e592ed29767aef2a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa804e385e98a3d3de237ed29757137d5c1d8bfac07588560c653551aef9f5bbe") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf843a5ab0271baa253936c2136619ba2ed30c8e74772094595172f19fbb82bc5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x24d4144bdc89e6d0e970278e2523177804d9408fca79c71959b1d75d0846df07") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0f6018efb98dd1d3543f33338960b6c39f12ab9c258513e52324e8d4e4edd294") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x66d13454f5c522cd9206f819711263535f04ebc006a25a591fc240314222b939") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1ea198b291f718b0570241c963788a3de027e732a9840c052e2d77cd2e73d9b8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x225d4587c7925188a8678281cdc0d5de1f28611bf2b25eb708e951870f63b4f3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4b3171acda452dc62a4c0e099ff14c1f86e433bc23c1bac0f460ecd830d57fb2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x064d061c86d9697381b0467f7a293679fc40bf439cd446f591e8e71b7ed6fabc") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x215cdfc54ea6626cccfd83bf76f7a16f3216c294eaf4f6eead455bd7e1c7befd") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1a28c86f4fd09c0ae97534b37de0e17174a4210bbdb691604080db043c208e7c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd51ce38da550946fb97ffc8c0eb1434fc43b18650f60b3f23951a086ea9a0a8b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9db427d875721a826eadda2bf64074e9119b09bf4aa304db4249fc959d68cbed") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb516d878b4a24dfe9874dc383dc217763e83e8de34df3e1ec195f2ce4978037b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6b6665d4f03c47b478ee55d6f2ce6224fff6f5ece55a5441135a1092ef0da000") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1fc09671df6227afa4a1901538dcd118c5c2d0525677ad9b84c9a14b664c4f2b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xde6e409dcccec0737aabdc97a1fe63a48b395f58daa4228fb0bb38f359e12afe") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x68b24d82d0aa161cbbb55b92dbbe3adc371866f6d855ea5aa55cd2d5e9bc7ed0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x74b2799ee67247cb5a7bf857c48896492db716ef804fad961dcb907e95908353") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb500122f339b0882239f53b32951d518235c563710a552eed68c005c9f412d39") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x79b968195a2c6fc45ba8eb313a1925b78997ff982ad87e3eef10c7d15fd02383") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4186bd9e8f7194e8d4a58ed54ca23e059de9798a188c2abc92827cebeb04d09b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x11bb798d95d17aa6b61144801a947d7df53ffe117be008a2bd85f0af4116f09a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc9aefa41376c56139b7b71a88767b498e8d326608215c72bd3388d2a48b04419") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd9f99aead61d012dd77a6550469ff0da5c30ee91edf41f62a7d78f6d9b8bbbb2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd7b0001587c0a545ca649622c21be815679fbb00e858e5e1dac20bacf68fe752") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3c6f0e22f57b0ffb03ba5f8b41b7614fb29230d2526799d9247b89c2b3af370c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb125429b97354a56c70bc3bfef2a15e4559b17a0e24cc7c1c02f68def3f07b0d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x35318ce873e921449ec2b017eaaabff87fa3e59afc088917ccab0a4d7328f9a0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd730a810e8c5b873c3563f20c6cdfa73e534ff55893267f0375ebbfd0210922f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa6bc77315e3bbe25707d2cb3b6576627cfa9d01952a9d7352aa19be1ae817980") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x40ce4819345fd0ac2a247553b6366d5c62bd37a34a3b728d00f47b2f7ea49b37") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcdb655b76bcd20896919db3024f61d37385f745f4cd6e7faf242ecb27675351c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9a27fbede83f8eb7a52aad0c505f90f90f53f8170ac45bb0f06e9687cc84df5e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7e2f30e263011e43169f12a27ed012f9824a3e3b847ee0cb8a2c91f36004745c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfe77867292a7a647336141ed2baa74d8a47d8717c2c842353eda2b4a2acf6390") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf0ad543e381bfc05d70af806c2ddb24d90031527a906476e63907c7de7bf9c83") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0a86728018de3a30fa4ba165d7871f26f40b86204b12d420a158d3eb90157fba") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe9a38a499b6f2c5c5dbc83cf931e70d4abc4469dd359365a3b068da2dd3ad344") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4563fb47a44478be8b6ea0ccdfdf9aa1443fd4079e4a4eea286eb5d292171feb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xac3ea62972a9daa93dbb18b4f4ba9bbef2f11487f4116ef6329b9088b8dc9c69") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x687030af7c970eba78d57d7e9507e02f88ac1d021c2e740956e0500e2a2bd237") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x64e8541fd0a38410b8aeb496123087fbc158d8f2f84080f1a05b803ff332a031") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3e6ec75c9d278cb28fff04a807f35e68278b3ea483a63fcfc7f3b2238d7d0b4e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1fb1977f17de69a03272760d821bf3d5a069577793e36deebbb580d3bca6164c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x177af9140796f2b6405b45dd05d9d1ff9ee0811406b112767886933ad84473da") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x646276b6e3a5ea90542440b6fe51dc89131f7f3ad219f8516edea6f03fbd1013") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdc4bcb8e75aca61c890643efce61db9f21b058400b61173dbeb3fab43f5ece88") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x58c2c7c32f1c22cd2d301f9f46ea85a7d547afcc800fc4825bf8c7a125fb7755") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2ff77d87cfd8365512ecca6e50413ab8e13b8850ba97de6f069a4f23c7b8ccd2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x47ee08cc8e5a23976f3b4b804f1c2df7a32b8b996b5c01b865516eb1d69e2da5") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xce1def817bd89c0e2baeebc3273d9266236a566965813583d548f624e8a625bc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6d9268b4cdd09c67a646badbb80217e4d348b852faa8d5dabaead5658c992249") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb60fa0ee43577c5b70ed870b009075aad8099bc68c2df0894a2c1224a2fdc417") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc832baea86d00e8838ba03793d1e2e922facdbe42f19ae9bbef00a230956c2da") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x427f9c3540dbbd9a412dd68e214fc51da66b70c5ce440074c08d57db40c812f0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb1e8aeb06ba976a2b4dd09fa419b9f771f76e07e2029aa29dd86adbb521f9bac") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdab1aacbe5a7a85f265263217a5a7ed01632efc3e4065147be87dcbd7f96091d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb51b79a7e48a2f34cb266d80168ffdca988d2a45a4caae6909fc6123f37cf65f") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7885ee28b236cba2b18bb420dd4323b1dc0a930f96117d380003c3096c44ef2c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaf2e99cd9808181dc25c5c5afda86662c0d71a7fc3bb2839f1a4a65b5cf7c926") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa8ef215ebd0710598c42ff643398288b19e5ae3f9362f08983b9b9eabb631dc2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xed410ef7f76fcc8719b1ad1f55d974cf1c44915629624e25201706882616934b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8d4549abdb0d9f4dd4d60688ec994dc11d7d7c8813bd16a8b9a208a9b0f21291") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x51a12814215ab1d7f2b7b74394fc7b8001f846033fc69d9f8e08b2d8a5adcd9e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5e4d7b0169ab046fce17034b97c5f8231184c2dfb3ac70d11e97a31043a0d7b3") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfe1833566ac24988566dc35327c61170efbe7831434039029bd37e2fc2934cad") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6f8148b759bdfeda3b5dcc7b411fcb381daebfc34241d87b3274ddcce5906c29") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x687a2ff39b9da4cdfdf93e8573f718b5969fe3a4efbd2c0c3915b3471ae66ecd") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xee024eb708d7d9b75fc1caaf3e1588851181aae4f664b7ce9fb8a20d652a58cb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x52b77860e75ca73ee6663504f0c9042aac9a3c4234cc832443a2c03f480e6114") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x02563ba45717908cf3b4c63e4e524e3e6105de016b5da647424e5effcc8d27ce") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8aeb010eb65a822529560f37f0a3d6e1c2f75afda61bd0e44bda7e1effdbae95") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4fccfc73c1ff0bb36f21360074a4af9906e2a1a52f3ae5472f49976e20dd5c50") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x76741b0b84743b0c06e9fcd8bae7f4d1bcef05c34eff2b2933f0d6689247ffb8") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0da9ece48ba6a83e606a93d1384cca76d9abc7797bd60420871e7981e3850be7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x88e54a1bead9f4e4135a3da9bdcb068d6c818cc1a4d05d0bd055e464c5dd0886") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb89aefe8cf05598d51e82080404b3ed647e6e43f5796a9a4af6fab2085611e76") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaa09b95a53616e2f0ce9a16a72749cd7e6e1d2aaf6b352e53f13cca0f2fad970") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xeeb0de766b26ca76d0df5e26c3f25bb0e4b5fc09d081c50396bde97430a768d3") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7a75ae9d455edd9925a35fa9dbc319a3cf41e49ffddb9baa5e0827a28b965226") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa20ff6c275096539fc532705c7c249bf37151bc45e732bc4fb678dcc1776f423") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6dcf1f150339529fbeba299596c259f8e38b017f3d768250b8d409eaeabafcd3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdd5a3b5ec28b8d7a9e48e2791597083ec2ab5dc1adb9975ed19125f255c02cf0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2ee5628ee8888e8494f6a9fb0e897b4fe5425c5b86f58a75ffc520bc4549ad5a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdcce76bfe97dc0559a69987aa33e8f6989f8888624bf513efa21d489ea957713") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x99d68e6db3ed7628d3b8cecaf208122053e38671b54a782e2f43eb3a731401d1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xaabe89761da0724e5b6cb26f34cb96531ec1b27dfee387aa393bcdb31e0af32f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb9b565c5562f88ca5723fcd3984d0f689dab20dad5fdd2fd35872a8a7c6b4632") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x70ac8dfd0e42432244b79a136276f3ec27b281ef2cd2af55cde672b900ff381a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2ce4b1e608fbcf4b6ef8118716172a1ed8f9fa3a0ea2c754d9fa9924803ce657") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdebe5ddeacb7b9934db39206065694ebb1acbcd551395945898c39fd9bc194ab") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x53f6e788d42d67e34c85f8658c9ee31f2c49b1d8a6f4d8e82c019047f81f0e58") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9b2e35c2a86c93bdcf8d32ff37f61e63aa016f59df1c391f92b10ee6d15ae4d9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x22ce96ecb25d0f31830b73994da4585d9ae06fae5f144bf3ba2888979158a729") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe87d045f9cf5b8e2d4a61ed9e42d5cf2a443aa4a02b0c96a460ed043d94bd8d8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6c58214e2c49abc99a80b09eb4b2b4701dc4822decb50d23d8a0484670d16818") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5569334b3c1bbbee75dabb422a7ab5f2c803c4e23642634dbf6fc849c0f08ff5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x06566574e54ca8cc0b4a5bde121e9550e668e4c86c6acaf051738871fbb73c53") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa52af8723bcd8c694db0b534901086fe58d091f61a8a5a758e46b7f56e08699e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa6f5f4575d62335220c302ab582b8e5d6e29419ede501c0bfeeccbcde3805bc9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x28d4d985959c41d59733088a0358dabc420a4d4b3c202781b171477dc3d6e68b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5417343977b105734257c340feb22ca914a9665ecdfec5d5a8da8baaf115d48d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x989f9815e3085749e5d1334f0f3c51baad6420a72d63c45dadd36ff04b76751c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7194514e00f808025fc1e9db2e390d7a3c9aeec647de9ace208e98861ca0da90") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x57d327e6c5aa8d4f5cf88619e5dea6d3366d69337fc264e1bab353b483129abc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x57cfe6ae164e86275d42380d0edd264725f028964c7745a5a01e033b08856538") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf24aa45eae39b4a15193a78662a3f936831a90b045d37777afb293945c5a7139") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x88fdad3021a27913461d156216fbb002e3acaec5ba42d9b3d9d04963b8fb43f8") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa7080143195c5527b5113515479862abd0f60cdd910613356ec367a72c16b901") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x07a05b010b86162ff6c94d083c56f50eaa9ca7b0869dce5fff3ba3ce1920a5a1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb3912f4401b1461cc1cdf1b87d66b7dc9c47d63f923429e85b859274c0e2c582") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x26c13e32af60a8c0700960574f13f9cc8933753d728f50b2eef7137a0d82619e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xaf08d383576eac2ce51808bd0b25a5cc71b842b5f94c009d6229ba4c596eba0c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf33884c3a116731faa54c6da0889819e17954970f27265dd61d9ac3d64f1acf2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9fa3452c7e7304ea2238ff06961a9d416e094edc398ec72b2586f555aabfeda9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8a10e8ee2b75f5dc83d4edd19a6470d00def898c4cb5a75cb4b9a5b85a94c7da") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb4148ddddb3bc6c601f2ed8986f69b5690ea8bea0d70b86ce8ebb4601047eeff") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x332d8db136ec8121d6d45768806772e87901120f556f4e5b49d63fa7a11ff21e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x548491080930a39f829cc829fecf5ae698816a023deab4bd43ca9c9918544234") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x72ad2be423f0166e42e1a328e5e24ce19ebc4d08e80e5cba4af0f65c8653e866") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8ec9b351833c128d59d589baa05824c32311390184ae236303e44912c92fc05a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x764f989cf90bfa0742d2abf61988e8a651dcec7ecae4a1f8b8513fee69b0c80a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3e9e49265d0b011b0ba3c67a2e3e2f14128a2ea72a1cff91ca6d45907a2324ff") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6f287c26b5af37dd6d777fac6ddc5081195c578d57c3d70e6315abf52ad3a28e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc7e6d7be1a54f8cead4b503c67cc3a4c9bd416821ba94a66961811df35bcdbd9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x180d474d5be2a25710bd5389d23fa92c808267c38487eb7e813c23955e4e9208") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa71c90eb831091d24d696827fb10878e89e238931497d4536fc43defc0ecc61d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x304e6bdb8139c7d01dee6848737bb3ec527fb9823e9bbcef7f1cb0186797374e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2e0db7c7928c8728cb56d23ea1bad3b07e6d9603d96a62ff5d21ae64fac7779b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x41d48aeb9468e830db34e49f70418221c5718611312aac3300b41a666dbab80d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1dd3391deded054bdcb8a45b9a33efbba3dde0781227fdf1dd3ec61f23fda37c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2d81c190a3e6fef67ac777dbab7e362d29b1417e07a776cc4a5ae90a06557932") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x49b7712a955b6075d73fd657024424c97367cd181de4115e2cb6c64d7543a9b9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7e029113afcf3bd80b8579048413c62cf2d210e5935ea3175429a71704a28030") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc630fb9190286cbf0ca1f3fc96c8b919fa5f865e0f59f8ba516b76bed80c6fb6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5534f91336c4e826395a80b63e19b3cb40659272968b9493deb86b931fb844fa") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0f11a8a139fa4cca38bdf7d137549e20a5f5bf68288faa714d19548b7c72b796") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3140da81c3438b8e07b7d0c5d04e16f5b66ab48be0621d15aeb50ae6254912a1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4effbc045a7737423e851e223d2836bcb3566d59f58988df4b004c2357430a9d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x75f038f72961f8551c6fccba5621064ad66b8cb03650646ef69cd16ac692d557") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xbce89ba275aaca183fbda7b6f30005f85449d88d7f91960abb300800c90dd577") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xec670dc11d4598160370ddf6899d504205d00ddc74251708d5136f10adff833e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x164c182ad58ece08b3b5266de1bf0afa05b18d9221531cde5e4081bb5d08153b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x4c305af9fcbe4e1c93f3bb2503f4fcfb4ccbc2ac5ddc150925bf7ad994f71aba") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb3bfd352194891bc15088603f1fee410e7c8fa8b2e93f7e6acf0a66dc95398cc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6c672e97dcb56863dcd5e011e3c4fe191d3a1f85a1c4da7e5871b2a5883a914b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc19c9a857fb4e07a6d3b1bb9a9400b46a7081d96e52907f9e82bb30293ab9d3a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9cf12f65cd9f480de6d99e04f7b6a2cd00657a32f7f98b49d9d735dc227b5ac0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7381cd442139d0f689c9d7d7a4662ef25305a092f09b7d68bcb9a7474a6b85e3") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf472640d3bb631af678616f49d46cf1435ade360a932eb16459e9b0db4cf6221") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd8e0726f9a3be62c20d9b5f6a92b9b4ec55ac3c1d14473827276452dc0711d99") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x952d82de03a513959af01fcb962305e234bfb0f7b688e2e950ac5a7b50599929") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x77eb647746cebec74d5defdb8b11e8349a0a67459c465af17e3ecbacd7a72a7f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcf37416ba4b921b04ab696b3ac6616f23007641890576c2e8afb34c06c1f0656") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x228c8feb1cc621a06838fc404af25f02e144b1a6fe5280f367e399bf3f330066") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa1a3edec77684724574bf3da8874a07bd6dcca692a04307762362b41eb6ec130") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4baa4e3b406da3419f7cc25159570acc723c01f5e7072083e7d87006931ca398") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x54fca45a9ae4385e469eceffaaed298c9444c5a3a632d402c894cbf842c8d672") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x95542ff3d71a870e6a8bb2c5fe10d244e3a4bd2a7d5592c5dcc04de45e9ba013") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb462fb92877f0ce7e60012293abeb649525986b7a98316318b908a7f0cd65da3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5e18ffab89c86ae11c40e6bcf11a8c51d6835a1de72234f05c5d632186607e12") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7021d0d71e902e6727d9b2e2a11b78934560aac765456badb006c5bea92d3d34") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x399c3db00ac703cd594820bacd9daf20b4154066da44f0c80cefb94d52e4a54d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8b55a0761d78e94f003a42feb2cf70d912066604c3e74dd2c3f881e6b31b899d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x86b2b369640729c5f4eb510d84166aeac3130eb0e1c303614bba1e9f334000d0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xba2d526d1f4c8c68cc21eb6910cae045da6f9d1a62d887c3724fc9899c76e7d0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5ea848e5e872b91fdb0f98d3a250cbf650b5d273f47a2cc1b47496043c94e30c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc2e6332ea432defba166c04bd5ca54afe2df38c204eb70b96e76e142889487d7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x87acba570de52421b60060b972d12b3a1c545376512635bda3f456c3fb59cb97") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa9e21200368463db944f55b8e11f47a9b4d783ecb7a8ed2856416742dda3ce66") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x09d37bffedf06c48c344ec0bffb9c0cf9d52e61e8cd5d6cce71c20fc52a2c79c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8e0ad26cfc21e095596533db2ace3758c036c8ac826930e0ab5fa01e1339e1f6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe746dafc2ec5be7f16c77ce66960a0d58556c67456ab2767fff455c0422a4cd0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7c8283736f5ea3f2194443f2b12cccebe959eaa5f7063cc9348d01deb1d61c01") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0ca6ccea941ab437807ab332ca04cd4f4ad0cc3cf9eb163cebe55db4aba0f0f1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa4f9670d0e234c154edd869a5cef935e0a56dcca3d9d6793b20381c7b129c065") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3cdc95fa94b6c53c641c774b56fe02c803faac3dc631b3318ae6ac43709b6378") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb5a6da94ad57fce650cacfc5a4b322fd24ab83fbf62a604bcaa9e4ba7578fd03") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc9fa7b1dc92fe70f1823b03bb8093f404c9daf2c5f085574487837ed08bb42ea") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x64e29389fc38c52e89ce62ac796f010e466c622b126459d307dadf8e785058e4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x960f94e3a2d1b6c31622bf8f2859a44cf0a79c7bd3b2a51a4b4e351e1bda23b2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x97ae285883611f0fd18fa37684f2eaee25bdd64285498025e5ac839d72dad7de") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x17bdeae8c9df374541104d81321dc34a6ed905b4834ce1d5cee35d2f75f95e81") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8ab49ca8e5660bc6eb55c4a006e4fc2f5ac88c68f74953a76e651c72aed70c82") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x43e3f9d43920a32200898b9551ed4a1b0281fd424f2c771576f4631fc8b3b250") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xceae98c85c944751750c677dc7fee2d22d6475ce660b306a7e9ca4658398c6cc") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2a595d26887c3e211f976083c9a220ea64d65af003858b157fe6ec22cf5f5e6b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf29b310869a8e0918524c207ba1441f8f080a07f9fbfcb21ed191e4c7d625187") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4a783e7e6c723b5fd9d78f03517a37a6cb95c186e6bce29f50fab5dd83ee7400") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5cbb9f6e7fb6b4cd251b9e9c5d637a86fb9b6d4b926687188af515708f820970") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe5817dcebcd605b158413eb3d53b0392d3119b42526a13784e85ea4189fbbb94") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x806b8da5960f26feca222148a03776ba2a3a5fad79d2707a059718b02cae4547") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xef902d681c248ff1ed1a94d8e6cdf70a9035799fd5dd1f1b3f22eeb35d4a6da0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x54aaeade93789e89b303544f54c6123e7a40a4dd54cba10ec69fc15aa5050476") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2d31fc7b81cca3802fda8bdacb8848262cabb945a48729a67fecb35a0245f459") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe09f1075ae272f1d3f0d50ead9b6635a4c2cc734e9a43a39814336791cfdd2e1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xded06434a29fa69bec696e94bea6e982713a4a100e51d014de4ad3c19147e9a2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1270975ddfc44962159cee88d3bd9c95061115dfbf1cc1a385b78a049170f40a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x91f4a98bd834a1abb0e318f578d1d3876df5ab4d91f3c6fa6776ba56f0c6d33a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x917ae3da693eeb3a33e96396b24e9ca64fc200ff1365851bf55b1d7c6d491680") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9c1f51776e0a4d9b7357db8e245e393460ebf7fc9aa41439d28baba79889c6f5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x43cfa9846c4d8f78dd4f5a5f244f826b0c34b829b8d752ec352a6d5ca9eef6e6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7016554c00ab1ff542f2b802f22557d2add1b2880f511b0debafd3194ebd0bc8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8fe2297af994671d1453be1e9a9fd0d114d7ebd350a35e47842a11d4c97430c7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8c3817569da386e605fa9219557b94582d5c095ea24734263c27f66e5b27102e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2c7b6c2ab778c8fcfc9980201a90b3e8110215abe25739e69f31b06f55af883a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb34fc4c798134b437016a1d5361dc8637c1f80ba4894925c09183afb9b8f6478") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9fd4cda33b36e162de3df6ecb5126fb3f4e16bcb3a40d806743be9e843f37c0e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xff1c91dbc64e1a689b512cae88963963505977b423911c14bce4d9b572582db6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xdd1a832125762b3b75415e120b3b19a9e840280b6a6e7611859f1faee7ff5ec2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x20295b4a24d76f3c775c0777c9377bc9a61f17751fe673d0027c94618ef8c19d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6e1c206d47cf30de37b5a2442cc43335144d17c35dc3026c24feff76c440a78c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x95b134c3477653cf85947647bbd9027a91a86faf863cbad105f696461a33a20f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa8b12832ba6679a92f5bc6553331637affa8631918cd32e45209ae59c1ebc6c2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x323ef6e31946b35b14f7bb11199a6b53b0b27e2bf89739c5862f2f012b37f0f1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x90c5ce6c5fc7ea39446a871bf96e943c68dad0373ef857e00935d748d04ec677") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x18fbbb22a9a8a3ef0e1ce37ef2fc5d4eb0b8c1378f79c57b096766c207b49aee") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9eb975864d4d3b858015c2f53e44e59193dba092cbf17a997ac413b8483c5cc1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x48aa3bd7231751eda519975b90d224c3207865c10f62772774726f5ac321f299") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfbfffba56ec9f6e49c8f4e4cc5412e52930795470a25ec18a5cf1db429fa0cf8") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7b1c1d97a58631a911ee87ad500aee705dd92317bdab5367f9a44c9424ecbfa6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x26932bb05f810ef9fd1fa1595fd43bde9b6f4afe1ea182c34d6a315127450670") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8109d902ded5a490c60c63395880e20a09f111b0ea5c78ba0c98a29490499693") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9c7134854684a45d3e4235807f9c26b436bd99ed23b03c128bdadbcb9543b9fc") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xda2c7b7faf15c6f2ca7d5fb7b6f5189edc243b13a63b01abb9397c53e2754574") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x338603c388e08985edbd3b1f289ceb3855da7005ce37c5e0aed9899bca67e6a9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf07e02c76b03d1544cec937622404547aa81af312223d5f063071b04185ac8ab") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8f58bd8c057673f0bbe7e59239b5c48949c43b7664800bf19916fa47125f25bc") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xae706306127523d20c1c3d89e2ab5818966bab94e8896512d7b67808ae94d71f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc425b1fc3392d9e4448d665f5508df4a5a1ebb8008da9ef769dc551b63b74fc1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe8241511a98299ed218cc546d1500022afdd77e9085418fbcfb638dbe7c57cff") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc1d0f4e917006623c89368d065236a1205983c078d08f199e924f81d3f298736") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc41a658950468b26ee56aee3e6fbf23574eaf323334fe1a4da7822e9d802d7d9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfe543b4a49422ba9d36514337bb94551e5df665da9bbb4425910e8b99cb44338") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd9fd1dbfaaf8111c52204f4d131e4fbeeac3534c6c7dd4df03db00e89a87bfc0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0b23aead662fd7cba680632ff238ebe47a8a10ec62455c9a7db82600ea08613f") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5d8f86ebfed68b41135fea70aee90cb4170531f2b2dc9d691d3b9a93a598bbb9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5fdbe29ff807ce88114b4d70ae6c646347b28856d1293a31a380c0a39ca8e259") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x273ca921de41548bc5164af7dfdb5f35d9c1283efb1068c99eeda4d8a9dcd4ff") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x98fef789c02c604e5a6ae541b47234034c1f23d8920a60b943e37e636df852de") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0ea0836d0ea434029c4ea7fed4dba8f6b7ae115937999ff61cb385cedf67dcae") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6f7286c995f8a6e8d54e4d198dac6049fcd78d1505f5825bb136ca5fffd50512") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5a510a5d3e4b2cad5b7f55180fb09a55438c26de25353317d6ac727beb4b105a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6a52400b6d27299445d6324896b50a4132c6e039b1c3f92ef6adb81d0a2be3dd") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1c575d62f6123c900739b85ff8980f9d555aa8175343c52c20203d316d950e29") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3148c0f02cdeb91f14eca43c2ef55854d81276a5fccb2fb0cfa79d43effb3253") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9e665271a196ea6c5056655971c8e24c95b0b2534eda5f0696bf5359306213d9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x04efe4f945bbc847bb2614bcdce4a1ff760094406d5725c05a8f1f3f3b7d953a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3ff804a505a9ce746ca95c48b7f7594d8e76b44cd0233fcd31e520407ceaf03d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x10ceaaf115cbe39f457840d0bc827a68513ef7b6dd31064dd71059a5cb9970a9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc9499e5b54d6382a135790cc1d5d85c2007f86f4136713980bfbb1ff0c48e3a7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x34f1003504cc942344cdf48907aceb34ded9b9d221458b45f8c180e13f81ef5b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa7a4cc997e7c898b1ede30b86ec696f033fe6d55abfac2651764fc2979ed8cd7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x824862d97082ba0684880b31de90878bb5a64b8a1a79f440dfe0104883acaaeb") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5b5c2009395a5ef26dafa6c69901a2162bf9da1624fff666df774ed19fd001ac") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1296362561a28cf961319dd144d8e93eec0dfee38e280a5ef357456e88573639") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6507ba49e04b780d6986f99aa7d33ec9c924b64d79b7f26dee219df4f47df803") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc427426640fb7784420aa4ebb636002fa5c552642dcec4d4f27a383e9c56db2e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7c7490d95a24ecf232e325fcb191b3cfeef6d68d55d914377ce2a2cde68a98c4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf7598e874e77afb5d8c6ede812a8f3d75d6a9afe118bd542572fc908d3319962") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd03d8090fa9a8be8a4a35af461b036e7564fa8fefcf7e4c8aeaf022faa3cd278") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x25432772e8d5ee1f250996821a748f75a0738e9be2570d3956ff1449c41a5a73") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x16cae46b879fe3268e61a6adaff6d8ad9eebc023eb265dc62a55802363f7f630") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9d506e93f3dbcfd20f48accc3b4c34e3eac810df0eaf4503b6dc8566b9e242d5") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4b85d59aca7cb9131836878508c00d093a86a43fbc47492dccb8a9e13d15ad4c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2f1037cfb95e0b3d40937d583f1efb1f23ee98b32ecb704aafaa06e9e0f11d9e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6e73841e23187865d7a7c203e7fa630c1309799e1a6f094aed6e77947ed60d1e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x698ec95c9014ded699a57363dfe36d5df00893ae0604b41cf36ed065c58c3825") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb2a43aabf479e725139c7a35db8e5c7ad83ae3eb1deee2d16501879cb90c4802") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3b1d62683b6ef11d7f75340462b8bf8bc37cbf6958cbd616270381c608d4190e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe4be56ab2fb7fc95e8ab0db5ef76d6b6e1de28ce3409cf2c48fa7b834fa755b7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf57198039225950201d9caf38020c00b97335b2ecedca8ee248107d509f4638c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf26168c4706e0a15a51ea5a34d39af3ed57179cc0f34cceb14675d6ddae33588") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd9f748c37da4c052eb6927513b6fe4019e38581f80268d79dc7703ed6323663f") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5f9fc82ad3563a432b4feca8b31545d7f63649ab5ea466ff167c461fdd2f9610") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7fba7e99a9117e2263f531464b2618fea9e11a89d5bf1e99d188dd00b55e879b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa3d1a325df413298d2648a51aa0f150edc642ac2637edcc5d31582a0a11172ff") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcc928f3596db7774cfc95d6b4073c8c29d02e1b359d199eaf9c95545026ba4a7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x46cac32ed6f4bee7c9ddd1e123f9aa6c7487bb558ffbe281b0b6e9a5afe3744e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x271a448c1775a36c2da895a00a4111ba2212f2bb04bffbed77c7598f112fedc2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x357ce5f68ffde480612fd7f1e0048b1249b645758398ffa35c9cb023e6136cf0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x697f7705b21384daa3e8360049e0007801d95591d3b6dad8b26c7379b950fa68") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x08e033b7891a1a0aa1101d55c7d8bf9c2d345ad6c28bb37fbe945036f09387ba") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcb0fbff02ff17d6174ab7d71e9487dbd4eaf86e45c51415fb6eb7267f1503585") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x82a6b9445590707ee6be5ab6bc390163c1ac9ba150954b39ca0fe8009c5f3995") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb3ae6a2017ffe93be41c480da2e829dc7f8d46e121367af60a2b3a4ce9fcee56") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd182f015e1c3b19e170e8109dd99c5e7a0015adb512220041970d6d21dac22bb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x680c8ed820530b85d2329bf78a5c4e2df84e4e3d1ff6063f22cd9a19f0049a3c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x74256f0ac95b1b405e8d9a37273c9997c3015a48ed10ad2db6883211fdae4bed") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf7c78e4d33ad6d20745774966d478510ad5fd9410a80791d3505361b6e517fb7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x07eb86f88b28bd0bf678a85dbe91bee43989589c7069624d17f2890308d053bb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1cf005366664061db72061c4c37ccbfbe8d623bd7077cfec4ef8a024d8d2eeed") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x395845f9007d5b0761fcb7225291e45a4475499d401ed8f62c873ce50e8c7e31") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfb7d3bc2cd8c21713f2600a2d4d14aa0cf7fd0bfef40eebb5036786cb5543c79") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2a67e53098d0360382a5b08470a47e0e1bc3f049af90102bb0f2eba2e88879b7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe0ab3c24e55b1f1cf6aaf40e848cf1b0c89be25073b38bcbeb0b79fad1da793b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xafcb342a87bfe0f372620058c7885bf39ee701f74f5ca513e31deb9fbd38601b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3e44e22507d98d3eea22de63d11d0d09d5517676c1d47cedb63d8f5baede9700") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6b1808d631281b8db8d5e762f5e60f4bf56f6ce2dc1a6ad75387f9c8840fefea") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xdf2c488776718f7eadfff739a303c1cb6cb5e7884c9a2b2c58ffe1009f93b97e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0a31c4be3144eabe6cefa0b8c8b48064a66f954b7be8c3410107965428fc86bf") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x4736a2ad126712703a40bab29df980ae0da5249071ec9f411fd492a67b83b030") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xec5274cf6a6b20109aad278e3639f6722d7fcbc8ccd6d31f70038dcf77e2fe37") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9a7da50b27fc3935fc863634abe58a7d9c0434b82aa43ceeb17f147d8d21829c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5b11fcd1b573326048d6547953bf78485e7d9d5ee50cb8c39cf0f54e4d34eba0") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1991903e7002699419322ea2a07d2aeeaed718511afe7114122cc47378c30d33") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb7a91c58fcc295fe684c3457cda150dbda96e67595159b7b44615e858155ca6e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1feb3e6d946a899b596a987802b1ca5fb6a47015a45f27aca039de47b5dce120") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdb920b7f8a410c4e5f10058c8b199af15acdcc079f04d61047b28a34c5a9892b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x884c5759dc367d13b64f8af076788b47e1bb723f2af8c6a429ba8d336e27f2c0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0d1c939ad0f409a2a9a05b65ac139b53f83edd2ddca8074e4a27605301ab7209") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x4df179d1f41d886c68a2a25119cd992efc6620bae5dee117e893f6aecb17c78a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x724f2ecd150008f7ea41d559994628fe3ad1651d94e37ca11ec5232584dab2b4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x423873b09f5ed3350b064c590d465cd4c9b89a36f5812af384c3c3f5119babf4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x73b2dc73684d90731facbffc6bc0f11a31e9a9bb8c43f6877dd145a97e04c05a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x51c215595b2d677c8813465a18a948260d2bfa6777aaf5920ccb0f455fe234bd") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5f5714c13bd5b2d8af8d2971858ca0d27b222df19718a9d9ff287714b7a99463") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe016af0e1d760e264af8122ea5b4440534309ea4f3a017f1b1b2fe0ef2c24c4e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x47011c296fc5abcb82f3f11061fd89d2f24f81afa491817e0ea984a392b2d19e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaaa5d9508a3abe7a15940689c968dbf0f7f94f3b631626cd927588b2f15ee978") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc5bbf8dd243f1ee41d464bffcfc1d1c5cce491b486c1c61834f523a3249e8a4a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb36eb72b9084176aa24fd90b18ce3c33eb68a72bd64af25575ebcef379416509") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x92d9661e5a09dd563d6a4b62ba23a8fe2f279e0c17ffde5ecbd8d0af826aef86") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x04c0f57ffd52752ce6b507106cb5b7af1d6cf53a570837b3f59968de881acb27") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4c51d341862f9fa87f0660855a76d8d35011b7c0713ff8ceb79d6439962d4a7b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x419fda36e069538a9e13b952ae29028d374d0156cd601ce812581a77738b455d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa7fcb5226c67dca0a3e3c0b99af18ea082b3d1f28533aeb1690b693f061929be") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc74c7321fdf7e92c32ef0bcca1229eaa24267901ae7ab7851cbaf6b5af596028") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x829e99096c4c565c2124e1ea5e3593d7c4fa12a17508ff069a6dd847c437e9f4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x786d3745ee523138fbb13dadddf33cb287c98a3c827a7a0c1c6f1340e0a3ca9d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd2191d0305a1c9601bb3811b5c7ca1b1782baecc4e8c6179a82a36cbe6d63f24") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x23eebd2d96364a08964f0b596b19cb4df057f25f22beeaa3dd7ef4a3676221bc") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe0fb78bce829d73b3f4d8813c0cc5ca1da62471463afa3a3da7be65ed54b2318") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x49f46c05628b38f211fd704b0b1290fdc03ed8faa104db0deac06fe4948d7f49") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2c148a087dbb80a9a1647ae44521f4cb6786066cbebb510a540590537aa373e2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x4508855856adc3d05943cc8f9e2e87fc59aa0c635d4e4febcd986a8df12e60d2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc02eaf879ac42136a425aba06454032fc8500ef0a4410a708022f2cfe858b2ba") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb1f476835caac59be92452d7ce70f329529902d0e8621414a6923cbc670711e9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4bded654093f2c0c04c3dbf4c7c8b63e7827186f64afc5b110246917d7ae31ca") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6b3106d9a4cf02f73049b96e89b6b5de5e12970ecee64f562dd9302db222a808") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6caeb489e55a4ba7c98c87b44cb1c550fd67622953a6f0d8ac66dca22371640f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2ce0ff149e2d44cd28189144ae76e74f3b4b65c241f18dd61d1d30c60e36bfb7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6db6e7b17bb3c52f5ebd0427db9306b467ec1cefed08750875495607d70e5523") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc6bdea91b78bb0a74a3130de36779e62d06a9a99455799e3efa3f7464c5152b3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc2cdfd5dcaf0d3df3a9785f59a393d200e35fe67fe57766fe4c49033f3c308cc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb28ee0e0645c985af64c8b7167272920b6e206b2ddcea38e3486f5c4dab00e7c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdc39b0474ded75f745dac38328b6ab9e69041c6442bd2bee33f17075514995e3") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2cc757ea0f83d86b9d65b8c4497d85f357ee9020484f8f8b31655d25e58da1c6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x345e8f6c2f5d03a0cb9146f914089b6743542e961c348ba610acff85fac8a8b5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaf75a75ca51b25e0a625409742f1e60968aa30334002adaef54ba80cedf8f8a0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2a5073707f23a138d50de42b7439b398b49892598f512570236c8d98ca23c496") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc7c81d169f03bd9786b2469d35089cb951b4c5cee6614acbdd7ee0692a572848") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe62b7b3fd082b8a1a15cb5edfa0eb36d0ee55c2271fec72c12dde208e9fbe960") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0db03a9bd0914a33a48e599f3cabb2fe4c98a066cd5689b9d807240febbe006d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xaa2e54b033052eb72d1a77f052438474ebbc3dcac2f7343b389bf1672a1b4a7e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x95fd243029487ae05e56c58f969adc2bcf86c3af752956f263d3da7b25b6c685") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x738b2ec5a273c21e342fdb2ef9f0ab261c5cf2f71a2a001674b081c95c6a6bea") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xbb11d0a39834e9aba891816caea0a960e3f54a804ab0e6441a521b06165130a4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x11623a7b4b0c0b1ffa6ff009f1bc1e41fdf4e8194f5adffe3faf9ffb816888c1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x77502f6f35ec9ccf85e9a8b819d39d696923a5479e6626f2ef5f9568fc8e897d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc697d2c68af0d9d042df0112712a8dd5354a8c2543c433540af8ad645436411e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0126ddb7ea4a22923b1d1e2dbf558b8407c9c3168350996fa7819fd2cdb18760") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x79263cbe0ed0618f7d4649fcec0ef490a0044aa5bc69d53f465217dee5c13310") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf4bccd822ad591326561e1c0c6c02ba135fbdddd935a32182cfae9990a54fb83") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe082f9578b1c6ae4e635e072c8fe263e517376c852e1c8bea3db8463369aeaa8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa3e7e2b4b51aef34887d7a92e49ca59e5f3185226dad53bf39415df53e8b2d81") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x17d9967b079227c23dc54772d638ee125d3be5c8c3b9bb3b85f88ea957e27183") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0d71c56080983b98cd12dc428add7c3f14dc849eddc83875dad7489f7f5fcdbf") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x00bb47d7075259d5eeff23fe0c880df5610e2e2e7c6028d96862e80563c2dff9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xee33236f4f38b83c8e23e65612419416ff7a846b381d05ace1d51bccc8ce9005") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xedc70b29630154fa12528d6b0a2897976397c21cc8e8b15d80da609ca7a9b64f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x10bd03bfb877af15405ad277cea2341fb6982c46b1da642ec4f459e9c7ab1641") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9685028dd4f22474468200530bcea5833233cf4f435ee1fcf066d52d8c528b06") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaad201b313a1d21667b2b7e56b626bbaadefab65b8520906f4477dfb665f7186") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x33220a3a2d075995cc49b6350b950e9573f94151d72896941d93807929da6e7f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x37bf059efaaef71c5be591b36b4237ad2f9283728bce45d51016bd347009d293") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0a0de08c89be9e582146ac223188fc27158981c8358fdd38c71881791c42d57e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xbd21620861a89ade58ae087a9d3c299fe21ab79b8a308b965f142453a04abbc2") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x4182ef542dcf581b02440df72f8b3ce3d7b04928213624476952722014ce52ea") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xee9335362e0e59c58758f76f870fcd6d4039fb6320f988c848be11e39c7a5432") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa6aabbf02c8e971c04ce1de9797da8138b534e702b71fa38341104b8efec974c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe211f319a31d9930979b4a613499b7375184ef76fa2e9b857f15f02d2fa71af7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x40c3e599160387808877ad61bdf1e43741592883ecf5b4e04f4ae001b3ccf301") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0eb613ec0f150129bd71b7435a0cf88c56d7e009c74e7150dbf95f1763818560") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfe9b40d1c294c1747beb1b17d6f5e9baf2339f13412d267a0e9df934c5c665e1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x14baac23e4f0aa4f6d5aa982d9899f99d068073519638dca785b79adb13250f4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x81e56f0d97e1506288fb6942654e3739ffda5b9f44f93efe7377a247001bb85b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf819e79b2cf9c52fe5884118e942ec2e59bb80565242da15a2975df413079192") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5cfbd087c7af79edf3904c377ad2efc8cb17246de69e24a1503f3830184dba0c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x991746472868074369f56cc4c28ff8d30c223d4c4e17eec5fac4e66fcfa047ca") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xacb65c99d0953c9654ca1c08982e6040cea2b2b74505f0a231fdc4d342c70d16") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x41ddc68eaf1c9cb8e7293a04b3304a0e4be602662523bd8a7df6b0edb4db31b4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb984e86020cc01e0e062b2ee578f1096e82f606d5dd2beb31a7186e6e1aff2c1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6e401ccfdfc226f2964aea5898ae36af01cd25b95ea14b3a22f466c520ed3673") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5e639610281b1c980865fa7045411c6f9ac5d6ce39c99357351679d3d6dc64cc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc39489d2d45388eb8d68a428f3091fcb07df2c720fc9f325de19ce68f3b25051") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2ef7b137937d6e372f0814bed84f329bc4357735f672c8480feb62bfc6b1edb8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9819265af958204376502cdab0f0de0324781124c1fd38b3a03dbfc3641f1d81") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xaedad9a9020d269cb7f4d71586718654489b5f4eb257011c9753b40ce9810c9b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5772049e93ba567147c355f627b644d3bafe5890f05abab372d1da09c858530e") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd13fff04eb28cc00e4295b26d3c90e5280a461ded73e037f6c1ea9af3a1aba67") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd281bf0d399f908ed8758d8973f59d8a4ca0de5ea305e959e183bf60128a0d44") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x299d0de3cf436a57868845d83a7bf824e32f88ea3cb9f03ecbd71e18e85d75a5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x60b2a5fae08de55a0aed67e6b3c35830e40b12496b03fe6f7c3a0229e127ffb4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7fdca8ab1fc62074d581faa68d74c4fd30f72fec296b01d66237e9e3c2ee9a51") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6b834da17d69e7f2618c63b2990b684daad05f52accf840ab9992d02b9ce5125") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc253c67a6f6b06ebce10dac28f839583f7059f391f7abf4b0415ddd10c1eece4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x814d580e1d4ad2e37fd0b48cfcf190742029d6db2778ff5b9350ec3bac94b3f4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x164be9b17fbcf4ff6a605073a2ae0a91a889b88065ddec85bd4e4113e6ec8ace") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x594e81c038e8cf22af61872f3dc8f66326502bf02cbf250a20a20975df16602a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x39da7cd57c02c2bb5198a7e6a43211053bc41e6f72cf0bfde8841196806a242c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x04f9e40f0dca4e4dc72d05eeb494d68c36ff8a6d60be12beef3d8147b25a4565") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5da1924830cfa6a8c2f4904b1821d8b529ffb9d03098e7b946e6e9a44dad29f5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd7f8bb4f84dc112592c0cb356392a0c5b5dfdf774bebb7f7376ecf898adcfece") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2cc4d05da6afc1e78f92798c70e5ba61b20c77e5c21f9bafb4d768026459f54d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x34bb970153cf19046a4738f503d95d4479fa5ac2b23b281b84d560f08eafaa5c") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8c3c2f43146e140557bd78beb6d0577e8f19514fe2bd15908dc209b6afd93d4d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf9c5009b6a78d8ba91246453d656f6cb51e23c2fc19094d33b31dae085283cc7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6bfea9a563df00b503085765f0bd5d24235c875f15157df06769fa3e84e2f3e6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcb06d56dfd17aa06b6e4ca84b03d96b8bb3e988aae236380c66027f497546a88") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa8c7d8908d49ddc1d62c4ff1ed6c2cc7c5c9a766fde2505c6bfc5e71f785740e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x63e2e30e6a88e644b3e7a57967acacc1f68cf162f784c146d2c4a2dbb5d8d3b5") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfb3100e2c52ce50b5d95347f81a943790fe1b103773fbc819252eec16dabd699") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x65dc15934ecf35639915d5a039067eb14df2acc16052b3bae0648565ff6419e5") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb26cc696d1fcd53501eb6ab2e32917021fe895852a7d583af4f9d67c55d6f7c1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9265b66e5f9def2a03e5d9367dbd85e3078f0ed4adb8f4d530aa6f076f7f37ef") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe8aa32a80564c276c99e81cad6fe870fc30c0d7c1ecba8a5b5c36847605a54c2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc2e707b7f6b71fda584dc3b815c9a812499570dd19723cf47b9aa044ca9389b7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1f4d578c9af85ae12b2175673a1c5ebab23b6b098afd7cf6cc29348de5496f57") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x339f038cf07ba5c7cc9bc66308c4490317210da319794a016720959bbe400c79") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe9303e0ee3533de4b93b609e2a8e270f845456023446284f2d60ae6f6c85bcb4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x3395c152e4d226a1b279d156358efc7f61735df53b3ceb94ab807186e92ca900") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9ee2698fd881000a1a73e816d7fa936c122bd17534bbd0bf17b987ee43024c4f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xba6a665e1f70b7142b58803926aef9fef4a2c3e34a12882a676d4ac0692db6fb") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x771e241e92ea7c4626672021e2b4c139b413da203df629aecbbb3b120939622e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6d6c3b0c46fcc6e15f871c9c89a43ed62c81e30f3a728822b7544dca1ea3f7f7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9dd86253d4705ad916ae429d4bb46d2afd22bdbeb71bf000b1a30ecca926ca95") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x234c960bdfd90085599a99c217f4158c8ae3a11292eca0369d304402d7553ba9") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf6e5f5f130b64620f7436d5084a587091349751c3299c6e2eff5c4d00bf5b991") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1910673cdb904acadf927750e0b11bc224d5f311f443bb7062ed3e9c04558be6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x22c34c8c052fa71314a330c802875255919f067259e3ae1f84e5cc769f96be34") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x578d47b50416747e330903ee3d467249f3b306af5265f3b261aeaf46fd96571b") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x287507902ec4ef90ea51bf2bade4d7eb4452e55e1ed405952b15a202248bcb5b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe881342f0f6b35ce83edbe39c48d943976a1a021567bc099d64f1c94396fbb20") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9b689db73aa3757ee240dab7cc885ee3fde7dd17bc63663fc066cf54008c2d05") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x099d06912912f24fafdf177a964708d82489dd71d051e28a7dfc124b51e943db") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe310d803fece90e8357f029c8b70fb786a1281e921a7f86a03f5f63e353d3495") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5c5504367154665cd225dc2f40bf1c3bf74b2e9135860fd9f203ab95cb2f1bd7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x995028ae21bd2ae35ac40aa4fe5d18cdde1aeb3d04aaf2aa242077787cafa2d3") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6f40ac82a40030137a628cf8abf7094bf073771d561dac34226d1eff8283058d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1de356b002248f374698c4725c5f4606cd02b55624daa6cf0f6359021f8771a7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe0dc79fa3991763a038b4375cd4202f8e20b2038f5817aea7cd2110c95f17047") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdea838a11302f6e6d58e943200cb8bb20dfffe61171c8e1202ef47de89c504f2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xfdbc6b8aa4c87d99b95338b71af7b6e1b7bc7738012f1d2614b2e08e98251d54") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x21a3cb1ae372bfd110938d399e2db128d630770e023d8c011557d2eacd7a4afb") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe58b9cc6f767789c8b685475c8f0609424a3ef8cfcb9d2eaa3602d3eec173800") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x78aa74b4113f7ab620eb63b4946ae6285117dd24b2484d2452d31e83087a0b59") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x14ec86a8dd6914dc917863e7210c84c53ba5061d189358c6f7e510a99b761ee1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x340a68320e56a9ccea3d4e00db0bb09568789f18c9e06bba1028585a5c448f1a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x37f6e9cf2889cea698d613df5aaffe7fe96d2cbb103133e89f59512a067b95ff") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xbf0a8d48e4265f321a2799412eb16e354db8001148863cf92dd0580e46582e3a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7712d587c7efc0c13c51f89fac9fc2be405dc4337f878f7309a053e6b782a715") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x9067f7515c1e7eaa366af0fff8b42d56780915054a647eb8e41b22806e808fdc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x60fd52a4139b7add04f8c7ae8fd21c096ea25abe46a0dcca6d5447b2af9cd218") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5cc0149452c390f0ed6ccd4dcc2b87420d3f86dcef078433bdd79c62089b4f03") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcde6bc0ae3799515c168f5ed458c8e1115e6b389c16a390d4176d1fa0b24f08d") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3c432737aa80b4757ca060a93e9580244c2dcba4872bb451a64723bf96f609f1") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9458145720fc87386d5c34e2cb92ff921e79d041958624505e696e2e91ab90ec") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x234440fa8a486cf148a4a1b1e730f6593ba6fbd10d73e954841e02569d36d930") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9388a1a2d6ff91145c08ac09c03fa0b3d7124e33897bdd854ed5bdc402651ed3") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x835a3787b509dceec819bc37751f15feea87b8f015b36cede70a87153793f4b6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xe402879519f353279fe57feb3e55071923617ff79f3886e27db6ec329c646440") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2f557545c7f9b6f4bbc6c9d069c7b524c294b2469ac5d66aa9aa3f0941eb70df") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6e799e5a5705308d256037d803d3c70a416815cf9f7b76f83a9f975b10e69165") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3e070e01a750c748a90636e53d7d3e5a7c6ac2fb4ab5b8634fca6a1cd6f304cf") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcac6f0044258cb64e668e3b6623229095ed71d789d7b947b780bd6b7ddc84b7f") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x09ddadf9fec9e2c88695445791898fcd623ed245f5478ee567059e448f9e750c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaa9588493460893745e924ea977cad1bfc73485b35d8f0be30286c6547be0164") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xd0dd12b9b16836ced0eff0d2b4fcc7fccc6e5bac93fc697ac5efe6c5da66de4e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7a590bd36cdc026bc7e5866515439ce066aad5df130a2f0ee15001d904c7b0c1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x8e6f2eb1b8ff12728ea4ceef398a32abc531e957473941be69bc86299bc56448") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xebd15f5c309f94a4927c6f2c3703e3a6e3f2e353fe7e8d5d5b6948a5446e7c37") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x15c028d2e3f6b4880e6d114f6e94cf3bd9da82dba25dd5184bc02abe0c11a2cc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc8061270004e81ac2670f98a9a62cf0bd337318860169f76a9492ba17948d313") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1605f5105d7dbf448c0b506da6eeda83b72cdfe4ee4858cae45f5408670e30a8") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x340db79e9e9aa3bf83ff60bfaaa2771a00af8bc22d1e1bff503656792aabc489") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x987fdfb61eca9d6986f3c365a72e3ea0987acf5f95f7e1471f3fdd792952de5b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x2e36b9b8426cd75f567a5485e30827b043bdbab57799daf73e3a150ea9281cde") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2a1b899401189e2da04155f3e538b92f3d570bf214b5b26da0a245d86a1d2671") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x823d26e19d74f269a8c7ba76ecc2916d9e4b5770d15b84946f8f94a12373ea73") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x3c7071c2f91f47fb6fdde57bdc83b45f106b9f7214089da1584c41a0ed055c2d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x0fc3083866ca07fa6474b84c265f565bb75b4136c8e7215cc517c8684b80a78a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf04f66f0ecad58474ce377c8f248fa51a04c63bb8c11bb56e5ec3a1b3051855b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x59a829d754cc1eee56117e31e50cfeabdd63907ba39f834a078e28a9350234e0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x121f4a034af4d834b765e9ffd289353afefc8ed7280f5b1b0e81126b85a8baaf") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x198c11dcf5ef3af2b176f5b51cb1c09dbe046f9ee20576f413c9a527e05c2d01") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa38ea713e82830f67d819c78113d629be4570966808b8d0b3d6606bc42d1f1c4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x6a505f258804a1e698527cf2c7356fb69fa5e496d05c79b0347e63d993fbd8e0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdaf837c75fb2ca1c01e9a70ad8d8a00f976d145f7c4f618aedf2b37a2acf1e61") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xb7441b84dcfd31a9942275e36011dbdb5a18e571904894da9e8529b21523d294") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x80be68899c1ff07b0b05a9735e371bfb959146190ee9e9774d10cce1a2c9cbe7") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x30aace33c06a01d3a7f1afe5219ac0ca50db69523228a1d3c726a1c81b39cfe0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xf6e191db380dd7b84d9fef3970f0033bd4b1a16d985c3551997d7b21efb49d99") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc13bb729d8f9e64c87fd72a5160ab1a3fa847883d445c41c2fcbd26e0e94df80") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xdd6b6fb6b5736b361e8f321efe7d54ba6c379d7b3ff6b0f2b14f5bd04cbfcce6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1bfcfcc63367122a118d8937e76a4e1821379db4bb6b35fd2bdafbdc01a8f9b6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x50fa60d961e0ceb7468ef0744951dd2b3c90cdddc48b9b4a9e1e0cc5d55ba987") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xc9a8b3698df0148c7a2ca5d2767c0bf3080818dedcae47a9b058b25330791cac") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc3064a4f39d77b6345dc30a5a91c4807fec18cf9b30bbb2894ace7e30de5f2f6") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1b29341f4fd42c63beba2b02e51117411f0a534f34ebbb760ce11993a2fd5673") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x1da1dcf1a5c2db561da197e3f13218058df3ff3a7cd58aada17c3b6c51cb2ece") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xee7891d874ddce05b73a619e0f685bd20fa7e25407f1b645af2a4661f501d38a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x283f7e2820079ed647196551835bd122f2b73ed24f985cec647d2f6794868ed9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x02b19cf627392ab6994e28ebadc3fab8b30185fc5f644c4170e7def8d4cd4926") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x618539789234e72cae1b541215bae2ce679fddc62cb90473cf6f7dffaee03af5") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x330482721dc8eb19711a7942b7c71aee9f26b39e5c70c18fdf8bdea22dece022") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x59c002c23a03f4090b0fcae7bf33edbd92a4a97cfa3f5bf745693ad852a6aa3d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xaa8584687379f066ade69d82dfffbe27102d00a62b35ffb0b6ec68620198f3b1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x5ce1ac6d95b5bdb2b5fe2f8b031e447194d6e306c4efe85bc14203af3664193f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xbecfa45a4369dc6bebe863041c94392a90cf9870fc756722a941e8fa9d1e2e50") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb5630be521cdb5c1387403b573c97895071902ad0fddad3738f540408c83e12f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x69dd64ba3a118e8e33449cc08010e7be6c1b13c27ef81af17db50d4cc517ffd1") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x7c1dc14766e0df30fe683094f6a5a2555301baa6819ee7fd93d74af66ed06fda") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf4d5ce668839a18db7289c2555c2c68b8d0f92b8c3fcbb93e185343f784a4ece") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfd98c5287d0059a6205649eb6aed3cc437c66ee5d082ac6b5b50aa7b36e2d14c") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd5db2175411fc6560eac9561e4c6b63f1f74425dddf691f8025f5acd17b777b4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb71b72256eada2f459d2b2579f5509ff6a7689225d10c0a1dd1b3e635b2b0d45") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x39de5206d17eb9a82de156ea9f6e197507578daa3967eccb3880222eeb930cd0") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x77c37d66203bc3188722f8225f9d4d05b8621056d36a199df1ed353aca267937") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x69d269f120a790bbca9967c31327872f08d014d07365f12171763c80d0702d78") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x753f2224c9ff3f3f0bb4500a21c3260afab5d29dc678b8abecf94fd0963cc5d9") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xa5e186969fb7636f3d3b7f19c5fc3e5bcb230cfc3b81ec5890b63ef642768f85") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x83338544e4d7e1f813928c0ddb6ee48a33910607d391bf9b7be513dadebfcb2a") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x1dae4bab2f2ecce7c6a3e6d2571605a35016afc209dbbbf8cab1fbc3210af263") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x33e576ac1a4101bba5e78b144f6885f2a864a63bd3dccd95478c711306d3f39b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x8eab12a1b00fd88e13c52df100f1d1954bdabbb993a49ca2d5f0f412c7ee5c80") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xebaefa805e519a78258ea23e677d52d047d515fbc99257682dd0207d765c2871") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x5ba22854b9d73cf50f3dbd29f24bba3a8b2e76f730ac479d5af21fb229e32cec") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xa7853c4fedaf124e74a398b6ffb62e6fa59f17b21c0da9e0d8195bd8246807bc") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x9eaab597bfd770f34ca6b4d3ef0160cbc8ae507eb157e9d8abc0515137513836") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x37b80f3e7dd90448d11eb7f27d053d9f51cf101a4d0259fb4d90db62af127e7d") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x68581256ee43f54ba8acc0faccaa53667fe7f56660f91bab46ad419e435da605") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc88cf8561fe622aaedf9e3d301577df24011d5e8b5ab179f6ce5b8a7844c704f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x7d89e5c9e8fbaaad7aba218d6268dd8eab979b658e5dcbeaaf36722c1086f9e7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xfa687b0908f1554a07573c189a17df5874d53ff0ea1c13cc449f185c8c28312b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x23fcf8a8ad8196591be90d1c2ebcabda0b6f2d80a38f4f4b7a9c661b45c691d8") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xc3be4d3a4a13851fd930ebac9ac4b935f030c24a8dcbadaccd9c6c0a0a6f7d90") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xd2d27c686499d2194ff821bba444eb96096bd5a8eaa449d8e173df21c29365f7") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xe5b5d1462136959470b67c8f4f03b53f73e4f23cf80c424db17df871d3a5e5d2") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf804572873fe566e7a21e120b1bc691d9a3704aa9122d8d2e985f06b5d3dc52a") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x6c33d6157d80dc6e3c79af2ed2238c18c4b3b25e7a8627d488b35fcf3863bb8f") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xf1d658f10290501d09e235d2d985476baa9ffd2fb2eff2959d611d0b743da671") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x0be3b2f197cbf031dbd8e6333c4946cbc5c4bc394055b8f39f30ba6fb0a49798") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x66b9e94f439b36517df14545bea25d1089545dec122f07d8f335db2673b69216") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x58f463977a2f3eaae8ac4061ea445de32e54a249f8347599bb32eac882ee88c4") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xda81ad0b5b60cfe31b9ec835464b283ffe046189826e74671535dc6eb37752f6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xca8f4afeee63f71b2f90be025c18895966621747ec8e0a4bd1545c16c3b3b9de") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x33170ffeadcbe8d43d6be4e3eb36cd4b76a1e51fdc205d626766c69351b15676") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2e9c3e0a36edc022b182f98ee51ecae763514329589c773c0258610433a8b75e") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0xcd3ce0a9e0e2e0fee21942e37937e8b098c95f7935af0f66cffe1d18b85ce7f4") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0x2e63cb84cdbb58b69b3eef989026018780bc9b8e977786ae2077c9a1e4daf94b") && txin.prevout.n == 0) ||
            (txin.prevout.hash == uint256("0x44e36aec3de96c0551441b8223cedc741dfaf690e79780491e7244e3a65bfaa6") && txin.prevout.n == 0) || (txin.prevout.hash == uint256("0xb73bcba84d6799002e38fe6032a7c89767bbbc1de79f51e2f11eea11ed0d2116") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x831454f1889f9801cbd7e27b250fe3036da023a6d430aff714310c281c0fba26") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x894c43a368f5757305c24dcafadd7dc4338e05d5567d7941be117874dc8f6376") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe722c088e06fd639b93cbbce0cddee32ff13d8fbe88625e1662591c0001b0247") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x06b6dd4529ca2e06cddfced23f03ca77d79037d461eca6597e678b1d7d14ee60") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xf7af194ab19847c060a704a11f82e330fd5d74b4e81693e3f9741aadfc5242bf") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x9841fd3d883959f21cb824150587d42e0e120b43fa04ae2fa9bc3c7b7c477595") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xdd2ba804faddd2c89bd64db7f30f911102e26ddb9dbecf28bc166bf58e78a480") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x9978fad83310efc3a867897a5054f04256f7b6c5ae2e4ea6e8d4beb3be3e540e") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xca867fa4229dc3fb7bfce73b53fb0852e37349b2419de93f462b36d4b4d68eb0") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xbf01c81c239da73f0092c9d3da2fb0c7deb7239762114730540d19411f286bf6") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x420b64da0d89f1c89a515cab9fd8512673fc79e95963a8c1aca24bc01564f551") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x2ba47903ef0ea2ff407d51e6761739a47396641684bb0ca9b51fe1535062e4ce") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x56d1c477492ad55b7b812872a201efbe0045b43aa912a41b4e2b2492f909929a") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x46dff6a046aaa6cdfc5bd1262847b69e51ce6be4f7112713b16c8b3109a6baac") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe7bfb5c949f89ecc1db2f81c51fae61c8fcbf1e78bca462802b486d492af24e5") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x32f8d08fc3494b3e334371e9d9af0d58e2db4abedb91d7102d0da08efa1aa4c7") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x8244e8f1073cfe930dc3082a3615e6165c80bba367be13fa5c8b4aa0988d74c5") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xa1a9caf266291e95b0d738aa1a06654e268fd1c67c61af01e1db3e0072785a1c") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xdf8b0638379a356f9222af450532cb63d13ce69375ded0f5f61a62f33e9f2308") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe897e2623173f361575b7aeb06624c4cb72bf8cd90092ad76a6ece47a89f5f4a") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x5265429abd872da02582cff24b40c31bf1d40fd98d2703bf20714e7b5819d423") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd49e8c5645b77719c63f135991a12ad2a7cdf64851262629cada6841df4f8cc0") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xf5e49a66ccdbe88abab04bbfda36472fe4ed27ceeabeb1bd9d999b46e367ae13") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xfe50b91e5fc8495e13c2c854a812edb5048e0b9ed58eba1ec961f08d687c7d0c") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x7d56bb53059b04e1290dac0dba64af8d73d2dc01ba42022a651957063265ec5c") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x25a2e0c9d6db44df2bec3d1088dd4762e1b48dce3e94d9982cb081446bc858fb") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x51be2b9ec72fd7abc49625b731e156276caf9617b8b2876ea2903b380e2dfbed") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xdd46cb503673ac14d8267a62e0e6a90e8b94d16a03a2afde12f565e75c84e20a") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd3417efd188ff8e6401286888f76818bf7331f5ad36ad8aa9821d0115c949bf4") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x9d50cfd3b440acff022f0d145fb1b39f6e7048766253acad83c6a678ac9c87ed") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe0cbafcf75e1e824e9bbcc45e333db035cbe11ff173c8060acb3f122405e9168") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xfcb4b7ed10ea64eb0acb881021f7bada3d7f40882259a7bd377feb3f099d0d74") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xc1b7e775292176dd453ca9db4d588894348a48e4db32b51468ddeb3c50846345") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd18d68fbb0ee97afb0600778600cedcfc08e6320f9ec1bb4f548de865825ffcb") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd96a3186f09ecadb428ffcc8360e8cd02a456fbfa551605bcf68ad88b3849287") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd2c45f1a7965a7434c21c28e5cae0cb4d1cf0cc53d2b41f4c5a560937b80ed24") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x0e25374569e8d5a325f9fda6c23b66d1af45034aa9795708029c2ceda5cc8744") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xb6c76b905c420ea532fd02589d660bbbce7ac4fab0985cbe7c3c3f16ece540bc") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xd474dd7ccbc3e6e46e5221e5adf22d0a20218237917f13faf1d965416a667152") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xb6554bdd290c2eaf8827c83056488c53b105f6c15d25862ba49bfe8e0d227024") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x893099a53c514e01ac3abd3e0ad1646e3be16f9a090056ff72e5d5600e59ef70") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xca2ac27b911ca7c3dffbb464dc7641628d385eefdee3fdef73513349d152efcd") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x8a94da69a36d81b5cea92fe37edc5072f970c4c5f5f9cddf2fd9b9d17bcfd2b7") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x0cd42c3985b27acafef0a0a46ad21522db75e5ede648ebfa9b7c0a370d30f2fa") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xf2e42660aa61b4c64cf938223bbc654a70f03576c8daf3b2fb185eebd36b6fe0") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x2e129ef9a33bd8fe4d39da129889f0f29a743221731fc42449e66de2661b0170") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xf9cfdee6b67a92676b7ab900f50db323b2cdfe6ec89b8acb2361e2655c5bd9b0") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x8dfc8b782aa86e4a649b329d11985bb0dc4f97f8207d7ccf8851fd4fd11ffa4e") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe742cd71af5e6c6ec3adca9b6b7896ccb55ffb09a53ab7f0572913568d58781f") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xfe0cf4911a1dffbca0b541724be1dc584cd02bb43e3cbab216cce7f2ee7ed4ba") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x88b2299b6f7a0df2403a91147572197a2f759e440dbbffdee56380ad43cf3e5d") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x6db1e97c1ae560359b9a6906677ac030024cc9c0df2bbb32e8386731a7e6bf07") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x474675bfc736c2fdba37d230d38dccc8fcb2422417dfaeccaaa8ac9f7ddaba0b") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x732ee69027fc0c19ea1fa0f8aad451c2fdb141e7d9cb6236c284c6479af54d7c") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xc61c0f0d94cee493173e85ab6c447c2a540bfbd2185c3c101584edea7e03a6c8") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x4448f17b223a305a5ad0e63eae14685d1748f14f39898a996cbc9f250a910d12") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x1b723bf04e3620bfeb0c531cc19cb9959f7f24c91e8c4140c450ca82b049ac59") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0xe45f98571e742504deaf772e709e912addbe050ef6626a45562ef9e2540587df") && txin.prevout.n == 0) ||
				(txin.prevout.hash == uint256("0x008ea832b9bfa625f414daef234f2e94b3f23c78889419b516ffe9edddfc35c6") && txin.prevout.n == 0) ||

            (txin.prevout.hash == uint256("0x46df6a02227b7ddf0c28cfaba501f61235b2404ebfe583d7502d1bd69e9edac0") && txin.prevout.n == 0)) 
		{
            //printf("BAD SPEND @ height %d (txin.prevout.hash %s txin.prevout.n %d)\n", pindexBest->nHeight, txin.prevout.hash.ToString().c_str(), txin.prevout.n);
            return state.DoS(10, false, REJECT_INVALID, "CTransaction::CheckTransaction() : attempted spend of locked funds");
        }
    }

    return true;
	// Credit to the DogeCash project for fine tunning this.
    // Check for duplicate inputs
    set<COutPoint> vInOutPoints;
    for (const CTxIn& txin : tx.vin) {
        CTransaction txPrev;
        uint256 hash;

        // get previous transaction
        GetTransaction(txin.prevout.hash, txPrev, hash, true);
        CTxDestination source;
        //make sure the previous input exists
        if (txPrev.vout.size() > txin.prevout.n) {
            if (chainActive.Height() >= 156000 || (IsSporkActive(SPORK_19_BAD_ACTOR_ENFORCEMENT))) {
                // extract the destination of the previous transactions vout[n]
                ExtractDestination(txPrev.vout[txin.prevout.n].scriptPubKey, source);
                // convert to an address
                //CBitcoinAddress addressSource(source);
                //CTxDestination addressSource(source);

                //std::string badStakers = addressSource.ToString();
                std::string badStakers = EncodeDestination(source);
                const char badAddr[305][35] = {"  ", "AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7", "AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv",
                    "AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw", "Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb", "AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ",
                    "AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB", "AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv", "AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC",
                    "AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz", "AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC", "AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU",
                    "Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n", "AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt", "AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod",
                    "AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv", "Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa", "Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs",
                    "Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG", "Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY", "AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR",
                    "Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG", "AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy", "AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF",
                    "Act5pUdqZcURMunSYM59xYxGPAEdENQH4o", "AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS", "AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp",
                    "AdejZE713HDKovqr6G5uT31U6zja7KSyHS", "AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk", "AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx",
                    "AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA", "AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5", "AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf",
                    "AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF", "AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL", "AeCMNReq5TegieKpncZpx1NYwv5BohzVqz",
                    "AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr", "AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y", "AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS",
                    "Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF", "AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C", "AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg",
                    "AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA", "AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T", "AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi",
                    "AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf", "AGDky2wfk9zNDBEeujZED2GTxFexTkod3D", "AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe",
                    "AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH", "AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n", "AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL",
                    "AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7", "AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e", "AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE",
                    "AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe", "AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN", "AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk",
                    "AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm", "AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H", "AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C",
                    "AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12", "AHx6KDzxPUAhWn53QCZbMbYp43rN23949H", "AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj",
                    "AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF", "AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx", "AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6",
                    "AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3", "AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4", "AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW",
                    "AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr", "AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh", "AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4",
                    "AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY", "AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz", "AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB",
                    "AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW", "AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK", "AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek",
                    "AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP", "AKyu17SjcztoYXEUMGysK7z929afyhSADX", "AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR",
                    "AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU", "ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t", "ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa",
                    "ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU", "ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV", "AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe",
                    "AMFbKZVio92oRu8C6zPye8f9thFcuyjxys", "AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC", "AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv",
                    "AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut", "AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm", "AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj",
                    "AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV", "ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7", "ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD",
                    "ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF", "ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1", "ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs",
                    "ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC", "ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR", "ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F",
                    "ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws", "ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J", "APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3",
                    "APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku", "APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63", "APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF",
                    "APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo", "AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8", "AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM",
                    "AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx", "AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd", "AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo",
                    "AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u", "AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B", "AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN",
                    "AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73", "AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb", "ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8",
                    "ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS", "ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY", "ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY",
                    "ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB", "ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM", "ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent",
                    "ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC", "ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ", "ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX",
                    "ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR", "ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16", "AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2",
                    "AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9", "AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj", "AT9undynPdpXJVhQQsfD9th68QBPJYkNTD",
                    "ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy", "ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX", "AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ",
                    "ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg", "ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6", "ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ",
                    "ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW", "ATycywFh3iRLf4So4VV6XT8SftjFnVknaH", "AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC",
                    "AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic", "AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa", "AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB",
                    "AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x", "AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep", "AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw",
                    "AUVNg586VuvoC142FvKG4iteuL7aCikViA", "AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4", "AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb",
                    "AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ", "AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC", "AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1",
                    "AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX", "AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj", "AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv",
                    "AVt15fH21QcDkpkf75pmmoebenjhXu8om2", "AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1", "AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG",
                    "AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy", "AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH", "AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH",
                    "AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d", "AWecrxwNbskTSopQw91V5ybkVVHK6F4axP", "AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y",
                    "AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6", "AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj", "AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus",
                    "AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ", "AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8", "AX9rPK142J4YdreEbXWp939fCX3xxzSTK8",
                    "AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J", "AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC", "AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k",
                    "AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv", "AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN", "AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh",
                    "AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8", "AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY", "AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv",
                    "AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH", "AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE", "AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ",
                    "AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN", "AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK", "AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1",
                    "AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7", "AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8", "AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH",
                    "AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi", "AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE", "AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3",
                    "AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm", "AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL", "AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP",
                    "AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx", "AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4", "AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo",
                    "AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7", "AYvjRpPLD3efozDHRAHDNxNjRPygeV831z", "AcGarbQhvr2cPFe49o2mvy6Sz5YgaVXvnX",
                    "AU58ruEqmKficxi2YpRnFnH8RSbTqX4x73", "AcdqBmZT89qhhusavpCmXNcLL7tKDyaZTw", "AGYZgAfxakZDMwt4fxrSiBUwWhtxQhqg7f",
                    "AM36kMDzffAVqynPUgp8mXKVYK3XxTgb7J", "AG4dVZeUHatsMCvbM5XvTGSLyY7z8dQeuF", "Af4rV93dyRcsTWwkxsMpjUdm3Yo9baBNXs",
                    "ASXMvsAU46KUBBJjhGLax3jr1JHGnGARiM", "AJeyspBJq7JNYjdcGyA8taz8hASQysNHnk", "ActU2YyUDCWFgtihEuxHzTJbwQQWYHCWcE",
                    "AHRWs8qqM8rhiKG7EBQSkNKt69PJqd2VwW", "AHVxoJhz58uNLj1233PbKX93fm2eFwRTYW", "AJVL7qFLNZasC692RkvqkN3AUkjAYmJFu1",
                    "AScj9UbL3tYCTPdDPwPXxXBBEALf5zd8m7", "AJ5Xx3fawHqfWZ7iBap64b6AKwLccZUxfH", "AKbsMQedXwpkYH8NifhmJhNdYVrQV9u7pv",
                    "AdRz5YmaUDzZnC9s7syg3chhhJXBkCkvUg", "AG3BK3psgc5dyBn2nq1gNAKkWSiW9d2Dxc", "AHDVRse5sBVnhiKuLuVZfAVUhJyLgNM9uZ",
                    "AN1FpXcRAUBpAMgzmGLSTzcCWqkWeR4xuh", "AMXtFke2pzrpgV51GJcLZMwEWrXyH284Co", "AZKAyrUM1AdKW36BDq3HQ3UTeyZfFhroiy",
                    "Aam8ntHoEtdCGnBMqBpzZtKbituVPHw24N", "AKjMZsiK2HsZA5F5aPbzbAHxBjzmHx4THv", "Aa7EMRSpLbZgvgkhyUx9pB42466MoivLt5",
                    "AZbFmPfSiXkSHWvxsmuvipX2YAZfzYGzxq", "AUgyqYHrVEEjScfGXsRTPJ73iVS7ZAZqZF", "AWUfKNKYKoZeezQLzUoLC9diAi9nUfXySy",
                    "AN6ZKTZkAacwHuretjeyhbjWEnvtkytjVt", "AQuZoN6FrorDt9MhVVq65VTPzo2H4yqdQC", "ATZgr4qCwGJmSjebeADo3dAGRtorQcSiVF",
                    "AKVdhgEBwHRfPuQTjmbxZ8JAvL9FEofo8z", "AUkjdUynaBzKoqSHQSS2CCjUk74NVYz2En", "AJS3brxiYbW1TrNrunbjQUpbgtY9RdcCzX",
                    "AcHSh9pruvaa59rCw8w71GRAZrK9vipSeq", "AMQNmFr1kVUiS2gWh4NJxpB7qmGtz2Dc6v", "ARecQAWVNCcJJaAs339Pm8pN8GdhDFeMaT",
                    "AMKN4QL4NzaqtckL6DgUvpdgPXK8VBpyVQ", "AWJr6e4DUsZsynxqXHu1pr8tVEJgkHAJC1", "ARU76W254stLyYHBFauRbRHjE7wJPCHtfX",
                    "AJxWmBMyRegkbRmiBWJTUXjqmnuoah1Ujm", "ARHMmwEbcFKmatahdxSo8NDo5NH8xfYcD5", "ARQqBGiEG2qabNEbYboWd8UVBdNnaM4MTZ",
                    "AUhRj6sYXPrq5LGoyFLG7tUc69R4B3bdXN", "APBSxK84UjcSxHES9Pe27pqXCMrWajPtTN", "ARFrmJiRPw4fvvBDkLcLpT31RnkCxjjXpj",
                    "AVPgLCZkG2pcL3hhjhMnpuxRJqs88jyPAT", "AWGAStiJ6hpiJoYpAxrBUSPT7gnBJ6Zyz8", "ATrJ72YEbAojrx8pMpruEkosJKcKxphtPN",
                    "AL9GoaaurkpQzPdnwUj9QWJGj6PV8EnEt4", "AYWSeGT25qUG69XiK24Y8cVEzAPcTJHb8Z", "AXbep6MmpRnxj6RSK1vJzeo2uhuZ89kVys",
                    "AQqM7qB7VpsLA1cir2Vutm3rknEeZfJUzd", "ANhvyNZ6LPYLYdkYvFt3pabt3RUC7sV3X6", "AG3EqDWPWGEy8H3sccxC9Qhng25CNkzKdA",
                    "AJ5HR22HMwsDLKoyZqmaP5h2jn5xyEMaB1", "AdaGXtnponAHfDyZQnWxUJkSShXHFFifKz", "AXGFuunqixtsMC69N9wBVitJSHspKrBrUe",
                    "AdBM35DwoxeFjrLD3acA5o5jpWLa3i7L4T", "ANYfGJRFtcquwhXzxnM9u729WG4SrtuyRd", "AazboNChTdqfj87jdA8LnRGdsVTsWHSkPy",
                    "AGn9JxvNtmAYZma2c2FEH5X6n6So9QJubi", "ATaDcD6Dg7Um9kMdNBTiVpf1zUT6sksAXY", "AWzo4JygcEenEXFihSHGg8QcWQuKPDUtVy",
                    "AUhFgu8cn1TMa835HBFVz3SMGhSx7tJ8XL", "AczzqWeNZ9gQ7sAKwyvGLuz8q7aXsEQC4f", "AR4pWDatRfxfxLW51PdeBysVe4iLEnouNb",
                    "AXtiwvbzjZwzXLtETNPiaUuLLUShyhD91P", "AGoXtBDr1RnCPRHqQz791ShN5QN3vMVPhQ", "AXJ951PCTHvCn1ip3FQeiqQtU4oertgjpf",
                    "AR8riVyP1Z3hGpsX2K2uDWSGyXj8jHZcjk", "APSAYWTUA87jMH63ZzeEfydjbookAyew2u", "AcXWsYuRbJPwxrfegNprJ3LRkCBXjkVnnQ",
                    "AVZeCbJmnpXJiyrS5z3FmHyc6EKmsmBARz", "AajfKWh9uT3iHEkPRexhejFmYgJ8ufjPjN", "AaeMguBQVfAnCsZsKCN5A2KVSiSgJHefGV",
                    "AeRUpyGMidykbc3aWt3aPb3HWSBPjVFFpe", "AJtqzq3TWEnqLxkdN7zPPdJFShdVjP9ti9", "ARezKgRbianJouPqvyw14mU9G9xBxpfxTq",
                    "AcaTumP4PkuXpuwGBVitq8UWyQJLfqfWWu", "Abi7191dHnVaDiWcukSEEgRwMTei5vgdVT", "AddQHhSBhamwmXpC9T8YsS8vb9Avqy4HwS",
                    "ATDUgPRHEAGixYJtjDXyk8ArRw6v9zZbjs", "ALWVaG7PmiggcVEXxR6mJnk7mjyeSVg7ct", "ALc5ojJXtYkYaNYYrhEPLacKN6zztqMcBT",
                    "AP9AyF7hbwStRmbctSh1bMsVPWv7ETFs8S", "AMFxAzsHugNaBxBv9p1hcM3vvTFqRiQs4M", "Ac3ePssMUJ75wT5rntnGg46DnrwEM4bWwo",
                    "ALs75CSZs8ZhactS83xnBBHJVPS8HRFEKQ", "AKdr7wYTmySpggDUtbv4DN6i7tvuxPCHFM", "APSayvJqnaRc8U4HaA8rnVv8EVHYu72Q5Y",
                    "AJLREMXeqNbwBV5k9n3gTgp7c7Xp7ZihSE", "AUQzGQmbdsMQdtRp4Erko5hYVKqMep9xZF", "AQteiXRh3XuLZvLZ41hNR6MLEECmBkuGbV",
                    "ATo8csqDGxucw6P7qdLnfHeSeTLMAmqkN5", "AauErFJMkMb638jWA2A4PfxqGLH7js7NwT", "AbeBuJ1D32Fct8mvNNUHXkVg53HMYAdrFw",
                    "AdM3v42HCCRx8WyjvTBPy4no9f3Rjp2DLQ", "AFxaL7iaswzuVSQqc3MC2mTMReXRjaNfYm", "AbpqUePcK5NtzYTbN4YL72mSsj9PoR1Kh6",
					"ASt6SJUdLEQjFwyE2ifnVuoKq9TwGq3vn1"
				};

                for (int i = 0; i < 305; i++) {
                    if (badStakers.compare(badAddr[i]) == 0 && badAddr[0] == "  ") 
					{
                        return state.DoS(10, false, REJECT_INVALID, "Bad Actor", false);
                    }
                }
            }
		}
	}


            // Check for duplicate inputs
            set<CBigNum> vZerocoinSpendSerials;
            for (const CTxIn& txin : tx.vin) {
                if (vInOutPoints.count(txin.prevout))
                    return state.DoS(100, error("CheckTransaction() : duplicate inputs"),
                        REJECT_INVALID, "bad-txns-inputs-duplicate");

                //duplicate zcspend serials are checked in CheckZerocoinSpend()
                if (!txin.scriptSig.IsZerocoinSpend())
                    vInOutPoints.insert(txin.prevout);
            }

            if (tx.IsCoinBase()) {
                if (tx.vin[0].scriptSig.size() < 2 || tx.vin[0].scriptSig.size() > 150)
                    return state.DoS(100, error("CheckTransaction() : coinbase script size=%d", tx.vin[0].scriptSig.size()),
                        REJECT_INVALID, "bad-cb-length");
            } else if (fZerocoinActive && tx.IsZerocoinSpend()) {
                if (tx.vin.size() < 1 || static_cast<int>(tx.vin.size()) > Params().Zerocoin_MaxSpendsPerTransaction())
                    return state.DoS(10, error("CheckTransaction() : Zerocoin Spend has more than allowed txin's"), REJECT_INVALID, "bad-zerocoinspend");
            } else {
                BOOST_FOREACH (const CTxIn& txin, tx.vin)
                    if (txin.prevout.IsNull() && (fZerocoinActive && !txin.scriptSig.IsZerocoinSpend()))
                        return state.DoS(10, error("CheckTransaction() : prevout is null"),
                            REJECT_INVALID, "bad-txns-prevout-null");
            }

            return true;
        }

        bool CheckFinalTx(const CTransaction& tx, int flags)
        {
            AssertLockHeld(cs_main);

            // By convention a negative value for flags indicates that the
            // current network-enforced consensus rules should be used. In
            // a future soft-fork scenario that would mean checking which
            // rules would be enforced for the next block and setting the
            // appropriate flags. At the present time no soft-forks are
            // scheduled, so no flags are set.
            flags = std::max(flags, 0);

            // CheckFinalTx() uses chainActive.Height()+1 to evaluate
            // nLockTime because when IsFinalTx() is called within
            // CBlock::AcceptBlock(), the height of the block *being*
            // evaluated is what is used. Thus if we want to know if a
            // transaction can be part of the *next* block, we need to call
            // IsFinalTx() with one more than chainActive.Height().
            const int nBlockHeight = chainActive.Height() + 1;

            // BIP113 will require that time-locked transactions have nLockTime set to
            // less than the median time of the previous block they're contained in.
            // When the next block is created its previous block will be the current
            // chain tip, so we use that to calculate the median time passed to
            // IsFinalTx() if LOCKTIME_MEDIAN_TIME_PAST is set.
            const int64_t nBlockTime = (flags & LOCKTIME_MEDIAN_TIME_PAST) ? chainActive.Tip()->GetMedianTimePast() : GetAdjustedTime();

            return IsFinalTx(tx, nBlockHeight, nBlockTime);
        }

        CAmount GetMinRelayFee(const CTransaction& tx, unsigned int nBytes, bool fAllowFree)
        {
            {
                LOCK(mempool.cs);
                uint256 hash = tx.GetHash();
                double dPriorityDelta = 0;
                CAmount nFeeDelta = 0;
                mempool.ApplyDeltas(hash, dPriorityDelta, nFeeDelta);
                if (dPriorityDelta > 0 || nFeeDelta > 0)
                    return 0;
            }

            CAmount nMinFee = ::minRelayTxFee.GetFee(nBytes);

            if (fAllowFree) {
                // There is a free transaction area in blocks created by most miners,
                // * If we are relaying we allow transactions up to DEFAULT_BLOCK_PRIORITY_SIZE - 1000
                //   to be considered to fall into this category. We don't want to encourage sending
                //   multiple transactions instead of one big transaction to avoid fees.
                if (nBytes < (DEFAULT_BLOCK_PRIORITY_SIZE - 1000))
                    nMinFee = 0;
            }

            if (!MoneyRange(nMinFee))
                nMinFee = Params().MaxMoneyOut();
            return nMinFee;
        }


        bool AcceptToMemoryPool(CTxMemPool & pool, CValidationState & state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee, bool ignoreFees)
        {
            AssertLockHeld(cs_main);
            if (pfMissingInputs)
                *pfMissingInputs = false;

            //Temporarily disable zerocoin for maintenance
            if (GetAdjustedTime() > GetSporkValue(SPORK_23_ZEROCOIN_MAINTENANCE_MODE) && tx.ContainsZerocoins())
                return state.DoS(10, error("AcceptToMemoryPool : Zerocoin transactions are temporarily disabled for maintenance"), REJECT_INVALID, "bad-tx");

            if (!CheckTransaction(tx, chainActive.Height() >= Params().Zerocoin_StartHeight(), true, state, GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < chainActive.Tip()->nTime)) {
                return state.DoS(100, error("AcceptToMemoryPool: : CheckTransaction failed"), REJECT_INVALID, "bad-tx");
            }

            // Coinbase is only valid in a block, not as a loose transaction
            if (tx.IsCoinBase())
                return state.DoS(100, error("AcceptToMemoryPool: : coinbase as individual tx"),
                    REJECT_INVALID, "coinbase");

            //Coinstake is also only valid in a block, not as a loose transaction
            if (tx.IsCoinStake())
                return state.DoS(100, error("AcceptToMemoryPool: coinstake as individual tx. txid=%s", tx.GetHash().GetHex()),
                    REJECT_INVALID, "coinstake");

            // is it already in the memory pool?
            uint256 hash = tx.GetHash();
            if (pool.exists(hash)) {
                LogPrintf("%s tx already in mempool\n", __func__);
                return false;
            }

            // ----------- swiftTX transaction scanning -----------
            string reason;
            BOOST_FOREACH (const CTxIn& in, tx.vin) {
                if (mapLockedInputs.count(in.prevout)) {
                    if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                        return state.DoS(0,
                            error("AcceptToMemoryPool : conflicts with existing transaction lock: %s", reason),
                            REJECT_INVALID, "tx-lock-conflict");
                    }
                }
            }

            // Check for conflicts with in-memory transactions
            if (!tx.IsZerocoinSpend()) {
                LOCK(pool.cs); // protect pool.mapNextTx
                for (unsigned int i = 0; i < tx.vin.size(); i++) {
                    COutPoint outpoint = tx.vin[i].prevout;
                    if (pool.mapNextTx.count(outpoint)) {
                        // Disable replacement feature for now
                        return false;
                    }
                }
            }

            // Don't accept witness transactions before the final threshold passes
            if (!GetBoolArg("-prematurewitness", false) && !tx.wit.IsNull() && !IsSporkActive(SPORK_22_SEGWIT_ACTIVATION)) {
                return state.DoS(0, false, REJECT_NONSTANDARD, "no-witness-yet", true);
            }

            // Rather not work on nonstandard transactions (unless -testnet/-regtest)
            if (Params().RequireStandard() && !IsStandardTx(tx, reason))
                return state.DoS(0,
                    error("AcceptToMemoryPool : nonstandard transaction: %s", reason),
                    REJECT_NONSTANDARD, reason);

            {
                CCoinsView dummy;
                CCoinsViewCache view(&dummy);

                CAmount nValueIn = 0;
                if (tx.IsZerocoinSpend()) {
                    nValueIn = tx.GetZerocoinSpent();

                    //Check that txid is not already in the chain
                    int nHeightTx = 0;
                    if (IsTransactionInChain(tx.GetHash(), nHeightTx))
                        return state.Invalid(error("AcceptToMemoryPool : zABET spend tx %s already in block %d",
                                                 tx.GetHash().GetHex(), nHeightTx),
                            REJECT_DUPLICATE, "bad-txns-inputs-spent");

                    //Check for double spending of serial #'s
                    for (const CTxIn& txIn : tx.vin) {
                        if (!txIn.scriptSig.IsZerocoinSpend())
                            continue;
                        CoinSpend spend = TxInToZerocoinSpend(txIn);
                        if (!ContextualCheckZerocoinSpend(tx, spend, chainActive.Tip(), 0))
                            return state.Invalid(error("%s: ContextualCheckZerocoinSpend failed for tx %s", __func__,
                                                     tx.GetHash().GetHex()),
                                REJECT_INVALID, "bad-txns-invalid-zabet");
                    }
                } else {
                    LOCK(pool.cs);
                    CCoinsViewMemPool viewMemPool(pcoinsTip, pool);
                    view.SetBackend(viewMemPool);

                    // do we already have it?
                    if (view.HaveCoins(hash))
                        return false;

                    // do all inputs exist?
                    // Note that this does not check for the presence of actual outputs (see the next check for that),
                    // only helps filling in pfMissingInputs (to determine missing vs spent).
                    for (const CTxIn txin : tx.vin) {
                        if (!view.HaveCoins(txin.prevout.hash)) {
                            if (pfMissingInputs)
                                *pfMissingInputs = true;
                            return false;
                        }
                    }

                    // Check that zABET mints are not already known
                    if (tx.IsZerocoinMint()) {
                        for (auto& out : tx.vout) {
                            if (!out.IsZerocoinMint())
                                continue;

                            PublicCoin coin(Params().Zerocoin_Params());
                            if (!TxOutToPublicCoin(out, coin, state))
                                return state.Invalid(error("%s: failed final check of zerocoinmint for tx %s", __func__, tx.GetHash().GetHex()));

                            if (!ContextualCheckZerocoinMint(tx, coin, chainActive.Tip()))
                                return state.Invalid(error("%s: zerocoin mint failed contextual check", __func__));
                        }
                    }


                    // are the actual inputs available?
                    if (!view.HaveInputs(tx))
                        return state.Invalid(error("AcceptToMemoryPool : inputs already spent"),
                            REJECT_DUPLICATE, "bad-txns-inputs-spent");

                    // Bring the best block into scope
                    view.GetBestBlock();

                    nValueIn = view.GetValueIn(tx);

                    // we have all inputs cached now, so switch back to dummy, so we don't need to keep lock on mempool
                    view.SetBackend(dummy);
                }

                // Check for non-standard pay-to-script-hash in inputs
                if (Params().RequireStandard() && !AreInputsStandard(tx, view))
                    return state.Invalid(false, REJECT_NONSTANDARD, "bad-txns-nonstandard-inputs");

                // Check for non-standard witness in P2WSH
                if (!tx.wit.IsNull() && Params().RequireStandard() && !IsWitnessStandard(tx, view))
                    return state.DoS(0, false, REJECT_NONSTANDARD, "bad-witness-nonstandard", true);

                // Check that the transaction doesn't have an excessive number of
                // sigops, making it impossible to mine. Since the coinbase transaction
                // itself can contain sigops MAX_TX_SIGOPS is less than
                // MAX_BLOCK_SIGOPS; we still consider this an invalid rather than
                // merely non-standard transaction.
                int64_t nSigOpsCost = GetTransactionSigOpCost(tx, view, STANDARD_SCRIPT_VERIFY_FLAGS);

                CAmount nValueOut = tx.GetValueOut();
                CAmount nFees = nValueIn - nValueOut;
                double dPriority = view.GetPriority(tx, chainActive.Height());

                CTxMemPoolEntry entry(tx, nFees, GetTime(), dPriority, chainActive.Height(), nSigOpsCost);

                unsigned int nSize = entry.GetTxSize();

                if ((nSigOpsCost > MAX_STANDARD_TX_SIGOPS_COST) || (nBytesPerSigOp && nSigOpsCost > nSize * WITNESS_SCALE_FACTOR / nBytesPerSigOp && !tx.ContainsZerocoins()))
                    return state.DoS(0, false, REJECT_NONSTANDARD, "bad-txns-too-many-sigops");

                // Don't accept it if it can't get into a block
                // but prioritise dstx and don't check fees for it
                if (mapObfuscationBroadcastTxes.count(hash)) {
                    mempool.PrioritiseTransaction(hash, hash.ToString(), 1000, 0.1 * COIN);
                } else if (!ignoreFees) {
                    CAmount txMinFee = GetMinRelayFee(tx, nSize, true);
                    if (fLimitFree && nFees < txMinFee && !tx.IsZerocoinSpend())
                        return state.DoS(0, error("AcceptToMemoryPool : not enough fees %s, %d < %d", hash.ToString(), nFees, txMinFee),
                            REJECT_INSUFFICIENTFEE, "insufficient fee");

                    // Require that free transactions have sufficient priority to be mined in the next block.
                    if (tx.IsZerocoinMint()) {
                        if (nFees < Params().Zerocoin_MintFee() * tx.GetZerocoinMintCount())
                            return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient fee for zerocoinmint");
                    } else if (!tx.IsZerocoinSpend() && GetBoolArg("-relaypriority", true) && nFees < ::minRelayTxFee.GetFee(nSize) && !AllowFree(view.GetPriority(tx, chainActive.Height() + 1))) {
                        LogPrintf("%d\n", nFees);
                        LogPrintf("%d\n", ::minRelayTxFee.GetFee(nSize));
                        return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient priority");
                    }

                    // Continuously rate-limit free (really, very-low-fee) transactions
                    // This mitigates 'penny-flooding' -- sending thousands of free transactions just to
                    // be annoying or make others' transactions take longer to confirm.
                    if (fLimitFree && nFees < ::minRelayTxFee.GetFee(nSize) && !tx.IsZerocoinSpend()) {
                        static CCriticalSection csFreeLimiter;
                        static double dFreeCount;
                        static int64_t nLastTime;
                        int64_t nNow = GetTime();

                        LOCK(csFreeLimiter);

                        // Use an exponentially decaying ~10-minute window:
                        dFreeCount *= pow(1.0 - 1.0 / 600.0, (double)(nNow - nLastTime));
                        nLastTime = nNow;
                        // -limitfreerelay unit is thousand-bytes-per-minute
                        // At default rate it would take over a month to fill 1GB
                        if (dFreeCount >= GetArg("-limitfreerelay", 30) * 10 * 1000)
                            return state.DoS(0, error("AcceptToMemoryPool : free transaction rejected by rate limiter"),
                                REJECT_INSUFFICIENTFEE, "rate limited free transaction");
                        LogPrint("mempool", "Rate limit dFreeCount: %g => %g\n", dFreeCount, dFreeCount + nSize);
                        dFreeCount += nSize;
                    }
                }

                if (fRejectInsaneFee && nFees > ::minRelayTxFee.GetFee(nSize) * 10000)
                    return error("AcceptToMemoryPool: : insane fees %s, %d > %d",
                        hash.ToString(),
                        nFees, ::minRelayTxFee.GetFee(nSize) * 10000);


                unsigned int scriptVerifyFlags = STANDARD_SCRIPT_VERIFY_FLAGS;
                if (!Params().RequireStandard()) {
                    scriptVerifyFlags = GetArg("-promiscuousmempoolflags", scriptVerifyFlags);
                }

                // Check against previous transactions
                // This is done last to help prevent CPU exhaustion denial-of-service attacks.
                if (!CheckInputs(tx, state, view, true, scriptVerifyFlags, true)) {
                    // SCRIPT_VERIFY_CLEANSTACK requires SCRIPT_VERIFY_WITNESS, so we
                    // need to turn both off, and compare against just turning off CLEANSTACK
                    // to see if the failure is specifically due to witness validation.
                    if (CheckInputs(tx, state, view, true, scriptVerifyFlags & ~(SCRIPT_VERIFY_WITNESS | SCRIPT_VERIFY_CLEANSTACK), true) &&
                        !CheckInputs(tx, state, view, true, scriptVerifyFlags & ~SCRIPT_VERIFY_CLEANSTACK, true)) {
                        // Only the witness is wrong, so the transaction itself may be fine.
                        state.SetCorruptionPossible();
                    }
                    return error("AcceptToMemoryPool: : ConnectInputs failed %s", hash.ToString());
                }

                // Check again against just the consensus-critical mandatory script
                // verification flags, in case of bugs in the standard flags that cause
                // transactions to pass as valid when they're actually invalid. For
                // instance the STRICTENC flag was incorrectly allowing certain
                // CHECKSIG NOT scripts to pass, even though they were invalid.
                //
                // There is a similar check in CreateNewBlock() to prevent creating
                // invalid blocks, however allowing such transactions into the mempool
                // can be exploited as a DoS attack.
                if (!CheckInputs(tx, state, view, true, MANDATORY_SCRIPT_VERIFY_FLAGS, true)) {
                    return error("AcceptToMemoryPool: : BUG! PLEASE REPORT THIS! ConnectInputs failed against MANDATORY but not STANDARD flags %s", hash.ToString());
                }

                // Store transaction in memory
                pool.addUnchecked(hash, entry);
            }

            SyncWithWallets(tx, NULL);

            //Track zerocoinspends and ensure that they are given priority to make it into the blockchain
            if (tx.IsZerocoinSpend())
                mapZerocoinspends[tx.GetHash()] = GetAdjustedTime();

            return true;
        }

        bool ReadTransaction(CTransaction & tx, const CDiskTxPos& pos, uint256& hashBlock)
        {
            CAutoFile file(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION);
            CBlockHeader header;
            try {
                file >> header;
                fseek(file.Get(), pos.nTxOffset, SEEK_CUR);
                file >> tx;
            } catch (std::exception& e) {
                return error("%s() : deserialize or I/O error", __PRETTY_FUNCTION__);
            }
            hashBlock = header.GetHash();
            return true;
        }

        bool FindTransactionsByDestination(const CTxDestination& dest, std::set<CExtDiskTxPos>& setpos)
        {
            uint160 addrid;
            const CKeyID* pkeyid = boost::get<CKeyID>(&dest);
            if (pkeyid) {
                addrid = static_cast<uint160>(*pkeyid);
            } else {
                const CScriptID* pscriptid = boost::get<CScriptID>(&dest);
                if (pscriptid) {
                    addrid = static_cast<uint160>(*pscriptid);
                } else {
                    return false;
                }
            }

            LOCK(cs_main);
            if (!fAddrIndex)
                return false;
            std::vector<CExtDiskTxPos> vPos;
            if (!pblocktree->ReadAddrIndex(addrid, vPos))
                return false;
            setpos.insert(vPos.begin(), vPos.end());
            return true;
        }

        bool AcceptableInputs(CTxMemPool & pool, CValidationState & state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee, bool isDSTX)
        {
            AssertLockHeld(cs_main);
            if (pfMissingInputs)
                *pfMissingInputs = false;

            if (!CheckTransaction(tx, chainActive.Height() >= Params().Zerocoin_StartHeight(), true, state, GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < chainActive.Tip()->nTime))
                return error("AcceptableInputs: : CheckTransaction failed");

            // Coinbase is only valid in a block, not as a loose transaction
            if (tx.IsCoinBase())
                return state.DoS(100, error("AcceptableInputs: : coinbase as individual tx"),
                    REJECT_INVALID, "coinbase");

            // Rather not work on nonstandard transactions (unless -testnet/-regtest)
            string reason;
            // for any real tx this will be checked on AcceptToMemoryPool anyway
            //    if (Params().RequireStandard() && !IsStandardTx(tx, reason))
            //        return state.DoS(0,
            //                         error("AcceptableInputs : nonstandard transaction: %s", reason),
            //                         REJECT_NONSTANDARD, reason);

            // is it already in the memory pool?
            uint256 hash = tx.GetHash();
            if (pool.exists(hash))
                return false;

            // ----------- swiftTX transaction scanning -----------

            BOOST_FOREACH (const CTxIn& in, tx.vin) {
                if (mapLockedInputs.count(in.prevout)) {
                    if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                        return state.DoS(0,
                            error("AcceptableInputs : conflicts with existing transaction lock: %s", reason),
                            REJECT_INVALID, "tx-lock-conflict");
                    }
                }
            }

            // Check for conflicts with in-memory transactions
            if (!tx.IsZerocoinSpend()) {
                LOCK(pool.cs); // protect pool.mapNextTx
                for (unsigned int i = 0; i < tx.vin.size(); i++) {
                    COutPoint outpoint = tx.vin[i].prevout;
                    if (pool.mapNextTx.count(outpoint)) {
                        // Disable replacement feature for now
                        return false;
                    }
                }
            }


            {
                CCoinsView dummy;
                CCoinsViewCache view(&dummy);

                CAmount nValueIn = 0;
                {
                    LOCK(pool.cs);
                    CCoinsViewMemPool viewMemPool(pcoinsTip, pool);
                    view.SetBackend(viewMemPool);

                    // do we already have it?
                    if (view.HaveCoins(hash))
                        return false;

                    // do all inputs exist?
                    // Note that this does not check for the presence of actual outputs (see the next check for that),
                    // only helps filling in pfMissingInputs (to determine missing vs spent).
                    for (const CTxIn txin : tx.vin) {
                        if (!view.HaveCoins(txin.prevout.hash)) {
                            if (pfMissingInputs)
                                *pfMissingInputs = true;
                            return false;
                        }
                    }

                    // Check that zABET mints are not already known
                    if (tx.IsZerocoinMint()) {
                        for (auto& out : tx.vout) {
                            if (!out.IsZerocoinMint())
                                continue;

                            PublicCoin coin(Params().Zerocoin_Params());
                            if (!TxOutToPublicCoin(out, coin, state))
                                return state.Invalid(error("%s: failed final check of zerocoinmint for tx %s", __func__, tx.GetHash().GetHex()));

                            if (!ContextualCheckZerocoinMint(tx, coin, chainActive.Tip()))
                                return state.Invalid(error("%s: zerocoin mint failed contextual check", __func__));
                        }
                    }

                    // are the actual inputs available?
                    if (!view.HaveInputs(tx))
                        return state.Invalid(error("AcceptableInputs : inputs already spent"),
                            REJECT_DUPLICATE, "bad-txns-inputs-spent");

                    // Bring the best block into scope
                    view.GetBestBlock();

                    nValueIn = view.GetValueIn(tx);

                    // we have all inputs cached now, so switch back to dummy, so we don't need to keep lock on mempool
                    view.SetBackend(dummy);
                }

                // Check for non-standard pay-to-script-hash in inputs
                // for any real tx this will be checked on AcceptToMemoryPool anyway
                //        if (Params().RequireStandard() && !AreInputsStandard(tx, view))
                //            return error("AcceptableInputs: : nonstandard transaction input");

                // Check that the transaction doesn't have an excessive number of
                // sigops, making it impossible to mine. Since the coinbase transaction
                // itself can contain sigops MAX_TX_SIGOPS is less than
                // MAX_BLOCK_SIGOPS; we still consider this an invalid rather than
                // merely non-standard transaction.
                int64_t nSigOpsCost = GetTransactionSigOpCost(tx, view, STANDARD_SCRIPT_VERIFY_FLAGS);

                CAmount nValueOut = tx.GetValueOut();
                CAmount nFees = nValueIn - nValueOut;
                double dPriority = view.GetPriority(tx, chainActive.Height());

                CTxMemPoolEntry entry(tx, nFees, GetTime(), dPriority, chainActive.Height(), nSigOpsCost);

                unsigned int nSize = entry.GetTxSize();

                if ((nSigOpsCost > MAX_STANDARD_TX_SIGOPS_COST) || (nBytesPerSigOp && nSigOpsCost > nSize * WITNESS_SCALE_FACTOR / nBytesPerSigOp))
                    return state.DoS(0, false, REJECT_NONSTANDARD, "bad-txns-too-many-sigops");

                // Don't accept it if it can't get into a block
                // but prioritise dstx and don't check fees for it
                if (isDSTX) {
                    mempool.PrioritiseTransaction(hash, hash.ToString(), 1000, 0.1 * COIN);
                } else { // same as !ignoreFees for AcceptToMemoryPool
                    CAmount txMinFee = GetMinRelayFee(tx, nSize, true);
                    if (fLimitFree && nFees < txMinFee && !tx.IsZerocoinSpend())
                        return state.DoS(0, error("AcceptableInputs : not enough fees %s, %d < %d", hash.ToString(), nFees, txMinFee),
                            REJECT_INSUFFICIENTFEE, "insufficient fee");

                    // Require that free transactions have sufficient priority to be mined in the next block.
                    if (GetBoolArg("-relaypriority", true) && nFees < ::minRelayTxFee.GetFee(nSize) && !AllowFree(view.GetPriority(tx, chainActive.Height() + 1))) {
                        LogPrintf("%d\n", nFees);
                        LogPrintf("%d\n", ::minRelayTxFee.GetFee(nSize));
                        return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient priority");
                    }

                    // Continuously rate-limit free (really, very-low-fee) transactions
                    // This mitigates 'penny-flooding' -- sending thousands of free transactions just to
                    // be annoying or make others' transactions take longer to confirm.
                    if (fLimitFree && nFees < ::minRelayTxFee.GetFee(nSize) && !tx.IsZerocoinSpend()) {
                        static CCriticalSection csFreeLimiter;
                        static double dFreeCount;
                        static int64_t nLastTime;
                        int64_t nNow = GetTime();

                        LOCK(csFreeLimiter);

                        // Use an exponentially decaying ~10-minute window:
                        dFreeCount *= pow(1.0 - 1.0 / 600.0, (double)(nNow - nLastTime));
                        nLastTime = nNow;
                        // -limitfreerelay unit is thousand-bytes-per-minute
                        // At default rate it would take over a month to fill 1GB
                        if (dFreeCount >= GetArg("-limitfreerelay", 30) * 10 * 1000)
                            return state.DoS(0, error("AcceptableInputs : free transaction rejected by rate limiter"),
                                REJECT_INSUFFICIENTFEE, "rate limited free transaction");
                        LogPrint("mempool", "Rate limit dFreeCount: %g => %g\n", dFreeCount, dFreeCount + nSize);
                        dFreeCount += nSize;
                    }
                }

                if (fRejectInsaneFee && nFees > ::minRelayTxFee.GetFee(nSize) * 10000)
                    return error("AcceptableInputs: : insane fees %s, %d > %d",
                        hash.ToString(),
                        nFees, ::minRelayTxFee.GetFee(nSize) * 10000);

                // Check against previous transactions
                // This is done last to help prevent CPU exhaustion denial-of-service attacks.
                if (!CheckInputs(tx, state, view, false, STANDARD_SCRIPT_VERIFY_FLAGS, true)) {
                    return error("AcceptableInputs: : ConnectInputs failed %s", hash.ToString());
                }

                // Check again against just the consensus-critical mandatory script
                // verification flags, in case of bugs in the standard flags that cause
                // transactions to pass as valid when they're actually invalid. For
                // instance the STRICTENC flag was incorrectly allowing certain
                // CHECKSIG NOT scripts to pass, even though they were invalid.
                //
                // There is a similar check in CreateNewBlock() to prevent creating
                // invalid blocks, however allowing such transactions into the mempool
                // can be exploited as a DoS attack.
                // for any real tx this will be checked on AcceptToMemoryPool anyway
                //        if (!CheckInputs(tx, state, view, false, MANDATORY_SCRIPT_VERIFY_FLAGS, true))
                //        {
                //            return error("AcceptableInputs: : BUG! PLEASE REPORT THIS! ConnectInputs failed against MANDATORY but not STANDARD flags %s", hash.ToString());
                //        }

                // Store transaction in memory
                // pool.addUnchecked(hash, entry);
            }

            // SyncWithWallets(tx, NULL);

            return true;
        }

        /** Return transaction in tx, and if it was found inside a block, its hash is placed in hashBlock */
        bool GetTransaction(const uint256& hash, CTransaction& txOut, uint256& hashBlock, bool fAllowSlow)
        {
            CBlockIndex* pindexSlow = NULL;
            {
                LOCK(cs_main);
                {
                    if (mempool.lookup(hash, txOut)) {
                        return true;
                    }
                }

                if (fTxIndex) {
                    CDiskTxPos postx;
                    if (pblocktree->ReadTxIndex(hash, postx)) {
                        CAutoFile file(OpenBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
                        if (file.IsNull())
                            return error("%s: OpenBlockFile failed", __func__);
                        CBlockHeader header;
                        try {
                            file >> header;
                            fseek(file.Get(), postx.nTxOffset, SEEK_CUR);
                            file >> txOut;
                        } catch (std::exception& e) {
                            return error("%s : Deserialize or I/O error - %s", __func__, e.what());
                        }
                        hashBlock = header.GetHash();
                        if (txOut.GetHash() != hash)
                            return error("%s : txid mismatch", __func__);
                        return true;
                    }

                    // transaction not found in the index, nothing more can be done
                    return false;
                }

                if (fAllowSlow) { // use coin database to locate block that contains transaction, and scan it
                    int nHeight = -1;
                    {
                        CCoinsViewCache& view = *pcoinsTip;
                        const CCoins* coins = view.AccessCoins(hash);
                        if (coins)
                            nHeight = coins->nHeight;
                    }
                    if (nHeight > 0)
                        pindexSlow = chainActive[nHeight];
                }
            }

            if (pindexSlow) {
                CBlock block;
                if (ReadBlockFromDisk(block, pindexSlow)) {
                    BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                        if (tx.GetHash() == hash) {
                            txOut = tx;
                            hashBlock = pindexSlow->GetBlockHash();
                            return true;
                        }
                    }
                }
            }

            return false;
        }


        //////////////////////////////////////////////////////////////////////////////
        //
        // CBlock and CBlockIndex
        //

        bool WriteBlockToDisk(CBlock & block, CDiskBlockPos & pos)
        {
            // Open history file to append
            CAutoFile fileout(OpenBlockFile(pos), SER_DISK, CLIENT_VERSION);
            if (fileout.IsNull())
                return error("WriteBlockToDisk : OpenBlockFile failed");

            // Write index header
            unsigned int nSize = fileout.GetSerializeSize(block);
            fileout << FLATDATA(Params().MessageStart()) << nSize;

            // Write block
            long fileOutPos = ftell(fileout.Get());
            if (fileOutPos < 0)
                return error("WriteBlockToDisk : ftell failed");
            pos.nPos = (unsigned int)fileOutPos;
            fileout << block;

            return true;
        }

        bool ReadBlockFromDisk(CBlock & block, const CDiskBlockPos& pos)
        {
            block.SetNull();

            // Open history file to read
            CAutoFile filein(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION);
            if (filein.IsNull())
                return error("ReadBlockFromDisk : OpenBlockFile failed");

            // Read block
            try {
                filein >> block;
            } catch (std::exception& e) {
                return error("%s : Deserialize or I/O error - %s", __func__, e.what());
            }

            // Check the header
            if (block.IsProofOfWork()) {
                if (!CheckProofOfWork(block.GetHash(), block.nBits))
                    return error("ReadBlockFromDisk : Errors in block header");
            }

            return true;
        }

        bool ReadBlockFromDisk(CBlock & block, const CBlockIndex* pindex)
        {
            if (!ReadBlockFromDisk(block, pindex->GetBlockPos()))
                return false;
            if (block.GetHash() != pindex->GetBlockHash()) {
                LogPrintf("%s : block=%s index=%s\n", __func__, block.GetHash().ToString().c_str(), pindex->GetBlockHash().ToString().c_str());
                return error("ReadBlockFromDisk(CBlock&, CBlockIndex*) : GetHash() doesn't match index");
            }
            return true;
        }

        double ConvertBitsToDouble(unsigned int nBits)
        {
            int nShift = (nBits >> 24) & 0xff;

            double dDiff =
                (double)0x0000ffff / (double)(nBits & 0x00ffffff);

            while (nShift < 29) {
                dDiff *= 256.0;
                nShift++;
            }
            while (nShift > 29) {
                dDiff /= 256.0;
                nShift--;
            }

            return dDiff;
        }

        int64_t GetBlockValue(int nHeight)
        {
            int64_t nSubsidy = 0;

            if (IsTreasuryBlock(nHeight)) {
                LogPrintf("GetBlockValue(): this is a treasury block\n");
                nSubsidy = GetTreasuryAward(nHeight);

            } else {
                if (nHeight == 0) {
                    nSubsidy = 210000 * COIN;
                } else if (nHeight <= 1000) { //Before v1.1.0.0
                    nSubsidy = 0.1 * COIN;
                } else if (nHeight <= 21160) { //Before v1.1.0.0
                    nSubsidy = 0.7 * COIN;
                } else if (nHeight <= 31240) { //Before v1.1.0.0
                    nSubsidy = 2 * COIN;
                } else if (nHeight <= 41320) { //Before v1.1.0.0
                    nSubsidy = 2.5 * COIN;
                } else if (nHeight <= 51400 && nHeight > 41320) { // 7 days
                    nSubsidy = 3 * COIN;
                } else if (nHeight <= 61480 && nHeight > 51400) { // 7 days
                    nSubsidy = 3.5 * COIN;
                } else if (nHeight <= 71560 && nHeight > 61480) { // 7 days
                    nSubsidy = 4 * COIN;
                } else if (nHeight <= 81640 && nHeight > 71560) { // 7 days
                    nSubsidy = 4.5 * COIN;
                } else if (nHeight <= 91720 && nHeight > 81640) { // 7 days
                    nSubsidy = 5 * COIN;
                } else if (nHeight <= 101800 && nHeight > 91720) { // 7 days
                    nSubsidy = 5.5 * COIN;
                } else if (nHeight <= 111880 && nHeight > 101800) { // 7 days
                    nSubsidy = 6 * COIN;
                } else if (nHeight <= 121960 && nHeight > 111880) { // 7 days
                    nSubsidy = 6.5 * COIN;
                } else if (nHeight <= 132040 && nHeight > 121960) { // 7 days
                    nSubsidy = 7 * COIN;
                } else if (nHeight <= 142120 && nHeight > 132040) { // 7 days
                    nSubsidy = 7.5 * COIN;
                } else if (nHeight <= 152200 && nHeight > 142120) { // 7 days
                    nSubsidy = 8 * COIN;
                } else if (nHeight <= 162280 && nHeight > 152200) { // 7 days
                    nSubsidy = 8.5 * COIN;
                } else if (nHeight <= 172360 && nHeight > 162280) { // 7 days
                    nSubsidy = 9 * COIN;
                } else if (nHeight <= 182440 && nHeight > 172360) { // 7 days
                    nSubsidy = 9.5 * COIN;
                } else if (nHeight <= 192020 && nHeight > 182440) { // 7 days
                    nSubsidy = 10 * COIN;
                } else if (nHeight <= 212180 && nHeight > 192020) { // 14 days
                    nSubsidy = 9.75 * COIN;
                } else if (nHeight <= 232340 && nHeight > 212180) { // 14 days
                    nSubsidy = 9.5 * COIN;
                } else if (nHeight <= 252500 && nHeight > 232340) { // 14 days  This is when v2.0 will be forked
                    nSubsidy = 9.25 * COIN;
                } else if (nHeight <= 272660 && nHeight > 252500) { // 14 days  Start of the new rewards
                    nSubsidy = 20 * COIN;
                } else if (nHeight <= 292820 && nHeight > 272660) { // 14 days
                    nSubsidy = 22 * COIN;
                } else if (nHeight <= 312980 && nHeight > 292820) { // 14 days
                    nSubsidy = 24 * COIN;
                } else if (nHeight <= 333140 && nHeight > 312980) { // 14 days
                    nSubsidy = 26 * COIN;
                } else if (nHeight <= 353300 && nHeight > 333140) { // 14 days
                    nSubsidy = 28 * COIN;
                } else if (nHeight <= 373460 && nHeight > 353300) { // 14 days  Peak of rewards 
                    nSubsidy = 30 * COIN;
                } else if (nHeight <= 393620 && nHeight > 373460) { // 14 days
                    nSubsidy = 29.5 * COIN;
                } else if (nHeight <= 413780 && nHeight > 393620) { // 14 days
                    nSubsidy = 29 * COIN;
                } else if (nHeight <= 433940 && nHeight > 413780) { // 14 days
                    nSubsidy = 28.5 * COIN;
                } else if (nHeight <= 454100 && nHeight > 433940) { // 14 days
                    nSubsidy = 28 * COIN;
                } else if (nHeight <= 474260 && nHeight > 454100) { // 14 days
                    nSubsidy = 27.5 * COIN;
                } else if (nHeight <= 494420 && nHeight > 474260) { // 14 days
                    nSubsidy = 27 * COIN;
                } else if (nHeight <= 514580 && nHeight > 494420) { // 14 days
                    nSubsidy = 26.5 * COIN;
                } else if (nHeight <= 534740 && nHeight > 514580) { // 14 days
                    nSubsidy = 26 * COIN;
                } else if (nHeight <= 554900 && nHeight > 534740) { // 14 days
                    nSubsidy = 25.5 * COIN;
                } else if (nHeight <= 575060 && nHeight > 554900) { // 14 days
                    nSubsidy = 25 * COIN;
                } else if (nHeight <= 618260 && nHeight > 575060) { // 30 days
                    nSubsidy = 20 * COIN;
                } else if (nHeight <= 661460 && nHeight > 618260) { // 30 days
                    nSubsidy = 10 * COIN;
                } else if (nHeight <= 791060 && nHeight > 661460) { // 90 days
                    nSubsidy = 9 * COIN;
                } else if (nHeight <= 920660 && nHeight > 791060) { // 90 days
                    nSubsidy = 8 * COIN;
                } else if (nHeight <= 1179860 && nHeight > 920660) { // 180 days
                    nSubsidy = 7 * COIN;
                } else if (nHeight <= 1439060 && nHeight > 1179860) { // 180 days
                    nSubsidy = 6 * COIN;
                } else if (nHeight <= 1957460 && nHeight > 1439060) { // 360 days
                    nSubsidy = 3 * COIN;
                } else if (nHeight  > 1957460) { // Till Max Supply Is Reached
                    nSubsidy = 1.5 * COIN;
                }
                // Check if we reached the coin max supply.
                int64_t nMoneySupply = chainActive.Tip()->nMoneySupply;
                if (nMoneySupply + nSubsidy >= Params().MaxMoneyOut())
                    nSubsidy = Params().MaxMoneyOut() - nMoneySupply;
                if (nMoneySupply >= Params().MaxMoneyOut())
                    nSubsidy = 0;
                return nSubsidy;
            }
            return nSubsidy;
        }

        int64_t GetMasternodePayment(int nHeight, int64_t blockValue, int nMasternodeCount)
        {
            int64_t ret = 0;

            if (nHeight < 101) {
                ret = blockValue * 0;
            } else if (nHeight <= 192021 && nHeight > 101) {
                ret = blockValue * 0.8; //80% for nodes
            } else if (nHeight > 192021) {
                ret = blockValue * 0.9; //90% for nodes
            }

            return ret;
        }

        //Treasury blocks start from 192021 and then each 1440 block
        int nStartTreasuryBlock = 192021;
        int nTreasuryBlockStep = 1440;


        bool IsTreasuryBlock(int nHeight)
        {
            // Spork to allow dev fee to be turned on and off
            // If spork is on dev fee is turned off
            if (nHeight < nStartTreasuryBlock)
                return false;
            else if (IsSporkActive(SPORK_21_TREASURY_PAYMENT_ENFORCEMENT))
                return false;
            else if ((nHeight - nStartTreasuryBlock) % nTreasuryBlockStep == 0)
                return true;
            else
                return false;
        }

        int64_t GetTreasuryAward(int nHeight)
        {
            if (IsTreasuryBlock(nHeight)) {
                if (nHeight <= 212180 && nHeight > 192020) { // 14 days
                    return 702 * COIN;
                } else if (nHeight <= 232340 && nHeight > 212180) { // 14 days
                    return 684 * COIN;
                } else if (nHeight <= 252500 && nHeight > 232340) { // 14 days
                    return 666 * COIN;
                } else if (nHeight <= 272660 && nHeight > 252500) { // 14 days
                    return 1440 * COIN;
                } else if (nHeight <= 292820 && nHeight > 272660) { // 14 days
                    return 1584 * COIN;
                } else if (nHeight <= 312980 && nHeight > 292820) { // 14 days
                    return 1728 * COIN;
                } else if (nHeight <= 333140 && nHeight > 312980) { // 14 days
                    return 1872 * COIN;
                } else if (nHeight <= 353300 && nHeight > 333140) { // 14 days
                    return 2016 * COIN;
                } else if (nHeight <= 373460 && nHeight > 353300) { // 14 days 
                    return 2160 * COIN;
                } else if (nHeight <= 393620 && nHeight > 373460) { // 14 days
                    return 2124 * COIN;
                } else if (nHeight <= 413780 && nHeight > 393620) { // 14 days
                    return 2088 * COIN;
                } else if (nHeight <= 433940 && nHeight > 413780) { // 14 days
                    return 2052 * COIN;
                } else if (nHeight <= 454100 && nHeight > 433940) { // 14 days
                    return 2016 * COIN;
                } else if (nHeight <= 474260 && nHeight > 454100) { // 14 days
                    return 1980 * COIN;
                } else if (nHeight <= 494420 && nHeight > 474260) { // 14 days
                    return 1944 * COIN;
                } else if (nHeight <= 514580 && nHeight > 494420) { // 14 days
                    return 1908 * COIN;
                } else if (nHeight <= 534740 && nHeight > 514580) { // 14 days
                    return 1872 * COIN;
                } else if (nHeight <= 554900 && nHeight > 534740) { // 14 days
                    return 1836 * COIN;
                } else if (nHeight <= 575060 && nHeight > 554900) { // 14 days
                    return 1800 * COIN;
                } else if (nHeight <= 618260 && nHeight > 575060) { // 30 days
                    return 1440 * COIN;
                } else if (nHeight <= 661460 && nHeight > 618260) { // 30 days
                    return 720 * COIN;
                } else if (nHeight <= 791060 && nHeight > 661460) { // 90 days
                    return 648 * COIN;
                } else if (nHeight <= 920660 && nHeight > 791060) { // 90 days
                    return 576 * COIN;
                } else if (nHeight <= 1179860 && nHeight > 920660) { // 180 days
                    return 504 * COIN;
                } else if (nHeight <= 1439060 && nHeight > 1179860) { // 180 days
                    return 432 * COIN;
                } else if (nHeight <= 1957460 && nHeight > 1439060) { // 360 days
                    return 216 * COIN;
                } else if (nHeight  > 1957460) { // Till Max Supply Is Reached
                    return 108 * COIN;
                } else
                    return 108;
            } else
                return 0;
        }

        bool IsInitialBlockDownload()
        {
            LOCK(cs_main);
            if (fImporting || fReindex || fVerifyingBlocks || chainActive.Height() < Checkpoints::GetTotalBlocksEstimate())
                return true;
            static bool lockIBDState = false;
            if (lockIBDState)
                return false;
            bool state = (chainActive.Height() < pindexBestHeader->nHeight - 24 * 6 ||
                          pindexBestHeader->GetBlockTime() < GetTime() - 6 * 60 * 60); // ~144 blocks behind -> 2 x fork detection time
            if (!state)
                lockIBDState = true;
            return state;
        }

        bool fLargeWorkForkFound = false;
        bool fLargeWorkInvalidChainFound = false;
        CBlockIndex *pindexBestForkTip = NULL, *pindexBestForkBase = NULL;

        void CheckForkWarningConditions()
        {
            AssertLockHeld(cs_main);
            // Before we get past initial download, we cannot reliably alert about forks
            // (we assume we don't get stuck on a fork before the last checkpoint)
            if (IsInitialBlockDownload())
                return;

            // If our best fork is no longer within 72 blocks (+/- 3 hours if no one mines it)
            // of our head, drop it
            if (pindexBestForkTip && chainActive.Height() - pindexBestForkTip->nHeight >= 72)
                pindexBestForkTip = NULL;

            if (pindexBestForkTip || (pindexBestInvalid && pindexBestInvalid->nChainWork > chainActive.Tip()->nChainWork + (GetBlockProof(*chainActive.Tip()) * 6))) {
                if (!fLargeWorkForkFound && pindexBestForkBase) {
                    if (pindexBestForkBase->phashBlock) {
                        std::string warning = std::string("'Warning: Large-work fork detected, forking after block ") +
                                              pindexBestForkBase->phashBlock->ToString() + std::string("'");
                        CAlert::Notify(warning, true);
                    }
                }
                if (pindexBestForkTip && pindexBestForkBase) {
                    if (pindexBestForkBase->phashBlock) {
                        LogPrintf("CheckForkWarningConditions: Warning: Large valid fork found\n  forking the chain at height %d (%s)\n  lasting to height %d (%s).\nChain state database corruption likely.\n",
                            pindexBestForkBase->nHeight, pindexBestForkBase->phashBlock->ToString(),
                            pindexBestForkTip->nHeight, pindexBestForkTip->phashBlock->ToString());
                        fLargeWorkForkFound = true;
                    }
                } else {
                    LogPrintf("CheckForkWarningConditions: Warning: Found invalid chain at least ~6 blocks longer than our best chain.\nChain state database corruption likely.\n");
                    fLargeWorkInvalidChainFound = true;
                }
            } else {
                fLargeWorkForkFound = false;
                fLargeWorkInvalidChainFound = false;
            }
        }

        void CheckForkWarningConditionsOnNewFork(CBlockIndex * pindexNewForkTip)
        {
            AssertLockHeld(cs_main);
            // If we are on a fork that is sufficiently large, set a warning flag
            CBlockIndex* pfork = pindexNewForkTip;
            CBlockIndex* plonger = chainActive.Tip();
            while (pfork && pfork != plonger) {
                while (plonger && plonger->nHeight > pfork->nHeight)
                    plonger = plonger->pprev;
                if (pfork == plonger)
                    break;
                pfork = pfork->pprev;
            }

            // We define a condition which we should warn the user about as a fork of at least 7 blocks
            // who's tip is within 72 blocks (+/- 3 hours if no one mines it) of ours
            // or a chain that is entirely longer than ours and invalid (note that this should be detected by both)
            // We use 7 blocks rather arbitrarily as it represents just under 10% of sustained network
            // hash rate operating on the fork.
            // We define it this way because it allows us to only store the highest fork tip (+ base) which meets
            // the 7-block condition and from this always have the most-likely-to-cause-warning fork
            if (pfork && (!pindexBestForkTip || (pindexBestForkTip && pindexNewForkTip->nHeight > pindexBestForkTip->nHeight)) &&
                pindexNewForkTip->nChainWork - pfork->nChainWork > (GetBlockProof(*pfork) * 7) &&
                chainActive.Height() - pindexNewForkTip->nHeight < 72) {
                pindexBestForkTip = pindexNewForkTip;
                pindexBestForkBase = pfork;
            }

            CheckForkWarningConditions();
        }

        // Requires cs_main.
        void Misbehaving(NodeId pnode, int howmuch)
        {
            if (howmuch == 0)
                return;

            CNodeState* state = State(pnode);
            if (state == NULL)
                return;

            state->nMisbehavior += howmuch;
            int banscore = GetArg("-banscore", 100);
            if (state->nMisbehavior >= banscore && state->nMisbehavior - howmuch < banscore) {
                LogPrintf("Misbehaving: %s (%d -> %d) BAN THRESHOLD EXCEEDED\n", state->name, state->nMisbehavior - howmuch, state->nMisbehavior);
                state->fShouldBan = true;
            } else
                LogPrintf("Misbehaving: %s (%d -> %d)\n", state->name, state->nMisbehavior - howmuch, state->nMisbehavior);
        }

        void static InvalidChainFound(CBlockIndex * pindexNew)
        {
            if (!pindexBestInvalid || pindexNew->nChainWork > pindexBestInvalid->nChainWork)
                pindexBestInvalid = pindexNew;

            LogPrintf("InvalidChainFound: invalid block=%s  height=%d  log2_work=%.8g  date=%s\n",
                pindexNew->GetBlockHash().ToString(), pindexNew->nHeight,
                log(pindexNew->nChainWork.getdouble()) / log(2.0), DateTimeStrFormat("%Y-%m-%d %H:%M:%S", pindexNew->GetBlockTime()));
            LogPrintf("InvalidChainFound:  current best=%s  height=%d  log2_work=%.8g  date=%s\n",
                chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(), log(chainActive.Tip()->nChainWork.getdouble()) / log(2.0),
                DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()));
            CheckForkWarningConditions();
        }

        void static InvalidBlockFound(CBlockIndex * pindex, const CValidationState& state)
        {
            int nDoS = 0;
            if (state.IsInvalid(nDoS)) {
                std::map<uint256, NodeId>::iterator it = mapBlockSource.find(pindex->GetBlockHash());
                if (it != mapBlockSource.end() && State(it->second)) {
                    CBlockReject reject = {state.GetRejectCode(), state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), pindex->GetBlockHash()};
                    State(it->second)->rejects.push_back(reject);
                    if (nDoS > 0)
                        Misbehaving(it->second, nDoS);
                }
            }
            if (!state.CorruptionPossible()) {
                pindex->nStatus |= BLOCK_FAILED_VALID;
                setDirtyBlockIndex.insert(pindex);
                setBlockIndexCandidates.erase(pindex);
                InvalidChainFound(pindex);
            }
        }

        void UpdateCoins(const CTransaction& tx, CValidationState& state, CCoinsViewCache& inputs, CTxUndo& txundo, int nHeight)
        {
            // mark inputs spent
            if (!tx.IsCoinBase() && !tx.IsZerocoinSpend()) {
                txundo.vprevout.reserve(tx.vin.size());
                BOOST_FOREACH (const CTxIn& txin, tx.vin) {
                    txundo.vprevout.push_back(CTxInUndo());
                    bool ret = inputs.ModifyCoins(txin.prevout.hash)->Spend(txin.prevout, txundo.vprevout.back());
                    assert(ret);
                }
            }

            // add outputs
            inputs.ModifyCoins(tx.GetHash())->FromTx(tx, nHeight);
        }

        bool CScriptCheck::operator()()
        {
            const CScript& scriptSig = ptxTo->vin[nIn].scriptSig;
            const CScriptWitness* witness = (nIn < ptxTo->wit.vtxinwit.size()) ? &ptxTo->wit.vtxinwit[nIn].scriptWitness : NULL;
            if (!VerifyScript(scriptSig, scriptPubKey, witness, nFlags, CachingTransactionSignatureChecker(ptxTo, nIn, amount, cacheStore), &error)) {
                return ::error("CScriptCheck(): %s:%d VerifySignature failed: %s", ptxTo->GetHash().ToString(), nIn, ScriptErrorString(error));
            }
            return true;
        }

        bool CheckInputs(const CTransaction& tx, CValidationState& state, const CCoinsViewCache& inputs, bool fScriptChecks, unsigned int flags, bool cacheStore, std::vector<CScriptCheck>* pvChecks)
        {
            if (!tx.IsCoinBase() && !tx.IsZerocoinSpend()) {
                if (pvChecks)
                    pvChecks->reserve(tx.vin.size());

                // This doesn't trigger the DoS code on purpose; if it did, it would make it easier
                // for an attacker to attempt to split the network.
                if (!inputs.HaveInputs(tx))
                    return state.Invalid(error("CheckInputs() : %s inputs unavailable", tx.GetHash().ToString()));

                // While checking, GetBestBlock() refers to the parent block.
                // This is also true for mempool checks.
                CBlockIndex* pindexPrev = mapBlockIndex.find(inputs.GetBestBlock())->second;
                int nSpendHeight = pindexPrev->nHeight + 1;
                CAmount nValueIn = 0;
                CAmount nFees = 0;
                for (unsigned int i = 0; i < tx.vin.size(); i++) {
                    const COutPoint& prevout = tx.vin[i].prevout;
                    const CCoins* coins = inputs.AccessCoins(prevout.hash);
                    assert(coins);

                    // If prev is coinbase, check that it's matured
                    if (coins->IsCoinBase() || coins->IsCoinStake()) {
                        if (nSpendHeight - coins->nHeight < Params().COINBASE_MATURITY())
                            return state.Invalid(
                                error("CheckInputs() : tried to spend coinbase at depth %d, coinstake=%d", nSpendHeight - coins->nHeight, coins->IsCoinStake()),
                                REJECT_INVALID, "bad-txns-premature-spend-of-coinbase");
                    }

                    // Check for negative or overflow input values
                    nValueIn += coins->vout[prevout.n].nValue;
                    if (!MoneyRange(coins->vout[prevout.n].nValue) || !MoneyRange(nValueIn))
                        return state.DoS(100, error("CheckInputs() : txin values out of range"),
                            REJECT_INVALID, "bad-txns-inputvalues-outofrange");
                }

                if (!tx.IsCoinStake()) {
                    if (nValueIn < tx.GetValueOut())
                        return state.DoS(100, error("CheckInputs() : %s value in (%s) < value out (%s)", tx.GetHash().ToString(), FormatMoney(nValueIn), FormatMoney(tx.GetValueOut())),
                            REJECT_INVALID, "bad-txns-in-belowout");

                    // Tally transaction fees
                    CAmount nTxFee = nValueIn - tx.GetValueOut();
                    if (nTxFee < 0)
                        return state.DoS(100, error("CheckInputs() : %s nTxFee < 0", tx.GetHash().ToString()),
                            REJECT_INVALID, "bad-txns-fee-negative");
                    nFees += nTxFee;
                    if (!MoneyRange(nFees))
                        return state.DoS(100, error("CheckInputs() : nFees out of range"),
                            REJECT_INVALID, "bad-txns-fee-outofrange");
                }
                // The first loop above does all the inexpensive checks.
                // Only if ALL inputs pass do we perform expensive ECDSA signature checks.
                // Helps prevent CPU exhaustion attacks.

                // Skip ECDSA signature verification when connecting blocks
                // before the last block chain checkpoint. This is safe because block merkle hashes are
                // still computed and checked, and any change will be caught at the next checkpoint.
                if (fScriptChecks) {
                    for (unsigned int i = 0; i < tx.vin.size(); i++) {
                        const COutPoint& prevout = tx.vin[i].prevout;
                        const CCoins* coins = inputs.AccessCoins(prevout.hash);
                        assert(coins);

                        // Verify signature
                        CScriptCheck check(*coins, tx, i, flags, cacheStore);
                        if (pvChecks) {
                            pvChecks->push_back(CScriptCheck());
                            check.swap(pvChecks->back());
                        } else if (!check()) {
                            if (flags & STANDARD_NOT_MANDATORY_VERIFY_FLAGS) {
                                // Check whether the failure was caused by a
                                // non-mandatory script verification check, such as
                                // non-standard DER encodings or non-null dummy
                                // arguments; if so, don't trigger DoS protection to
                                // avoid splitting the network between upgraded and
                                // non-upgraded nodes.
                                CScriptCheck check2(*coins, tx, i,
                                    flags & ~STANDARD_NOT_MANDATORY_VERIFY_FLAGS, cacheStore);
                                if (check2())
                                    return state.Invalid(false, REJECT_NONSTANDARD, strprintf("non-mandatory-script-verify-flag (%s)", ScriptErrorString(check.GetScriptError())));
                            }
                            // Failures of other flags indicate a transaction that is
                            // invalid in new blocks, e.g. a invalid P2SH. We DoS ban
                            // such nodes as they are not following the protocol. That
                            // said during an upgrade careful thought should be taken
                            // as to the correct behavior - we may want to continue
                            // peering with non-upgraded nodes even after a soft-fork
                            // super-majority vote has passed.
                            return state.DoS(100, false, REJECT_INVALID, strprintf("mandatory-script-verify-flag-failed (%s)", ScriptErrorString(check.GetScriptError())));
                        }
                    }
                }
            }

            return true;
        }

        bool DisconnectBlock(CBlock & block, CValidationState & state, CBlockIndex * pindex, CCoinsViewCache & view, bool* pfClean)
        {
            if (pindex->GetBlockHash() != view.GetBestBlock())
                LogPrintf("%s : pindex=%s view=%s\n", __func__, pindex->GetBlockHash().GetHex(), view.GetBestBlock().GetHex());
            assert(pindex->GetBlockHash() == view.GetBestBlock());

            if (pfClean)
                *pfClean = false;

            bool fClean = true;

            CBlockUndo blockUndo;
            CDiskBlockPos pos = pindex->GetUndoPos();
            if (pos.IsNull())
                return error("DisconnectBlock() : no undo data available");
            if (!blockUndo.ReadFromDisk(pos, pindex->pprev->GetBlockHash()))
                return error("DisconnectBlock() : failure reading undo data");

            if (blockUndo.vtxundo.size() + 1 != block.vtx.size())
                return error("DisconnectBlock() : block and undo data inconsistent");

            // undo transactions in reverse order
            for (int i = block.vtx.size() - 1; i >= 0; i--) {
                const CTransaction& tx = block.vtx[i];

                /** UNDO ZEROCOIN DATABASING
         * note we only undo zerocoin databasing in the following statement, value to and from Altbet
         * addresses should still be handled by the typical bitcoin based undo code
         * */
                if (tx.ContainsZerocoins()) {
                    if (tx.IsZerocoinSpend()) {
                        //erase all zerocoinspends in this transaction
                        for (const CTxIn txin : tx.vin) {
                            if (txin.scriptSig.IsZerocoinSpend()) {
                                CoinSpend spend = TxInToZerocoinSpend(txin);
                                if (!zerocoinDB->EraseCoinSpend(spend.getCoinSerialNumber()))
                                    return error("failed to erase spent zerocoin in block");
                            }
                        }
                    }
                    if (tx.IsZerocoinMint()) {
                        //erase all zerocoinmints in this transaction
                        for (const CTxOut txout : tx.vout) {
                            if (txout.scriptPubKey.empty() || !txout.scriptPubKey.IsZerocoinMint())
                                continue;


                            PublicCoin pubCoin(Params().Zerocoin_Params());
                            if (!TxOutToPublicCoin(txout, pubCoin, state))
                                return error("DisconnectBlock(): TxOutToPublicCoin() failed");

                            if (!zerocoinDB->EraseCoinMint(pubCoin.getValue()))
                                return error("DisconnectBlock(): Failed to erase coin mint");
                        }
                    }
                }

                uint256 hash = tx.GetHash();

                // Check that all outputs are available and match the outputs in the block itself
                // exactly. Note that transactions with only provably unspendable outputs won't
                // have outputs available even in the block itself, so we handle that case
                // specially with outsEmpty.
                {
                    CCoins outsEmpty;
                    CCoinsModifier outs = view.ModifyCoins(hash);
                    outs->ClearUnspendable();

                    CCoins outsBlock(tx, pindex->nHeight);
                    // The CCoins serialization does not serialize negative numbers.
                    // No network rules currently depend on the version here, so an inconsistency is harmless
                    // but it must be corrected before txout nversion ever influences a network rule.
                    if (outsBlock.nVersion < 0)
                        outs->nVersion = outsBlock.nVersion;
                    if (*outs != outsBlock)
                        fClean = fClean && error("DisconnectBlock() : added transaction mismatch? database corrupted");

                    // remove outputs
                    outs->Clear();
                }

                // restore inputs
                if (!tx.IsCoinBase() && !tx.IsZerocoinSpend()) { // not coinbases or zerocoinspend because they dont have traditional inputs
                    const CTxUndo& txundo = blockUndo.vtxundo[i - 1];
                    if (txundo.vprevout.size() != tx.vin.size())
                        return error("DisconnectBlock() : transaction and undo data inconsistent - txundo.vprevout.siz=%d tx.vin.siz=%d", txundo.vprevout.size(), tx.vin.size());
                    for (unsigned int j = tx.vin.size(); j-- > 0;) {
                        const COutPoint& out = tx.vin[j].prevout;
                        const CTxInUndo& undo = txundo.vprevout[j];
                        CCoinsModifier coins = view.ModifyCoins(out.hash);
                        if (undo.nHeight != 0) {
                            // undo data contains height: this is the last output of the prevout tx being spent
                            if (!coins->IsPruned())
                                fClean = fClean && error("DisconnectBlock() : undo data overwriting existing transaction");
                            coins->Clear();
                            coins->fCoinBase = undo.fCoinBase;
                            coins->nHeight = undo.nHeight;
                            coins->nVersion = undo.nVersion;
                        } else {
                            if (coins->IsPruned())
                                fClean = fClean && error("DisconnectBlock() : undo data adding output to missing transaction");
                        }
                        if (coins->IsAvailable(out.n))
                            fClean = fClean && error("DisconnectBlock() : undo data overwriting existing output");
                        if (coins->vout.size() < out.n + 1)
                            coins->vout.resize(out.n + 1);
                        coins->vout[out.n] = undo.txout;

                        // erase the spent input
                        mapStakeSpent.erase(out);
                    }
                }
            }

            // move best block pointer to prevout block
            view.SetBestBlock(pindex->pprev->GetBlockHash());

            if (!fVerifyingBlocks) {
                //if block is an accumulator checkpoint block, remove checkpoint and checksums from db
                uint256 nCheckpoint = pindex->nAccumulatorCheckpoint;
                if (nCheckpoint != pindex->pprev->nAccumulatorCheckpoint) {
                    if (!EraseAccumulatorValues(nCheckpoint, pindex->pprev->nAccumulatorCheckpoint))
                        return error("DisconnectBlock(): failed to erase checkpoint");
                }
            }

            if (pfClean) {
                *pfClean = fClean;
                return true;
            } else {
                return fClean;
            }
        }

        void static FlushBlockFile(bool fFinalize = false)
        {
            LOCK(cs_LastBlockFile);

            CDiskBlockPos posOld(nLastBlockFile, 0);

            FILE* fileOld = OpenBlockFile(posOld);
            if (fileOld) {
                if (fFinalize)
                    TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nSize);
                FileCommit(fileOld);
                fclose(fileOld);
            }

            fileOld = OpenUndoFile(posOld);
            if (fileOld) {
                if (fFinalize)
                    TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nUndoSize);
                FileCommit(fileOld);
                fclose(fileOld);
            }
        }

        bool FindUndoPos(CValidationState & state, int nFile, CDiskBlockPos& pos, unsigned int nAddSize);

        static CCheckQueue<CScriptCheck> scriptcheckqueue(128);

        void ThreadScriptCheck()
        {
            RenameThread("altbet-scriptch");
            scriptcheckqueue.Thread();
        }

        void RecalculateZABETMinted()
        {
            CBlockIndex* pindex = chainActive[Params().Zerocoin_StartHeight()];
            int nHeightEnd = chainActive.Height();
            while (true) {
                if (pindex->nHeight % 1000 == 0)
                    LogPrintf("%s : block %d...\n", __func__, pindex->nHeight);

                //overwrite possibly wrong vMintsInBlock data
                CBlock block;
                assert(ReadBlockFromDisk(block, pindex));

                std::list<CZerocoinMint> listMints;
                BlockToZerocoinMintList(block, listMints);

                vector<libzerocoin::CoinDenomination> vDenomsBefore = pindex->vMintDenominationsInBlock;
                pindex->vMintDenominationsInBlock.clear();
                for (auto mint : listMints)
                    pindex->vMintDenominationsInBlock.emplace_back(mint.GetDenomination());

                if (pindex->nHeight < nHeightEnd)
                    pindex = chainActive.Next(pindex);
                else
                    break;
            }
        }

        void RecalculateZABETSpent()
        {
            CBlockIndex* pindex = chainActive[Params().Zerocoin_StartHeight()];
            while (true) {
                if (pindex->nHeight % 1000 == 0)
                    LogPrintf("%s : block %d...\n", __func__, pindex->nHeight);

                //Rewrite zABET supply
                CBlock block;
                assert(ReadBlockFromDisk(block, pindex));

                list<libzerocoin::CoinDenomination> listDenomsSpent = ZerocoinSpendListFromBlock(block);

                //Reset the supply to previous block
                pindex->mapZerocoinSupply = pindex->pprev->mapZerocoinSupply;

                //Add mints to zABET supply
                for (auto denom : libzerocoin::zerocoinDenomList) {
                    long nDenomAdded = count(pindex->vMintDenominationsInBlock.begin(), pindex->vMintDenominationsInBlock.end(), denom);
                    pindex->mapZerocoinSupply.at(denom) += nDenomAdded;
                }

                //Remove spends from zABET supply
                for (auto denom : listDenomsSpent)
                    pindex->mapZerocoinSupply.at(denom)--;

                //Rewrite money supply
                assert(pblocktree->WriteBlockIndex(CDiskBlockIndex(pindex)));

                if (pindex->nHeight < chainActive.Height())
                    pindex = chainActive.Next(pindex);
                else
                    break;
            }
        }

        bool RecalculateABETSupply(int nHeightStart)
        {
            if (nHeightStart > chainActive.Height())
                return false;

            CBlockIndex* pindex = chainActive[nHeightStart];
            CAmount nSupplyPrev = pindex->pprev->nMoneySupply;
            if (nHeightStart == Params().Zerocoin_StartHeight())
                nSupplyPrev = CAmount(1880313101204990);

            while (true) {
                if (pindex->nHeight % 1000 == 0)
                    LogPrintf("%s : block %d...\n", __func__, pindex->nHeight);

                CBlock block;
                assert(ReadBlockFromDisk(block, pindex));

                CAmount nValueIn = 0;
                CAmount nValueOut = 0;
                for (const CTransaction tx : block.vtx) {
                    for (unsigned int i = 0; i < tx.vin.size(); i++) {
                        if (tx.IsCoinBase())
                            break;

                        if (tx.vin[i].scriptSig.IsZerocoinSpend()) {
                            nValueIn += tx.vin[i].nSequence * COIN;
                            continue;
                        }

                        COutPoint prevout = tx.vin[i].prevout;
                        CTransaction txPrev;
                        uint256 hashBlock;
                        assert(GetTransaction(prevout.hash, txPrev, hashBlock, true));
                        nValueIn += txPrev.vout[prevout.n].nValue;
                    }

                    for (unsigned int i = 0; i < tx.vout.size(); i++) {
                        if (i == 0 && tx.IsCoinStake())
                            continue;

                        nValueOut += tx.vout[i].nValue;
                    }
                }

                // Rewrite money supply
                pindex->nMoneySupply = nSupplyPrev + nValueOut - nValueIn;
                nSupplyPrev = pindex->nMoneySupply;

                assert(pblocktree->WriteBlockIndex(CDiskBlockIndex(pindex)));

                if (pindex->nHeight < chainActive.Height())
                    pindex = chainActive.Next(pindex);
                else
                    break;
            }
            return true;
        }

        bool ReindexAccumulators(list<uint256> & listMissingCheckpoints, string & strError)
        {
            // Altbet: recalculate Accumulator Checkpoints that failed to database properly
            if (!listMissingCheckpoints.empty() && chainActive.Height() >= Params().Zerocoin_StartHeight()) {
                //uiInterface.InitMessage(_("Calculating missing accumulators..."));
                LogPrintf("%s : finding missing checkpoints\n", __func__);

                //search the chain to see when zerocoin started
                int nZerocoinStart = Params().Zerocoin_LastOldParams() + 1;

                // find each checkpoint that is missing
                CBlockIndex* pindex = chainActive[nZerocoinStart];
                while (pindex) {
                    if (ShutdownRequested())
                        return false;

                    // find checkpoints by iterating through the blockchain beginning with the first zerocoin block
                    if (pindex->nAccumulatorCheckpoint != pindex->pprev->nAccumulatorCheckpoint) {
                        if (find(listMissingCheckpoints.begin(), listMissingCheckpoints.end(), pindex->nAccumulatorCheckpoint) != listMissingCheckpoints.end()) {
                            uint256 nCheckpointCalculated = 0;
                            AccumulatorMap mapAccumulators(Params().Zerocoin_Params());
                            if (!CalculateAccumulatorCheckpoint(pindex->nHeight, nCheckpointCalculated, mapAccumulators)) {
                                // GetCheckpoint could have terminated due to a shutdown request. Check this here.
                                if (ShutdownRequested())
                                    break;
                                strError = _("Failed to calculate accumulator checkpoint");
                                return error("%s: %s", __func__, strError);
                            }

                            //check that the calculated checkpoint is what is in the index.
                            if (nCheckpointCalculated != pindex->nAccumulatorCheckpoint) {
                                LogPrintf("%s : height=%d calculated_checkpoint=%s actual=%s\n", __func__, pindex->nHeight, nCheckpointCalculated.GetHex(), pindex->nAccumulatorCheckpoint.GetHex());
                                strError = _("Calculated accumulator checkpoint is not what is recorded by block index");
                                return error("%s: %s", __func__, strError);
                            }

                            DatabaseChecksums(mapAccumulators);
                            auto it = find(listMissingCheckpoints.begin(), listMissingCheckpoints.end(), pindex->nAccumulatorCheckpoint);
                            listMissingCheckpoints.erase(it);
                        }
                    }

                    // if we have iterated to the end of the blockchain, then checkpoints should be in sync
                    pindex = chainActive.Next(pindex);
                }
            }
            return true;
        }

        bool UpdateZABETSupply(const CBlock& block, CBlockIndex* pindex)
        {
            std::list<CZerocoinMint> listMints;
            BlockToZerocoinMintList(block, listMints);
            std::list<libzerocoin::CoinDenomination> listSpends = ZerocoinSpendListFromBlock(block);

            // Initialize zerocoin supply to the supply from previous block
            if (pindex->pprev && pindex->pprev->GetBlockHeader().nVersion > 3) {
                for (auto& denom : zerocoinDenomList) {
                    pindex->mapZerocoinSupply.at(denom) = pindex->pprev->mapZerocoinSupply.at(denom);
                }
            }

            // Track zerocoin money supply
            CAmount nAmountZerocoinSpent = 0;
            pindex->vMintDenominationsInBlock.clear();
            if (pindex->pprev) {
                std::set<uint256> setAddedToWallet;
                for (auto& m : listMints) {
                    libzerocoin::CoinDenomination denom = m.GetDenomination();
                    pindex->vMintDenominationsInBlock.push_back(m.GetDenomination());
                    pindex->mapZerocoinSupply.at(denom)++;

                    //Remove any of our own mints from the mintpool
                    if (pwalletMain) {
                        if (pwalletMain->IsMyMint(m.GetValue())) {
                            pwalletMain->UpdateMint(m.GetValue(), pindex->nHeight, m.GetTxHash(), m.GetDenomination());

                            // Add the transaction to the wallet
                            for (auto& tx : block.vtx) {
                                uint256 txid = tx.GetHash();
                                if (setAddedToWallet.count(txid))
                                    continue;
                                if (txid == m.GetTxHash()) {
                                    CWalletTx wtx(pwalletMain, tx);
                                    wtx.nTimeReceived = block.GetBlockTime();
                                    wtx.SetMerkleBranch(block);
                                    pwalletMain->AddToWallet(wtx);
                                    setAddedToWallet.insert(txid);
                                }
                            }
                        }
                    }
                }

                for (auto& denom : listSpends) {
                    pindex->mapZerocoinSupply.at(denom)--;
                    nAmountZerocoinSpent += libzerocoin::ZerocoinDenominationToAmount(denom);

                    // zerocoin failsafe
                    if (pindex->mapZerocoinSupply.at(denom) < 0)
                        return error("Block contains zerocoins that spend more than are in the available supply to spend");
                }
            }

            for (auto& denom : zerocoinDenomList)
                LogPrint("zero", "%s coins for denomination %d pubcoin %s\n", __func__, denom, pindex->mapZerocoinSupply.at(denom));

            return true;
        }

        static int64_t nTimeVerify = 0;
        static int64_t nTimeConnect = 0;
        static int64_t nTimeIndex = 0;
        static int64_t nTimeCallbacks = 0;
        static int64_t nTimeTotal = 0;

        // Index either: a) every data push >=8 bytes,  b) if no such pushes, the entire script
        void static BuildAddrIndex(const CScript& script, const CExtDiskTxPos& pos, std::vector<std::pair<uint160, CExtDiskTxPos> >& out)
        {
            CScript::const_iterator pc = script.begin();
            CScript::const_iterator pend = script.end();
            std::vector<unsigned char> data;
            opcodetype opcode;
            bool fHaveData = false;
            while (pc < pend) {
                script.GetOp(pc, opcode, data);
                if (0 <= opcode && opcode <= OP_PUSHDATA4 && data.size() >= 8) { // data element
                    uint160 addrid;
                    if (data.size() <= 20) {
                        memcpy(&addrid, &data[0], data.size());
                    } else {
                        addrid = Hash160(data);
                    }
                    out.push_back(std::make_pair(addrid, pos));
                    fHaveData = true;
                }
            }
            if (!fHaveData) {
                uint160 addrid = Hash160(script);
                out.push_back(std::make_pair(addrid, pos));
            }
        }

        bool ConnectBlock(const CBlock& block, CValidationState& state, CBlockIndex* pindex, CCoinsViewCache& view, bool fJustCheck, bool fAlreadyChecked)
        {
            AssertLockHeld(cs_main);
            // Check it again in case a previous version let a bad block in
            if (!fAlreadyChecked && !CheckBlock(block, state, !fJustCheck, !fJustCheck))
                return false;

            // verify that the view's current state corresponds to the previous block
            uint256 hashPrevBlock = pindex->pprev == NULL ? uint256(0) : pindex->pprev->GetBlockHash();
            if (hashPrevBlock != view.GetBestBlock())
                LogPrintf("%s: hashPrev=%s view=%s\n", __func__, hashPrevBlock.ToString().c_str(), view.GetBestBlock().ToString().c_str());
            assert(hashPrevBlock == view.GetBestBlock());

            // Special case for the genesis block, skipping connection of its transactions
            // (its coinbase is unspendable)
            if (block.GetHash() == Params().HashGenesisBlock()) {
                view.SetBestBlock(pindex->GetBlockHash());
                return true;
            }

            if (pindex->nHeight <= Params().LAST_POW_BLOCK() && block.IsProofOfStake())
                return state.DoS(100, error("ConnectBlock() : PoS period not active"),
                    REJECT_INVALID, "PoS-early");

            if (pindex->nHeight > Params().LAST_POW_BLOCK() && block.IsProofOfWork())
                return state.DoS(100, error("ConnectBlock() : PoW period ended"),
                    REJECT_INVALID, "PoW-ended");

            bool fScriptChecks = pindex->nHeight >= Checkpoints::GetTotalBlocksEstimate();

            // Do not allow blocks that contain transactions which 'overwrite' older transactions,
            // unless those are already completely spent.
            // If such overwrites are allowed, coinbases and transactions depending upon those
            // can be duplicated to remove the ability to spend the first instance -- even after
            // being sent to another address.
            // See BIP30 and http://r6.ca/blog/20120206T005236Z.html for more information.
            // This logic is not necessary for memory pool transactions, as AcceptToMemoryPool
            // already refuses previously-known transaction ids entirely.
            // This rule was originally applied all blocks whose timestamp was after March 15, 2012, 0:00 UTC.
            // Now that the whole chain is irreversibly beyond that time it is applied to all blocks except the
            // two in the chain that violate it. This prevents exploiting the issue against nodes in their
            // initial block download.
            bool fEnforceBIP30 = (!pindex->phashBlock) || // Enforce on CreateNewBlock invocations which don't have a hash.
                                 !((pindex->nHeight == 91842 && pindex->GetBlockHash() == uint256("0x00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec")) ||
                                     (pindex->nHeight == 91880 && pindex->GetBlockHash() == uint256("0x00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721")));
            if (fEnforceBIP30) {
                BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                    const CCoins* coins = view.AccessCoins(tx.GetHash());
                    if (coins && !coins->IsPruned())
                        return state.DoS(100, error("ConnectBlock() : tried to overwrite transaction"),
                            REJECT_INVALID, "bad-txns-BIP30");
                }
            }

            CCheckQueueControl<CScriptCheck> control(fScriptChecks && nScriptCheckThreads ? &scriptcheckqueue : NULL);

            int64_t nTimeStart = GetTimeMicros();
            CAmount nFees = 0;
            int nInputs = 0;
            int64_t nSigOpsCost = 0;
            CExtDiskTxPos pos(CDiskTxPos(pindex->GetBlockPos(), GetSizeOfCompactSize(block.vtx.size())), pindex->nHeight);
            std::vector<std::pair<uint256, CDiskTxPos> > vPosTxid;
            std::vector<std::pair<uint160, CExtDiskTxPos> > vPosAddrid;
            std::vector<pair<CoinSpend, uint256> > vSpends;
            vector<pair<PublicCoin, uint256> > vMints;
            if (fTxIndex)
                vPosTxid.reserve(block.vtx.size());
            if (fAddrIndex)
                vPosAddrid.reserve(block.vtx.size() * 4);
            vPosTxid.reserve(block.vtx.size());
            CBlockUndo blockundo;
            blockundo.vtxundo.reserve(block.vtx.size() - 1);
            CAmount nValueOut = 0;
            CAmount nValueIn = 0;
            vector<uint256> vSpendsInBlock;
            uint256 hashBlock = block.GetHash();

            unsigned int flags = SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_DERSIG;

            if (GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < block.nTime) {
                flags |= SCRIPT_VERIFY_WITNESS | SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY | SCRIPT_VERIFY_CHECKSEQUENCEVERIFY;
            }

            for (unsigned int i = 0; i < block.vtx.size(); i++) {
                const CTransaction& tx = block.vtx[i];

                nInputs += tx.vin.size();

#if 0
        //Temporarily disable zerocoin transactions for maintenance
        if (block.nTime > GetSporkValue(SPORK_23_ZEROCOIN_MAINTENANCE_MODE) && !IsInitialBlockDownload() && tx.ContainsZerocoins()) {
            return state.DoS(100, error("ConnectBlock() : zerocoin transactions are currently in maintenance mode"));
        }
        if (tx.IsZerocoinSpend()) {
            int nHeightTx = 0;
            uint256 txid = tx.GetHash();
            vSpendsInBlock.emplace_back(txid);
            if (IsTransactionInChain(tx.GetHash(), nHeightTx)) {
                //when verifying blocks on init, the blocks are scanned without being disconnected - prevent that from causing an error
                if (!fVerifyingBlocks || (fVerifyingBlocks && pindex->nHeight > nHeightTx))
                    return state.DoS(100, error("%s : txid %s already exists in block %d , trying to include it again in block %d", __func__,
                                                tx.GetHash().GetHex(), nHeightTx, pindex->nHeight),
                                     REJECT_INVALID, "bad-txns-inputs-missingorspent");
            }

            //Check for double spending of serial #'s
            set<CBigNum> setSerials;
            for (const CTxIn& txIn : tx.vin) {
                if (!txIn.scriptSig.IsZerocoinSpend())
                    continue;
                CoinSpend spend = TxInToZerocoinSpend(txIn);
                nValueIn += spend.getDenomination() * COIN;

                //queue for db write after the 'justcheck' section has concluded
                vSpends.emplace_back(make_pair(spend, tx.GetHash()));

                if (!ContextualCheckZerocoinSpend(tx, spend, pindex, hashBlock))
                    return state.DoS(100, error("%s: failed to add block %s with invalid zerocoinspend", __func__, tx.GetHash().GetHex()), REJECT_INVALID);
                }

            // Check that zABET mints are not already known
            if (tx.IsZerocoinMint()) {
                for (auto& out : tx.vout) {
                    if (!out.IsZerocoinMint())
                        continue;

                    PublicCoin coin(Params().Zerocoin_Params());
                    if (!TxOutToPublicCoin(out, coin, state))
                        return state.DoS(100, error("%s: failed final check of zerocoinmint for tx %s", __func__, tx.GetHash().GetHex()));

                    if (!ContextualCheckZerocoinMint(tx, coin, pindex))
                        return state.DoS(100, error("%s: zerocoin mint failed contextual check", __func__));

                    vMints.emplace_back(make_pair(coin, tx.GetHash()));
                }
            }
#endif
                if (!tx.IsCoinBase()) {
                    if (!view.HaveInputs(tx))
                        return state.DoS(100, error("ConnectBlock() : inputs missing/spent"),
                            REJECT_INVALID, "bad-txns-inputs-missingorspent");

                    // Check that zABET mints are not already known
                    if (tx.IsZerocoinMint()) {
                        for (auto& out : tx.vout) {
                            if (!out.IsZerocoinMint())
                                continue;

                            PublicCoin coin(Params().Zerocoin_Params());
                            if (!TxOutToPublicCoin(out, coin, state))
                                return state.DoS(100, error("%s: failed final check of zerocoinmint for tx %s", __func__, tx.GetHash().GetHex()));

                            if (!ContextualCheckZerocoinMint(tx, coin, pindex))
                                return state.DoS(100, error("%s: zerocoin mint failed contextual check", __func__));

                            vMints.emplace_back(make_pair(coin, tx.GetHash()));
                        }
                    }

                    if (!tx.IsCoinStake())
                        nFees += view.GetValueIn(tx) - tx.GetValueOut();
                    nValueIn += view.GetValueIn(tx);

                    std::vector<CScriptCheck> vChecks;

                    // GetTransactionSigOpCost counts 3 types of sigops:
                    // * legacy (always)
                    // * p2sh (when P2SH enabled in flags and excludes coinbase)
                    // * witness (when witness enabled in flags and excludes coinbase)
                    nSigOpsCost += GetTransactionSigOpCost(tx, view, flags);
                    if (nSigOpsCost > MAX_BLOCK_SIGOPS_COST)
                        return state.DoS(100, error("ConnectBlock(): too many sigops"),
                            REJECT_INVALID, "bad-blk-sigops");

                    if (!CheckInputs(tx, state, view, fScriptChecks, flags, false, nScriptCheckThreads ? &vChecks : NULL))
                        return false;
                    control.Add(vChecks);
                }
                nValueOut += tx.GetValueOut();

                CTxUndo undoDummy;
                if (i > 0) {
                    blockundo.vtxundo.push_back(CTxUndo());
                }
                if (fTxIndex)
                    vPosTxid.push_back(std::make_pair(tx.GetHash(), pos));
                if (fAddrIndex) {
                    if (!tx.IsCoinBase()) {
                        BOOST_FOREACH (const CTxIn& txin, tx.vin) {
                            CCoins coins;
                            view.GetCoins(txin.prevout.hash, coins);
                            if (coins.IsAvailable(txin.prevout.n)) {
                                BuildAddrIndex(coins.vout[txin.prevout.n].scriptPubKey, pos, vPosAddrid);
                            }
                        }
                    }
                    BOOST_FOREACH (const CTxOut& txout, tx.vout)
                        BuildAddrIndex(txout.scriptPubKey, pos, vPosAddrid);
                }

                UpdateCoins(tx, state, view, i == 0 ? undoDummy : blockundo.vtxundo.back(), pindex->nHeight);
                pos.nTxOffset += ::GetSerializeSize(tx, SER_DISK, CLIENT_VERSION);
            }

            UpdateZABETSupply(block, pindex);

            // track money supply and mint amount info
            CAmount nMoneySupplyPrev = pindex->pprev ? pindex->pprev->nMoneySupply : 0;
            pindex->nMoneySupply = nMoneySupplyPrev + nValueOut - nValueIn;
            pindex->nMint = pindex->nMoneySupply - nMoneySupplyPrev + nFees;

            //    LogPrintf("XX69----------> ConnectBlock(): nValueOut: %s, nValueIn: %s, nFees: %s, nMint: %s zABETSpent: %s\n",
            //              FormatMoney(nValueOut), FormatMoney(nValueIn),
            //              FormatMoney(nFees), FormatMoney(pindex->nMint), FormatMoney(nAmountZerocoinSpent));

            int64_t nTime1 = GetTimeMicros();
            nTimeConnect += nTime1 - nTimeStart;
            LogPrint("bench", "      - Connect %u transactions: %.2fms (%.3fms/tx, %.3fms/txin) [%.2fs]\n", (unsigned)block.vtx.size(), 0.001 * (nTime1 - nTimeStart), 0.001 * (nTime1 - nTimeStart) / block.vtx.size(), nInputs <= 1 ? 0 : 0.001 * (nTime1 - nTimeStart) / (nInputs - 1), nTimeConnect * 0.000001);

            //PoW phase redistributed fees to miner. PoS stage destroys fees.
            CAmount nExpectedMint = GetBlockValue(pindex->pprev->nHeight);
            if (block.IsProofOfWork())
                nExpectedMint += nFees;

            //Check that the block does not overmint
            if (!IsBlockValueValid(block, nExpectedMint, pindex->nMint) && (pindex->pprev->nHeight != 84702)) { // bug patched at block 90000, too far to roll back
                return state.DoS(100, error("ConnectBlock() : reward pays too much (actual=%s vs limit=%s)", FormatMoney(pindex->nMint), FormatMoney(nExpectedMint)), REJECT_INVALID, "bad-cb-amount");
            }
#if 0

    // Ensure that accumulator checkpoints are valid and in the same state as this instance of the chain
    AccumulatorMap mapAccumulators(GetZerocoinParams(pindex->nHeight));
    if (!ValidateAccumulatorCheckpoint(block, pindex, mapAccumulators))
        return state.DoS(100, error("%s: Failed to validate accumulator checkpoint for block=%s height=%d", __func__,
                                    block.GetHash().GetHex(), pindex->nHeight), REJECT_INVALID, "bad-acc-checkpoint");
#endif
            if (!control.Wait())
                return state.DoS(100, false);
            int64_t nTime2 = GetTimeMicros();
            nTimeVerify += nTime2 - nTimeStart;
            LogPrint("bench", "    - Verify %u txins: %.2fms (%.3fms/txin) [%.2fs]\n", nInputs - 1, 0.001 * (nTime2 - nTimeStart), nInputs <= 1 ? 0 : 0.001 * (nTime2 - nTimeStart) / (nInputs - 1), nTimeVerify * 0.000001);

            //IMPORTANT NOTE: Nothing before this point should actually store to disk (or even memory)
            if (fJustCheck)
                return true;

            // Write undo information to disk
            if (pindex->GetUndoPos().IsNull() || !pindex->IsValid(BLOCK_VALID_SCRIPTS)) {
                if (pindex->GetUndoPos().IsNull()) {
                    CDiskBlockPos pos;
                    if (!FindUndoPos(state, pindex->nFile, pos, ::GetSerializeSize(blockundo, SER_DISK, CLIENT_VERSION) + 40))
                        return error("ConnectBlock() : FindUndoPos failed");
                    if (!blockundo.WriteToDisk(pos, pindex->pprev->GetBlockHash()))
                        return state.Error("Failed to write undo data");

                    // update nUndoPos in block index
                    pindex->nUndoPos = pos.nPos;
                    pindex->nStatus |= BLOCK_HAVE_UNDO;
                }

                pindex->RaiseValidity(BLOCK_VALID_SCRIPTS);
                setDirtyBlockIndex.insert(pindex);
            }

            //Record zABET serials
            set<uint256> setAddedTx;
            for (pair<CoinSpend, uint256> pSpend : vSpends) {
                //record spend to database
                if (!zerocoinDB->WriteCoinSpend(pSpend.first.getCoinSerialNumber(), pSpend.second))
                    return state.Error(("Failed to record coin serial to database"));

                // Send signal to wallet if this is ours
                if (pwalletMain) {
                    if (pwalletMain->IsMyZerocoinSpend(pSpend.first.getCoinSerialNumber())) {
                        LogPrintf("%s: %s detected zerocoinspend in transaction %s \n", __func__, pSpend.first.getCoinSerialNumber().GetHex(), pSpend.second.GetHex());
                        pwalletMain->NotifyZerocoinChanged(pwalletMain, pSpend.first.getCoinSerialNumber().GetHex(), "Used", CT_UPDATED);

                        //Don't add the same tx multiple times
                        if (setAddedTx.count(pSpend.second))
                            continue;

                        //Search block for matching tx, turn into wtx, set merkle branch, add to wallet
                        for (CTransaction tx : block.vtx) {
                            if (tx.GetHash() == pSpend.second) {
                                CWalletTx wtx(pwalletMain, tx);
                                wtx.nTimeReceived = pindex->GetBlockTime();
                                wtx.SetMerkleBranch(block);
                                pwalletMain->AddToWallet(wtx);
                                setAddedTx.insert(pSpend.second);
                            }
                        }
                    }
                }
            }
#if 0
    //Record mints to db
    for (pair<PublicCoin, uint256> pMint : vMints) {
        if (!zerocoinDB->WriteCoinMint(pMint.first, pMint.second))
            return state.Error(("Failed to record new mint to database"));
    }

    //Record accumulator checksums
    DatabaseChecksums(mapAccumulators);
#endif
            if (fTxIndex)
                if (!pblocktree->WriteTxIndex(vPosTxid))
                    return state.Error("Failed to write transaction index");

            if (fAddrIndex)
                if (!pblocktree->AddAddrIndex(vPosAddrid))
                    return state.Error("Failed to write address index");

            // add new entries
            for (const CTransaction tx : block.vtx) {
                if (tx.IsCoinBase() || tx.IsZerocoinSpend())
                    continue;
                for (const CTxIn in : tx.vin) {
                    LogPrint("map", "mapStakeSpent: Insert %s | %u\n", in.prevout.ToString(), pindex->nHeight);
                    mapStakeSpent.insert(std::make_pair(in.prevout, pindex->nHeight));
                }
            }


            // delete old entries
            for (auto it = mapStakeSpent.begin(); it != mapStakeSpent.end();) {
                if (it->second < pindex->nHeight - Params().MaxReorganizationDepth()) {
                    LogPrint("map", "mapStakeSpent: Erase %s | %u\n", it->first.ToString(), it->second);
                    it = mapStakeSpent.erase(it);
                } else {
                    it++;
                }
            }


            // add this block to the view's block chain
            view.SetBestBlock(pindex->GetBlockHash());

            int64_t nTime3 = GetTimeMicros();
            nTimeIndex += nTime3 - nTime2;
            LogPrint("bench", "    - Index writing: %.2fms [%.2fs]\n", 0.001 * (nTime3 - nTime2), nTimeIndex * 0.000001);

            // Watch for changes to the previous coinbase transaction.
            static uint256 hashPrevBestCoinBase;
            GetMainSignals().UpdatedTransaction(hashPrevBestCoinBase);
            hashPrevBestCoinBase = block.vtx[0].GetHash();

            int64_t nTime4 = GetTimeMicros();
            nTimeCallbacks += nTime4 - nTime3;
            LogPrint("bench", "    - Callbacks: %.2fms [%.2fs]\n", 0.001 * (nTime4 - nTime3), nTimeCallbacks * 0.000001);

            return true;
        }

        enum FlushStateMode {
            FLUSH_STATE_IF_NEEDED,
            FLUSH_STATE_PERIODIC,
            FLUSH_STATE_ALWAYS
        };

        /**
 * Update the on-disk chain state.
 * The caches and indexes are flushed if either they're too large, forceWrite is set, or
 * fast is not set and it's been a while since the last write.
 */
        bool static FlushStateToDisk(CValidationState & state, FlushStateMode mode)
        {
            LOCK(cs_main);
            static int64_t nLastWrite = 0;
            try {
                if ((mode == FLUSH_STATE_ALWAYS) ||
                    ((mode == FLUSH_STATE_PERIODIC || mode == FLUSH_STATE_IF_NEEDED) && pcoinsTip->GetCacheSize() > nCoinCacheSize) ||
                    (mode == FLUSH_STATE_PERIODIC && GetTimeMicros() > nLastWrite + DATABASE_WRITE_INTERVAL * 1000000)) {
                    // Typical CCoins structures on disk are around 100 bytes in size.
                    // Pushing a new one to the database can cause it to be written
                    // twice (once in the log, and once in the tables). This is already
                    // an overestimation, as most will delete an existing entry or
                    // overwrite one. Still, use a conservative safety factor of 2.
                    if (!CheckDiskSpace(100 * 2 * 2 * pcoinsTip->GetCacheSize()))
                        return state.Error("out of disk space");
                    // First make sure all block and undo data is flushed to disk.
                    FlushBlockFile();
                    // Then update all block file information (which may refer to block and undo files).
                    bool fileschanged = false;
                    for (set<int>::iterator it = setDirtyFileInfo.begin(); it != setDirtyFileInfo.end();) {
                        if (!pblocktree->WriteBlockFileInfo(*it, vinfoBlockFile[*it])) {
                            return state.Error("Failed to write to block index");
                        }
                        fileschanged = true;
                        setDirtyFileInfo.erase(it++);
                    }
                    if (fileschanged && !pblocktree->WriteLastBlockFile(nLastBlockFile)) {
                        return state.Error("Failed to write to block index");
                    }
                    for (set<CBlockIndex*>::iterator it = setDirtyBlockIndex.begin(); it != setDirtyBlockIndex.end();) {
                        if (!pblocktree->WriteBlockIndex(CDiskBlockIndex(*it))) {
                            return state.Error("Failed to write to block index");
                        }
                        setDirtyBlockIndex.erase(it++);
                    }
                    pblocktree->Sync();
                    // Finally flush the chainstate (which may refer to block index entries).
                    if (!pcoinsTip->Flush())
                        return state.Error("Failed to write to coin database");
                    // Update best block in wallet (so we can detect restored wallets).
                    if (mode != FLUSH_STATE_IF_NEEDED) {
                        GetMainSignals().SetBestChain(chainActive.GetLocator());
                    }
                    nLastWrite = GetTimeMicros();
                }
            } catch (const std::runtime_error& e) {
                return state.Error(std::string("System error while flushing: ") + e.what());
            }
            return true;
        }

        void FlushStateToDisk()
        {
            CValidationState state;
            FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
        }

        /** Update chainActive and related internal data structures. */
        void static UpdateTip(CBlockIndex * pindexNew)
        {
            chainActive.SetTip(pindexNew);

            // If turned on AutoZeromint will automatically convert ABET to zABET
            if (pwalletMain->isZeromintEnabled())
                pwalletMain->AutoZeromint();

            // New best block
            nTimeBestReceived = GetTime();
            mempool.AddTransactionsUpdated(1);

            LogPrintf("UpdateTip: new best=%s  height=%d  log2_work=%.8g  tx=%lu  date=%s progress=%f  cache=%u\n",
                chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(), log(chainActive.Tip()->nChainWork.getdouble()) / log(2.0), (unsigned long)chainActive.Tip()->nChainTx,
                DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
                Checkpoints::GuessVerificationProgress(chainActive.Tip()), (unsigned int)pcoinsTip->GetCacheSize());

            cvBlockChange.notify_all();

            // Check the version of the last 100 blocks to see if we need to upgrade:
            static bool fWarned = false;
            if (!IsInitialBlockDownload() && !fWarned) {
                int nUpgraded = 0;
                const CBlockIndex* pindex = chainActive.Tip();
                for (int i = 0; i < 100 && pindex != NULL; i++) {
                    if (pindex->nVersion > CBlock::CURRENT_VERSION)
                        ++nUpgraded;
                    pindex = pindex->pprev;
                }
                if (nUpgraded > 0)
                    LogPrintf("SetBestChain: %d of last 100 blocks above version %d\n", nUpgraded, (int)CBlock::CURRENT_VERSION);
                if (nUpgraded > 100 / 2) {
                    // strMiscWarning is read by GetWarnings(), called by Qt and the JSON-RPC code to warn the user:
                    strMiscWarning = _("Warning: This version is obsolete, upgrade required!");
                    CAlert::Notify(strMiscWarning, true);
                    fWarned = true;
                }
            }
        }

        /** Disconnect chainActive's tip. */
        bool static DisconnectTip(CValidationState & state, bool fBare)
        {
            CBlockIndex* pindexDelete = chainActive.Tip();
            assert(pindexDelete);
            mempool.check(pcoinsTip);
            // Read block from disk.
            CBlock block;
            if (!ReadBlockFromDisk(block, pindexDelete))
                return state.Error("Failed to read block");
            // Apply the block atomically to the chain state.
            int64_t nStart = GetTimeMicros();
            {
                CCoinsViewCache view(pcoinsTip);
                if (!DisconnectBlock(block, state, pindexDelete, view))
                    return error("DisconnectTip() : DisconnectBlock %s failed", pindexDelete->GetBlockHash().ToString());
                assert(view.Flush());
            }
            LogPrint("bench", "- Disconnect block: %.2fms\n", (GetTimeMicros() - nStart) * 0.001);
            // Write the chain state to disk, if necessary.
            if (!FlushStateToDisk(state, FLUSH_STATE_ALWAYS))
                return false;

            if (!fBare) {
                // Resurrect mempool transactions from the disconnected block.
                BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                    // ignore validation errors in resurrected transactions
                    list<CTransaction> removed;
                    CValidationState stateDummy;
                    if (tx.IsCoinBase() || tx.IsCoinStake() || !AcceptToMemoryPool(mempool, stateDummy, tx, false, NULL))
                        mempool.remove(tx, removed, true);
                }
                mempool.removeCoinbaseSpends(pcoinsTip, pindexDelete->nHeight);
                mempool.check(pcoinsTip);
            }

            // Update chainActive and related variables.
            UpdateTip(pindexDelete->pprev);
            // Let wallets know transactions went from 1-confirmed to
            // 0-confirmed or conflicted:
            BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                SyncWithWallets(tx, NULL);
            }
            return true;
        }

        static int64_t nTimeReadFromDisk = 0;
        static int64_t nTimeConnectTotal = 0;
        static int64_t nTimeFlush = 0;
        static int64_t nTimeChainState = 0;
        static int64_t nTimePostConnect = 0;

        /**
 * Connect a new block to chainActive. pblock is either NULL or a pointer to a CBlock
 * corresponding to pindexNew, to bypass loading it again from disk.
 */
        bool static ConnectTip(CValidationState & state, CBlockIndex * pindexNew, CBlock * pblock, bool fAlreadyChecked)
        {
            assert(pindexNew->pprev == chainActive.Tip());
            mempool.check(pcoinsTip);
            CCoinsViewCache view(pcoinsTip);

            if (pblock == NULL)
                fAlreadyChecked = false;

            // Read block from disk.
            int64_t nTime1 = GetTimeMicros();
            CBlock block;
            if (!pblock) {
                if (!ReadBlockFromDisk(block, pindexNew))
                    return state.Error("Failed to read block");
                pblock = &block;
            }
            // Apply the block atomically to the chain state.
            int64_t nTime2 = GetTimeMicros();
            nTimeReadFromDisk += nTime2 - nTime1;
            int64_t nTime3;
            LogPrint("bench", "  - Load block from disk: %.2fms [%.2fs]\n", (nTime2 - nTime1) * 0.001, nTimeReadFromDisk * 0.000001);
            {
                CInv inv(MSG_BLOCK, pindexNew->GetBlockHash());
                bool rv = ConnectBlock(*pblock, state, pindexNew, view, false, fAlreadyChecked);
                GetMainSignals().BlockChecked(*pblock, state);
                if (!rv) {
                    if (state.IsInvalid())
                        InvalidBlockFound(pindexNew, state);
                    return error("ConnectTip() : ConnectBlock %s failed", pindexNew->GetBlockHash().ToString());
                }
                mapBlockSource.erase(inv.hash);
                nTime3 = GetTimeMicros();
                nTimeConnectTotal += nTime3 - nTime2;
                LogPrint("bench", "  - Connect total: %.2fms [%.2fs]\n", (nTime3 - nTime2) * 0.001, nTimeConnectTotal * 0.000001);
                assert(view.Flush());
            }
            int64_t nTime4 = GetTimeMicros();
            nTimeFlush += nTime4 - nTime3;
            LogPrint("bench", "  - Flush: %.2fms [%.2fs]\n", (nTime4 - nTime3) * 0.001, nTimeFlush * 0.000001);

            // Write the chain state to disk, if necessary. Always write to disk if this is the first of a new file.
            FlushStateMode flushMode = FLUSH_STATE_IF_NEEDED;
            if (pindexNew->pprev && (pindexNew->GetBlockPos().nFile != pindexNew->pprev->GetBlockPos().nFile))
                flushMode = FLUSH_STATE_ALWAYS;
            if (!FlushStateToDisk(state, flushMode))
                return false;
            int64_t nTime5 = GetTimeMicros();
            nTimeChainState += nTime5 - nTime4;
            LogPrint("bench", "  - Writing chainstate: %.2fms [%.2fs]\n", (nTime5 - nTime4) * 0.001, nTimeChainState * 0.000001);

            // Remove conflicting transactions from the mempool.
            list<CTransaction> txConflicted;
            mempool.removeForBlock(pblock->vtx, pindexNew->nHeight, txConflicted);
            mempool.check(pcoinsTip);
            // Update chainActive & related variables.
            UpdateTip(pindexNew);
            // Tell wallet about transactions that went from mempool
            // to conflicted:
            BOOST_FOREACH (const CTransaction& tx, txConflicted) {
                SyncWithWallets(tx, NULL);
            }
            // ... and about transactions that got confirmed:
            BOOST_FOREACH (const CTransaction& tx, pblock->vtx) {
                SyncWithWallets(tx, pblock);
            }

            int64_t nTime6 = GetTimeMicros();
            nTimePostConnect += nTime6 - nTime5;
            nTimeTotal += nTime6 - nTime1;
            LogPrint("bench", "  - Connect postprocess: %.2fms [%.2fs]\n", (nTime6 - nTime5) * 0.001, nTimePostConnect * 0.000001);
            LogPrint("bench", "- Connect block: %.2fms [%.2fs]\n", (nTime6 - nTime1) * 0.001, nTimeTotal * 0.000001);
            return true;
        }

        bool DisconnectBlocksAndReprocess(int blocks)
        {
            LOCK(cs_main);

            CValidationState state;

            LogPrintf("DisconnectBlocksAndReprocess: Got command to replay %d blocks\n", blocks);
            for (int i = 0; i <= blocks; i++)
                DisconnectTip(state, false);

            return true;
        }

        /*
    DisconnectBlockAndInputs

    Remove conflicting blocks for successful SwiftX transaction locks
    This should be very rare (Probably will never happen)
*/
        // ***TODO*** clean up here
        bool DisconnectBlockAndInputs(CValidationState & state, CTransaction txLock)
        {
            // All modifications to the coin state will be done in this cache.
            // Only when all have succeeded, we push it to pcoinsTip.
            //    CCoinsViewCache view(*pcoinsTip, true);

            CBlockIndex* BlockReading = chainActive.Tip();
            CBlockIndex* pindexNew = NULL;

            bool foundConflictingTx = false;

            //remove anything conflicting in the memory pool
            list<CTransaction> txConflicted;
            mempool.removeConflicts(txLock, txConflicted);


            // List of what to disconnect (typically nothing)
            vector<CBlockIndex*> vDisconnect;

            for (unsigned int i = 1; BlockReading && BlockReading->nHeight > 0 && !foundConflictingTx && i < 6; i++) {
                vDisconnect.push_back(BlockReading);
                pindexNew = BlockReading->pprev; //new best block

                CBlock block;
                if (!ReadBlockFromDisk(block, BlockReading))
                    return state.Error(_("Failed to read block"));

                // Queue memory transactions to resurrect.
                // We only do this for blocks after the last checkpoint (reorganisation before that
                // point should only happen with -reindex/-loadblock, or a misbehaving peer.
                BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                    if (!tx.IsCoinBase()) {
                        BOOST_FOREACH (const CTxIn& in1, txLock.vin) {
                            BOOST_FOREACH (const CTxIn& in2, tx.vin) {
                                if (in1.prevout == in2.prevout) foundConflictingTx = true;
                            }
                        }
                    }
                }

                if (BlockReading->pprev == NULL) {
                    assert(BlockReading);
                    break;
                }
                BlockReading = BlockReading->pprev;
            }

            if (!foundConflictingTx) {
                LogPrintf("DisconnectBlockAndInputs: Can't find a conflicting transaction to inputs\n");
                return false;
            }

            if (vDisconnect.size() > 0) {
                LogPrintf("REORGANIZE: Disconnect Conflicting Blocks %lli blocks; %s..\n", vDisconnect.size(), pindexNew->GetBlockHash().ToString());
                BOOST_FOREACH (CBlockIndex* pindex, vDisconnect) {
                    LogPrintf(" -- disconnect %s\n", pindex->GetBlockHash().ToString());
                    DisconnectTip(state, false);
                }
            }

            return true;
        }


        /**
 * Return the tip of the chain with the most work in it, that isn't
 * known to be invalid (it's however far from certain to be valid).
 */
        static CBlockIndex* FindMostWorkChain()
        {
            do {
                CBlockIndex* pindexNew = NULL;

                // Find the best candidate header.
                {
                    std::set<CBlockIndex*, CBlockIndexWorkComparator>::reverse_iterator it = setBlockIndexCandidates.rbegin();
                    if (it == setBlockIndexCandidates.rend())
                        return NULL;
                    pindexNew = *it;
                }

                // Check whether all blocks on the path between the currently active chain and the candidate are valid.
                // Just going until the active chain is an optimization, as we know all blocks in it are valid already.
                CBlockIndex* pindexTest = pindexNew;
                bool fInvalidAncestor = false;
                while (pindexTest && !chainActive.Contains(pindexTest)) {
                    assert(pindexTest->nChainTx || pindexTest->nHeight == 0);

                    // Pruned nodes may have entries in setBlockIndexCandidates for
                    // which block files have been deleted.  Remove those as candidates
                    // for the most work chain if we come across them; we can't switch
                    // to a chain unless we have all the non-active-chain parent blocks.
                    bool fFailedChain = pindexTest->nStatus & BLOCK_FAILED_MASK;
                    bool fMissingData = !(pindexTest->nStatus & BLOCK_HAVE_DATA);
                    if (fFailedChain || fMissingData) {
                        // Candidate chain is not usable (either invalid or missing data)
                        if (fFailedChain && (pindexBestInvalid == NULL || pindexNew->nChainWork > pindexBestInvalid->nChainWork))
                            pindexBestInvalid = pindexNew;
                        CBlockIndex* pindexFailed = pindexNew;
                        // Remove the entire chain from the set.
                        while (pindexTest != pindexFailed) {
                            if (fFailedChain) {
                                pindexFailed->nStatus |= BLOCK_FAILED_CHILD;
                            } else if (fMissingData) {
                                // If we're missing data, then add back to mapBlocksUnlinked,
                                // so that if the block arrives in the future we can try adding
                                // to setBlockIndexCandidates again.
                                mapBlocksUnlinked.insert(std::make_pair(pindexFailed->pprev, pindexFailed));
                            }
                            setBlockIndexCandidates.erase(pindexFailed);
                            pindexFailed = pindexFailed->pprev;
                        }
                        setBlockIndexCandidates.erase(pindexTest);
                        fInvalidAncestor = true;
                        break;
                    }
                    pindexTest = pindexTest->pprev;
                }
                if (!fInvalidAncestor)
                    return pindexNew;
            } while (true);
        }

        /** Delete all entries in setBlockIndexCandidates that are worse than the current tip. */
        static void PruneBlockIndexCandidates()
        {
            // Note that we can't delete the current block itself, as we may need to return to it later in case a
            // reorganization to a better block fails.
            std::set<CBlockIndex*, CBlockIndexWorkComparator>::iterator it = setBlockIndexCandidates.begin();
            while (it != setBlockIndexCandidates.end() && setBlockIndexCandidates.value_comp()(*it, chainActive.Tip())) {
                setBlockIndexCandidates.erase(it++);
            }
            // Either the current tip or a successor of it we're working towards is left in setBlockIndexCandidates.
            assert(!setBlockIndexCandidates.empty());
        }

        /**
 * Try to make some progress towards making pindexMostWork the active block.
 * pblock is either NULL or a pointer to a CBlock corresponding to pindexMostWork.
 */
        static bool ActivateBestChainStep(CValidationState & state, CBlockIndex * pindexMostWork, CBlock * pblock, bool fAlreadyChecked)
        {
            AssertLockHeld(cs_main);
            if (pblock == NULL)
                fAlreadyChecked = false;
            bool fInvalidFound = false;
            const CBlockIndex* pindexOldTip = chainActive.Tip();
            const CBlockIndex* pindexFork = chainActive.FindFork(pindexMostWork);

            // Disconnect active blocks which are no longer in the best chain.
            while (chainActive.Tip() && chainActive.Tip() != pindexFork) {
                if (!DisconnectTip(state, false))
                    return false;
            }

            // Build list of new blocks to connect.
            std::vector<CBlockIndex*> vpindexToConnect;
            bool fContinue = true;
            int nHeight = pindexFork ? pindexFork->nHeight : -1;
            while (fContinue && nHeight != pindexMostWork->nHeight) {
                // Don't iterate the entire list of potential improvements toward the best tip, as we likely only need
                // a few blocks along the way.
                int nTargetHeight = std::min(nHeight + 32, pindexMostWork->nHeight);
                vpindexToConnect.clear();
                vpindexToConnect.reserve(nTargetHeight - nHeight);
                CBlockIndex* pindexIter = pindexMostWork->GetAncestor(nTargetHeight);
                while (pindexIter && pindexIter->nHeight != nHeight) {
                    vpindexToConnect.push_back(pindexIter);
                    pindexIter = pindexIter->pprev;
                }
                nHeight = nTargetHeight;

                // Connect new blocks.
                BOOST_REVERSE_FOREACH (CBlockIndex* pindexConnect, vpindexToConnect) {
                    if (!ConnectTip(state, pindexConnect, pindexConnect == pindexMostWork ? pblock : NULL, fAlreadyChecked)) {
                        if (state.IsInvalid()) {
                            // The block violates a consensus rule.
                            if (!state.CorruptionPossible())
                                InvalidChainFound(vpindexToConnect.back());
                            state = CValidationState();
                            fInvalidFound = true;
                            fContinue = false;
                            break;
                        } else {
                            // A system error occurred (disk space, database error, ...).
                            return false;
                        }
                    } else {
                        PruneBlockIndexCandidates();
                        if (!pindexOldTip || chainActive.Tip()->nChainWork > pindexOldTip->nChainWork) {
                            // We're in a better position than we were. Return temporarily to release the lock.
                            fContinue = false;
                            break;
                        }
                    }
                }
            }

            // Callbacks/notifications for a new best chain.
            if (fInvalidFound)
                CheckForkWarningConditionsOnNewFork(vpindexToConnect.back());
            else
                CheckForkWarningConditions();

            return true;
        }

        /**
 * Make the best chain active, in multiple steps. The result is either failure
 * or an activated best chain. pblock is either NULL or a pointer to a block
 * that is already loaded (to avoid loading it again from disk).
 */
        bool ActivateBestChain(CValidationState & state, CBlock * pblock, bool fAlreadyChecked)
        {
            CBlockIndex* pindexNewTip = NULL;
            CBlockIndex* pindexMostWork = NULL;
            do {
                boost::this_thread::interruption_point();

                bool fInitialDownload;
                while (true) {
                    TRY_LOCK(cs_main, lockMain);
                    if (!lockMain) {
                        MilliSleep(50);
                        continue;
                    }

                    pindexMostWork = FindMostWorkChain();

                    // Whether we have anything to do at all.
                    if (pindexMostWork == NULL || pindexMostWork == chainActive.Tip())
                        return true;

                    if (!ActivateBestChainStep(state, pindexMostWork, pblock && pblock->GetHash() == pindexMostWork->GetBlockHash() ? pblock : NULL, fAlreadyChecked))
                        return false;

                    pindexNewTip = chainActive.Tip();
                    fInitialDownload = IsInitialBlockDownload();
                    break;
                }
                // When we reach this point, we switched to a new tip (stored in pindexNewTip).

                // Notifications/callbacks that can run without cs_main
                if (!fInitialDownload) {
                    uint256 hashNewTip = pindexNewTip->GetBlockHash();
                    // Relay inventory, but don't relay old inventory during initial block download.
                    int nBlockEstimate = Checkpoints::GetTotalBlocksEstimate();
                    {
                        LOCK(cs_vNodes);
                        BOOST_FOREACH (CNode* pnode, vNodes)
                            if (chainActive.Height() > (pnode->nStartingHeight != -1 ? pnode->nStartingHeight - 2000 : nBlockEstimate))
                                pnode->PushInventory(CInv(MSG_BLOCK, hashNewTip));
                    }
                    // Notify external listeners about the new tip.
                    // Note: uiInterface, should switch main signals.
                    uiInterface.NotifyBlockTip(hashNewTip);
                    GetMainSignals().UpdatedBlockTip(pindexNewTip);

                    unsigned size = 0;

                    if (pblock)
                        size = GetSerializeSize(*pblock, SER_NETWORK, PROTOCOL_VERSION);
                    // If the size is over 1 MB notify external listeners, and it is within the last 5 minutes
                    if (size > MAX_BLOCK_SIZE_LEGACY && pblock->GetBlockTime() > GetAdjustedTime() - 300) {
                        uiInterface.NotifyBlockSize(static_cast<int>(size), hashNewTip);
                    }
                }
            } while (pindexMostWork != chainActive.Tip());
            CheckBlockIndex();

            // Write changes periodically to disk, after relay.
            if (!FlushStateToDisk(state, FLUSH_STATE_PERIODIC)) {
                return false;
            }

            return true;
        }

        bool InvalidateBlock(CValidationState & state, CBlockIndex * pindex)
        {
            AssertLockHeld(cs_main);

            // Mark the block itself as invalid.
            pindex->nStatus |= BLOCK_FAILED_VALID;
            setDirtyBlockIndex.insert(pindex);
            setBlockIndexCandidates.erase(pindex);

            while (chainActive.Contains(pindex)) {
                CBlockIndex* pindexWalk = chainActive.Tip();
                pindexWalk->nStatus |= BLOCK_FAILED_CHILD;
                setDirtyBlockIndex.insert(pindexWalk);
                setBlockIndexCandidates.erase(pindexWalk);
                // ActivateBestChain considers blocks already in chainActive
                // unconditionally valid already, so force disconnect away from it.
                if (!DisconnectTip(state, false)) {
                    return false;
                }
            }

            // The resulting new best tip may not be in setBlockIndexCandidates anymore, so
            // add them again.
            BlockMap::iterator it = mapBlockIndex.begin();
            while (it != mapBlockIndex.end()) {
                if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && !setBlockIndexCandidates.value_comp()(it->second, chainActive.Tip())) {
                    setBlockIndexCandidates.insert(it->second);
                }
                it++;
            }

            InvalidChainFound(pindex);
            return true;
        }

        bool ReconsiderBlock(CValidationState & state, CBlockIndex * pindex)
        {
            AssertLockHeld(cs_main);

            int nHeight = pindex->nHeight;

            // Remove the invalidity flag from this block and all its descendants.
            BlockMap::iterator it = mapBlockIndex.begin();
            while (it != mapBlockIndex.end()) {
                if (!it->second->IsValid() && it->second->GetAncestor(nHeight) == pindex) {
                    it->second->nStatus &= ~BLOCK_FAILED_MASK;
                    setDirtyBlockIndex.insert(it->second);
                    if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && setBlockIndexCandidates.value_comp()(chainActive.Tip(), it->second)) {
                        setBlockIndexCandidates.insert(it->second);
                    }
                    if (it->second == pindexBestInvalid) {
                        // Reset invalid block marker if it was pointing to one of those.
                        pindexBestInvalid = NULL;
                    }
                }
                it++;
            }

            // Remove the invalidity flag from all ancestors too.
            while (pindex != NULL) {
                if (pindex->nStatus & BLOCK_FAILED_MASK) {
                    pindex->nStatus &= ~BLOCK_FAILED_MASK;
                    setDirtyBlockIndex.insert(pindex);
                }
                pindex = pindex->pprev;
            }
            return true;
        }

        CBlockIndex* AddToBlockIndex(const CBlock& block)
        {
            // Check for duplicate
            uint256 hash = block.GetHash();
            BlockMap::iterator it = mapBlockIndex.find(hash);
            if (it != mapBlockIndex.end())
                return it->second;

            // Construct new block index object
            CBlockIndex* pindexNew = new CBlockIndex(block);
            assert(pindexNew);
            // We assign the sequence id to blocks only when the full data is available,
            // to avoid miners withholding blocks but broadcasting headers, to get a
            // competitive advantage.
            pindexNew->nSequenceId = 0;
            BlockMap::iterator mi = mapBlockIndex.insert(make_pair(hash, pindexNew)).first;

            //mark as PoS seen
            if (pindexNew->IsProofOfStake())
                setStakeSeen.insert(make_pair(pindexNew->prevoutStake, pindexNew->nStakeTime));

            pindexNew->phashBlock = &((*mi).first);
            BlockMap::iterator miPrev = mapBlockIndex.find(block.hashPrevBlock);
            if (miPrev != mapBlockIndex.end()) {
                pindexNew->pprev = (*miPrev).second;
                pindexNew->nHeight = pindexNew->pprev->nHeight + 1;
                pindexNew->BuildSkip();

                //update previous block pointer
                pindexNew->pprev->pnext = pindexNew;

                // ppcoin: compute chain trust score
                pindexNew->bnChainTrust = (pindexNew->pprev ? pindexNew->pprev->bnChainTrust : 0) + pindexNew->GetBlockTrust();

                // ppcoin: compute stake entropy bit for stake modifier
                if (!pindexNew->SetStakeEntropyBit(pindexNew->GetStakeEntropyBit()))
                    LogPrintf("AddToBlockIndex() : SetStakeEntropyBit() failed \n");

                // ppcoin: record proof-of-stake hash value
                if (pindexNew->IsProofOfStake()) {
                    if (!mapProofOfStake.count(hash))
                        LogPrintf("AddToBlockIndex() : hashProofOfStake not found in map \n");
                    pindexNew->hashProofOfStake = mapProofOfStake[hash];
                }

                // ppcoin: compute stake modifier
                uint64_t nStakeModifier = 0;
                bool fGeneratedStakeModifier = false;
                if (!ComputeNextStakeModifier(pindexNew->pprev, nStakeModifier, fGeneratedStakeModifier))
                    LogPrintf("AddToBlockIndex() : ComputeNextStakeModifier() failed \n");
                pindexNew->SetStakeModifier(nStakeModifier, fGeneratedStakeModifier);
                pindexNew->nStakeModifierChecksum = GetStakeModifierChecksum(pindexNew);
                if (!CheckStakeModifierCheckpoints(pindexNew->nHeight, pindexNew->nStakeModifierChecksum))
                    LogPrintf("AddToBlockIndex() : Rejected by stake modifier checkpoint height=%d, modifier=%s \n", pindexNew->nHeight, std::to_string(nStakeModifier));
            }
            pindexNew->nChainWork = (pindexNew->pprev ? pindexNew->pprev->nChainWork : 0) + GetBlockProof(*pindexNew);
            pindexNew->RaiseValidity(BLOCK_VALID_TREE);
            if (pindexBestHeader == NULL || pindexBestHeader->nChainWork < pindexNew->nChainWork)
                pindexBestHeader = pindexNew;

            //update previous block pointer
            if (pindexNew->nHeight)
                pindexNew->pprev->pnext = pindexNew;

            setDirtyBlockIndex.insert(pindexNew);

            return pindexNew;
        }

        /** Mark a block as having its data received and checked (up to BLOCK_VALID_TRANSACTIONS). */
        bool ReceivedBlockTransactions(const CBlock& block, CValidationState& state, CBlockIndex* pindexNew, const CDiskBlockPos& pos)
        {
            if (block.IsProofOfStake())
                pindexNew->SetProofOfStake();
            pindexNew->nTx = block.vtx.size();
            pindexNew->nChainTx = 0;
            pindexNew->nFile = pos.nFile;
            pindexNew->nDataPos = pos.nPos;
            pindexNew->nUndoPos = 0;
            pindexNew->nStatus |= BLOCK_HAVE_DATA | BLOCK_OPT_WITNESS;
            pindexNew->RaiseValidity(BLOCK_VALID_TRANSACTIONS);
            setDirtyBlockIndex.insert(pindexNew);

            if (pindexNew->pprev == NULL || pindexNew->pprev->nChainTx) {
                // If pindexNew is the genesis block or all parents are BLOCK_VALID_TRANSACTIONS.
                deque<CBlockIndex*> queue;
                queue.push_back(pindexNew);

                // Recursively process any descendant blocks that now may be eligible to be connected.
                while (!queue.empty()) {
                    CBlockIndex* pindex = queue.front();
                    queue.pop_front();
                    pindex->nChainTx = (pindex->pprev ? pindex->pprev->nChainTx : 0) + pindex->nTx;
                    {
                        LOCK(cs_nBlockSequenceId);
                        pindex->nSequenceId = nBlockSequenceId++;
                    }
                    if (chainActive.Tip() == NULL || !setBlockIndexCandidates.value_comp()(pindex, chainActive.Tip())) {
                        setBlockIndexCandidates.insert(pindex);
                    }
                    std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = mapBlocksUnlinked.equal_range(pindex);
                    while (range.first != range.second) {
                        std::multimap<CBlockIndex*, CBlockIndex*>::iterator it = range.first;
                        queue.push_back(it->second);
                        range.first++;
                        mapBlocksUnlinked.erase(it);
                    }
                }
            } else {
                if (pindexNew->pprev && pindexNew->pprev->IsValid(BLOCK_VALID_TREE)) {
                    mapBlocksUnlinked.insert(std::make_pair(pindexNew->pprev, pindexNew));
                }
            }

            return true;
        }

        bool FindBlockPos(CValidationState & state, CDiskBlockPos & pos, unsigned int nAddSize, unsigned int nHeight, uint64_t nTime, bool fKnown = false)
        {
            LOCK(cs_LastBlockFile);

            unsigned int nFile = fKnown ? pos.nFile : nLastBlockFile;
            if (vinfoBlockFile.size() <= nFile) {
                vinfoBlockFile.resize(nFile + 1);
            }

            if (!fKnown) {
                while (vinfoBlockFile[nFile].nSize + nAddSize >= MAX_BLOCKFILE_SIZE) {
                    LogPrintf("Leaving block file %i: %s\n", nFile, vinfoBlockFile[nFile].ToString());
                    FlushBlockFile(true);
                    nFile++;
                    if (vinfoBlockFile.size() <= nFile) {
                        vinfoBlockFile.resize(nFile + 1);
                    }
                }
                pos.nFile = nFile;
                pos.nPos = vinfoBlockFile[nFile].nSize;
            }

            nLastBlockFile = nFile;
            vinfoBlockFile[nFile].AddBlock(nHeight, nTime);
            if (fKnown)
                vinfoBlockFile[nFile].nSize = std::max(pos.nPos + nAddSize, vinfoBlockFile[nFile].nSize);
            else
                vinfoBlockFile[nFile].nSize += nAddSize;

            if (!fKnown) {
                unsigned int nOldChunks = (pos.nPos + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
                unsigned int nNewChunks = (vinfoBlockFile[nFile].nSize + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
                if (nNewChunks > nOldChunks) {
                    if (CheckDiskSpace(nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos)) {
                        FILE* file = OpenBlockFile(pos);
                        if (file) {
                            LogPrintf("Pre-allocating up to position 0x%x in blk%05u.dat\n", nNewChunks * BLOCKFILE_CHUNK_SIZE, pos.nFile);
                            AllocateFileRange(file, pos.nPos, nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos);
                            fclose(file);
                        }
                    } else
                        return state.Error("out of disk space");
                }
            }

            setDirtyFileInfo.insert(nFile);
            return true;
        }

        bool FindUndoPos(CValidationState & state, int nFile, CDiskBlockPos& pos, unsigned int nAddSize)
        {
            pos.nFile = nFile;

            LOCK(cs_LastBlockFile);

            unsigned int nNewSize;
            pos.nPos = vinfoBlockFile[nFile].nUndoSize;
            nNewSize = vinfoBlockFile[nFile].nUndoSize += nAddSize;
            setDirtyFileInfo.insert(nFile);

            unsigned int nOldChunks = (pos.nPos + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
            unsigned int nNewChunks = (nNewSize + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
            if (nNewChunks > nOldChunks) {
                if (CheckDiskSpace(nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos)) {
                    FILE* file = OpenUndoFile(pos);
                    if (file) {
                        LogPrintf("Pre-allocating up to position 0x%x in rev%05u.dat\n", nNewChunks * UNDOFILE_CHUNK_SIZE, pos.nFile);
                        AllocateFileRange(file, pos.nPos, nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos);
                        fclose(file);
                    }
                } else
                    return state.Error("out of disk space");
            }

            return true;
        }

        bool CheckBlockHeader(const CBlockHeader& block, CValidationState& state, bool fCheckPOW)
        {
            // Check proof of work matches claimed amount
            if (fCheckPOW && !CheckProofOfWork(block.GetHash(), block.nBits))
                return state.DoS(50, error("CheckBlockHeader() : proof of work failed"),
                    REJECT_INVALID, "high-hash");

            return true;
        }

        static int GetWitnessCommitmentIndex(const CBlock& block);
        bool CheckBlock(const CBlock& block, CValidationState& state, bool fCheckPOW, bool fCheckMerkleRoot, bool fCheckSig)
        {
            // These are checks that are independent of context.

            // Check that the header is valid (particularly PoW).  This is mostly
            // redundant with the call in AcceptBlockHeader.
            if (!CheckBlockHeader(block, state, block.IsProofOfWork()))
                return state.DoS(100, error("CheckBlock() : CheckBlockHeader failed"),
                    REJECT_INVALID, "bad-header", true);

            // Check timestamp
            LogPrint("debug", "%s: block=%s  is proof of stake=%d\n", __func__, block.GetHash().ToString().c_str(), block.IsProofOfStake());
            if (block.GetBlockTime() > GetAdjustedTime() + (block.IsProofOfStake() ? 180 : 7200)) // 3 minute future drift for PoS
                return state.Invalid(error("CheckBlock() : block timestamp too far in the future"),
                    REJECT_INVALID, "time-too-new");

            // Check the merkle root.
            if (fCheckMerkleRoot) {
                bool mutated;
                uint256 hashMerkleRoot2 = block.BuildMerkleTree(&mutated);
                if (block.hashMerkleRoot != hashMerkleRoot2)
                    return state.DoS(100, error("CheckBlock() : hashMerkleRoot mismatch"),
                        REJECT_INVALID, "bad-txnmrklroot", true);

                // Check for merkle tree malleability (CVE-2012-2459): repeating sequences
                // of transactions in a block without affecting the merkle root of a block,
                // while still invalidating it.
                if (mutated)
                    return state.DoS(100, error("CheckBlock() : duplicate transaction"),
                        REJECT_INVALID, "bad-txns-duplicate", true);
            }

            // All potential-corruption validation must be done before we do any
            // transaction validation, as otherwise we may mark the header as invalid
            // because we receive the wrong transactions for it.
            // Note that witness malleability is checked in ContextualCheckBlock, so no
            // checks that use witness data may be performed here.

            // Size limits
            if (block.vtx.empty() || block.vtx.size() > MAX_BLOCK_BASE_SIZE || ::GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) > MAX_BLOCK_BASE_SIZE)
                return state.DoS(100, error("CheckBlock() : size limits failed"),
                    REJECT_INVALID, "bad-blk-length");

            // First transaction must be coinbase, the rest must not be
            if (block.vtx.empty() || !block.vtx[0].IsCoinBase())
                return state.DoS(100, error("CheckBlock() : first tx is not coinbase"),
                    REJECT_INVALID, "bad-cb-missing");
            for (unsigned int i = 1; i < block.vtx.size(); i++)
                if (block.vtx[i].IsCoinBase())
                    return state.DoS(100, error("CheckBlock() : more than one coinbase"),
                        REJECT_INVALID, "bad-cb-multiple");

            if (block.IsProofOfStake()) {
                int commitpos = GetWitnessCommitmentIndex(block);
                if (commitpos >= 0) {
                    if (IsSporkActive(SPORK_25_SEGWIT_ON_COINBASE)) {
                        if (block.vtx[0].vout.size() != 2)
                            return state.DoS(100, error("CheckBlock() : coinbase output has wrong size for proof-of-stake block"));
                        if (!block.vtx[0].vout[1].scriptPubKey.IsUnspendable())
                            return state.DoS(100, error("CheckBlock() : coinbase must be unspendable for proof-of-stake block"));
                    } else {
                        return state.DoS(100, error("CheckBlock() : staking-on-segwit is not enabled"));
                    }
                } else {
                    if (block.vtx[0].vout.size() != 1)
                        return state.DoS(100, error("CheckBlock() : coinbase output has wrong size for proof-of-stake block"));
                }
                // Coinbase output should be empty if proof-of-stake block
                if (!block.vtx[0].vout[0].IsEmpty())
                    return state.DoS(100, error("CheckBlock() : coinbase output not empty for proof-of-stake block"));

                // Second transaction must be coinstake, the rest must not be
                if (block.vtx.empty() || !block.vtx[1].IsCoinStake())
                    return state.DoS(100, error("CheckBlock() : second tx is not coinstake"));
                for (unsigned int i = 2; i < block.vtx.size(); i++)
                    if (block.vtx[i].IsCoinStake())
                        return state.DoS(100, error("CheckBlock() : more than one coinstake"));
            }

			// Credit to BarryStyle for this code used in Merge Project
			/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
            if (!IsInitialBlockDownload() &&
                masternodeSync.IsSynced()) {
                // extract collateral info from masternode list
                CMasternode* pmn = mnodeman.Find(block.vtx[1].vout[2].scriptPubKey);
                CTxDestination mnaddress;
                
                if (!ExtractDestination(block.vtx[1].vout[2].scriptPubKey, mnaddress))
                    LogPrintf("WARNING: unknown masternode type/address\n");
                //CBitcoinAddress mnpayee(mnaddress);
                std::string mnpayee = EncodeDestination(mnaddress);

                if (!pmn) {
                    LogPrintf("WARNING: unknown masternode has claimed output in this block (block: %d, payee %s)\n", chainActive.Height() + 1, mnpayee);
                } else {
                    // extract details from the masternode
                    uint256 nCollateralHash = pmn->vin.prevout.hash;
                    int nCollateralOut = pmn->vin.prevout.n;
                    // retrieve collateral transaction from disk
                    uint256 blockHash;
                    CTransaction nCollateralTx;
                    if (!GetTransaction(nCollateralHash, nCollateralTx, blockHash, true))
                        LogPrintf("WARNING: could not find collateral transaction for this masternode\n");
                    else
                        LogPrintf("Found masternode collateral (blockhash: %s txhash: %s vout: %d)\n",
                            blockHash.ToString().c_str(), nCollateralTx.GetHash().ToString().c_str(), nCollateralOut);
                }
            }
            /////////////////////////////////////////////////////////////////////////////////////////////////////////////////


            // ----------- swiftTX transaction scanning -----------
            if (IsSporkActive(SPORK_3_SWIFTTX_BLOCK_FILTERING)) {
                BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                    if (!tx.IsCoinBase()) {
                        //only reject blocks when it's based on complete consensus
                        BOOST_FOREACH (const CTxIn& in, tx.vin) {
                            if (mapLockedInputs.count(in.prevout)) {
                                if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                                    mapRejectedBlocks.insert(make_pair(block.GetHash(), GetTime()));
                                    LogPrintf("CheckBlock() : found conflicting transaction with transaction lock %s %s\n", mapLockedInputs[in.prevout].ToString(), tx.GetHash().ToString());
                                    return state.DoS(0, error("CheckBlock() : found conflicting transaction with transaction lock"),
                                        REJECT_INVALID, "conflicting-tx-ix");
                                }
                            }
                        }
                    }
                }
            } else {
                LogPrintf("CheckBlock() : skipping transaction locking checks\n");
            }

            // masternode payments / budgets
            CBlockIndex* pindexPrev = chainActive.Tip();
            int nHeight = 0;
            if (pindexPrev != NULL) {
                if (pindexPrev->GetBlockHash() == block.hashPrevBlock) {
                    nHeight = pindexPrev->nHeight + 1;
                } else { //out of order
                    BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
                    if (mi != mapBlockIndex.end() && (*mi).second)
                        nHeight = (*mi).second->nHeight + 1;
                }

                // Altbet
                // It is entierly possible that we don't have enough data and this could fail
                // (i.e. the block could indeed be valid). Store the block for later consideration
                // but issue an initial reject message.
                // The case also exists that the sending peer could not have enough data to see
                // that this block is invalid, so don't issue an outright ban.
                if (nHeight != 0 && !IsInitialBlockDownload()) {
                    if (!IsBlockPayeeValid(block, nHeight)) {
                        mapRejectedBlocks.insert(make_pair(block.GetHash(), GetTime()));
                        return state.DoS(0, error("CheckBlock() : Couldn't find masternode/budget payment"),
                            REJECT_INVALID, "bad-cb-payee");
                    }
                } else {
                    if (fDebug)
                        LogPrintf("CheckBlock(): Masternode payment check skipped on sync - skipping IsBlockPayeeValid()\n");
                }
            }


            unsigned int nSigOps = 0;
            BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                nSigOps += GetLegacySigOpCount(tx);
            }
            if (nSigOps * WITNESS_SCALE_FACTOR > MAX_BLOCK_SIGOPS_COST)
                return state.DoS(100, error("CheckBlock() : out-of-bounds SigOpCount"),
                    REJECT_INVALID, "bad-blk-sigops", true);

            return true;
        }

        // Modified according to Lux coin to make SegWit working
        bool CheckWork(const CBlock block, CBlockIndex* const pindexPrev)
        {
            const CChainParams& chainParams = Params();
            if (pindexPrev == NULL)
                return error("%s: null pindexPrev for block %s", __func__, block.GetHash().GetHex());

            unsigned int nBitsRequired = GetNextWorkRequired(pindexPrev, &block);

            if (block.IsProofOfWork() && pindexPrev->nHeight + 1 > chainParams.LAST_POW_BLOCK())
                return error("%s: reject proof-of-work at height %d", __func__, pindexPrev->nHeight + 1);

            if (block.nBits != nBitsRequired)
                return error("%s: incorrect proof of work at %d", __func__, pindexPrev->nHeight + 1);

            if (block.IsProofOfStake()) {
                uint256 hashProofOfStake;
                uint256 hash = block.GetHash();

                if (!CheckProofOfStake(block, hashProofOfStake)) {
                    LogPrintf("WARNING: ProcessBlock(): check proof-of-stake failed for block %s\n", hash.ToString().c_str());
                    return false;
                }
                if (!mapProofOfStake.count(hash)) // add to mapProofOfStake
                    mapProofOfStake.insert(make_pair(hash, hashProofOfStake));
            }
            return true;
        }

        bool ContextualCheckBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex* const pindexPrev)
        {
            uint256 hash = block.GetHash();

            if (hash == Params().HashGenesisBlock())
                return true;

            assert(pindexPrev);

            int nHeight = pindexPrev->nHeight + 1;

            //If this is a reorg, check that it is not too deep
            int nMaxReorgDepth = GetArg("-maxreorg", Params().MaxReorganizationDepth());
            if (chainActive.Height() - nHeight >= nMaxReorgDepth)
                return state.DoS(1, error("%s: forked chain older than max reorganization depth (height %d)", __func__, nHeight));

            // Check timestamp against prev
            if (block.GetBlockTime() <= pindexPrev->GetMedianTimePast()) {
                LogPrintf("Block time = %d , GetMedianTimePast = %d \n", block.GetBlockTime(), pindexPrev->GetMedianTimePast());
                return state.Invalid(error("%s : block's timestamp is too early", __func__),
                    REJECT_INVALID, "time-too-old");
            }

            // Check that the block chain matches the known block chain up to a checkpoint
            if (!Checkpoints::CheckBlock(nHeight, hash))
                return state.DoS(100, error("%s : rejected by checkpoint lock-in at %d", __func__, nHeight),
                    REJECT_CHECKPOINT, "checkpoint mismatch");

            // Don't accept any forks from the main chain prior to last checkpoint
            CBlockIndex* pcheckpoint = Checkpoints::GetLastCheckpoint();
            if (pcheckpoint && nHeight < pcheckpoint->nHeight)
                return state.DoS(0, error("%s : forked chain older than last checkpoint (height %d)", __func__, nHeight));

            // Reject block.nVersion=1 blocks when 95% (75% on testnet) of the network has upgraded:
            if (block.nVersion < 2 &&
                CBlockIndex::IsSuperMajority(2, pindexPrev, Params().RejectBlockOutdatedMajority())) {
                return state.Invalid(error("%s : rejected nVersion=1 block", __func__),
                    REJECT_OBSOLETE, "bad-version");
            }

            // Reject block.nVersion=2 blocks when 95% (75% on testnet) of the network has upgraded:
            if (block.nVersion < 3 && CBlockIndex::IsSuperMajority(3, pindexPrev, Params().RejectBlockOutdatedMajority())) {
                return state.Invalid(error("%s : rejected nVersion=2 block", __func__),
                    REJECT_OBSOLETE, "bad-version");
            }

            return true;
        }

        // Compute at which vout of the block's coinbase transaction the witness
        // commitment occurs, or -1 if not found.
        static int GetWitnessCommitmentIndex(const CBlock& block)
        {
            int commitpos = -1;
            if (block.vtx.size() > 1) {
                for (size_t o = 0; o < block.vtx[0].vout.size(); o++) {
                    if (block.vtx[0].vout[o].scriptPubKey.size() >= 38 && block.vtx[0].vout[o].scriptPubKey[0] == OP_RETURN && block.vtx[0].vout[o].scriptPubKey[1] == 0x24 && block.vtx[0].vout[o].scriptPubKey[2] == 0xaa && block.vtx[0].vout[o].scriptPubKey[3] == 0x21 && block.vtx[0].vout[o].scriptPubKey[4] == 0xa9 && block.vtx[0].vout[o].scriptPubKey[5] == 0xed) {
                        commitpos = o;
                    }
                }
            }
            return commitpos;
        }

        void UpdateUncommittedBlockStructures(CBlock & block, const CBlockIndex* pindexPrev)
        {
            int commitpos = GetWitnessCommitmentIndex(block);
            static const std::vector<unsigned char> nonce(32, 0x00);
            if (commitpos != -1 && GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < pindexPrev->nTime && block.vtx[0].wit.IsEmpty()) {
                block.vtx[0].wit.vtxinwit.resize(1);
                block.vtx[0].wit.vtxinwit[0].scriptWitness.stack.resize(1);
                block.vtx[0].wit.vtxinwit[0].scriptWitness.stack[0] = nonce;
            }
        }

        std::vector<unsigned char> GenerateCoinbaseCommitment(CBlock & block, const CBlockIndex* pindexPrev)
        {
            std::vector<unsigned char> commitment;
            int commitpos = GetWitnessCommitmentIndex(block);
            bool fHaveWitness = false;
            for (size_t t = 1; t < block.vtx.size(); t++) {
                if (!block.vtx[t].wit.IsNull()) {
                    fHaveWitness = true;
                    break;
                }
            }
            std::vector<unsigned char> ret(32, 0x00);
            if (fHaveWitness && GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < pindexPrev->nTime) {
                if (commitpos == -1) {
                    uint256 witnessroot = BlockWitnessMerkleRoot(block, NULL);
                    CHash256().Write(witnessroot.begin(), 32).Write(&ret[0], 32).Finalize(witnessroot.begin());
                    CTxOut out;
                    out.nValue = 0;
                    out.scriptPubKey.resize(38);
                    out.scriptPubKey[0] = OP_RETURN;
                    out.scriptPubKey[1] = 0x24;
                    out.scriptPubKey[2] = 0xaa;
                    out.scriptPubKey[3] = 0x21;
                    out.scriptPubKey[4] = 0xa9;
                    out.scriptPubKey[5] = 0xed;
                    memcpy(&out.scriptPubKey[6], witnessroot.begin(), 32);
                    commitment = std::vector<unsigned char>(out.scriptPubKey.begin(), out.scriptPubKey.end());
                    const_cast<std::vector<CTxOut>*>(&block.vtx[0].vout)->push_back(out);
                    block.vtx[0].UpdateHash();
                }
            }
            UpdateUncommittedBlockStructures(block, pindexPrev);
            return commitment;
        }

        bool IsBlockHashInChain(const uint256& hashBlock)
        {
            if (hashBlock == 0 || !mapBlockIndex.count(hashBlock))
                return false;

            return chainActive.Contains(mapBlockIndex[hashBlock]);
        }

        bool IsTransactionInChain(const uint256& txId, int& nHeightTx, CTransaction& tx)
        {
            uint256 hashBlock;
            if (!GetTransaction(txId, tx, hashBlock, true))
                return false;
            if (!IsBlockHashInChain(hashBlock))
                return false;

            nHeightTx = mapBlockIndex.at(hashBlock)->nHeight;
            return true;
        }

        bool IsTransactionInChain(const uint256& txId, int& nHeightTx)
        {
            CTransaction tx;
            return IsTransactionInChain(txId, nHeightTx, tx);
        }

        bool ContextualCheckBlock(const CBlock& block, CValidationState& state, CBlockIndex* const pindexPrev)
        {
            const int nHeight = pindexPrev == NULL ? 0 : pindexPrev->nHeight + 1;

            // Version 4 header must be used after Params().Zerocoin_StartHeight(). And never before.
            if (nHeight > Params().Zerocoin_StartHeight()) {
                if (block.nVersion < Params().Zerocoin_HeaderVersion())
                    return state.DoS(50, error("CheckBlockHeader() : block version must be above 4 after ZerocoinStartHeight"),
                        REJECT_INVALID, "block-version");

                vector<CBigNum> vBlockSerials;
                for (const CTransaction& tx : block.vtx) {
                    if (!CheckTransaction(tx, true, chainActive.Height() + 1 >= Params().Zerocoin_StartHeight(), state, GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < block.nTime))
                        return error("CheckBlock() : CheckTransaction failed");

                    // double check that there are no double spent zABET spends in this block
                    if (tx.IsZerocoinSpend()) {
                        for (const CTxIn txIn : tx.vin) {
                            if (txIn.scriptSig.IsZerocoinSpend()) {
                                libzerocoin::CoinSpend spend = TxInToZerocoinSpend(txIn);
                                if (count(vBlockSerials.begin(), vBlockSerials.end(), spend.getCoinSerialNumber()))
                                    return state.DoS(100, error("%s : Double spending of zABET serial %s in block\n Block: %s",
                                                              __func__, spend.getCoinSerialNumber().GetHex(), block.ToString()));
                                vBlockSerials.emplace_back(spend.getCoinSerialNumber());
                            }
                        }
                    }
                }
                //} else {
                //if (block.nVersion >= Params().Zerocoin_HeaderVersion())
                //return state.DoS(50, error("CheckBlockHeader() : block version must be below 4 before ZerocoinStartHeight"),
                //REJECT_INVALID, "block-version");
            }

            // Check that all transactions are finalized
            BOOST_FOREACH (const CTransaction& tx, block.vtx)
                if (!IsFinalTx(tx, nHeight, block.GetBlockTime())) {
                    return state.DoS(10, error("%s : contains a non-final transaction", __func__), REJECT_INVALID, "bad-txns-nonfinal");
                }

            // Enforce block.nVersion=2 rule that the coinbase starts with serialized block height
            // if 750 of the last 1,000 blocks are version 2 or greater (51/100 if testnet):
            if (block.nVersion >= 2 &&
                CBlockIndex::IsSuperMajority(2, pindexPrev, Params().EnforceBlockUpgradeMajority())) {
                CScript expect = CScript() << nHeight;
                if (block.vtx[0].vin[0].scriptSig.size() < expect.size() ||
                    !std::equal(expect.begin(), expect.end(), block.vtx[0].vin[0].scriptSig.begin())) {
                    return state.DoS(100, error("%s : block height mismatch in coinbase", __func__), REJECT_INVALID, "bad-cb-height");
                }
            }

            // Validation for witness commitments.
            // * We compute the witness hash (which is the hash including witnesses) of all the block's transactions, except the
            //   coinbase (where 0x0000....0000 is used instead).
            // * The coinbase scriptWitness is a stack of a single 32-byte vector, containing a witness nonce (unconstrained).
            // * We build a merkle tree with all those witness hashes as leaves (similar to the hashMerkleRoot in the block header).
            // * There must be at least one output whose scriptPubKey is a single 36-byte push, the first 4 bytes of which are
            //   {0xaa, 0x21, 0xa9, 0xed}, and the following 32 bytes are SHA256(witness root, witness nonce). In case there are
            //   multiple, the last one is used.
            bool fHaveWitness = false;
            if (GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < pindexPrev->nTime) {
                int commitpos = GetWitnessCommitmentIndex(block);
                if (commitpos != -1) {
                    if (!IsSporkActive(SPORK_25_SEGWIT_ON_COINBASE)) {
                        if (fDebug) {
                            LogPrintf("CheckBlock() : staking-on-segwit is not enabled.\n");
                        }
                        return false;
                    }


                    bool malleated = false;
                    uint256 hashWitness = BlockWitnessMerkleRoot(block, &malleated);
                    // The malleation check is ignored; as the transaction tree itself
                    // already does not permit it, it is impossible to trigger in the
                    // witness tree.
                    if (block.vtx[0].wit.vtxinwit.size() != 1 || block.vtx[0].wit.vtxinwit[0].scriptWitness.stack.size() != 1 || block.vtx[0].wit.vtxinwit[0].scriptWitness.stack[0].size() != 32) {
                        return state.DoS(100, error("%s : invalid witness nonce size", __func__), REJECT_INVALID, "bad-witness-nonce-size", true);
                    }
                    CHash256().Write(hashWitness.begin(), 32).Write(&block.vtx[0].wit.vtxinwit[0].scriptWitness.stack[0][0], 32).Finalize(hashWitness.begin());
                    if (memcmp(hashWitness.begin(), &block.vtx[0].vout[commitpos].scriptPubKey[6], 32)) {
                        return state.DoS(100, error("%s : witness merkle commitment mismatch", __func__), REJECT_INVALID, "bad-witness-merkle-match", true);
                    }
                    fHaveWitness = true;
                }
            }

            // No witness data is allowed in blocks that don't commit to witness data, as this would otherwise leave room for spam
            if (!fHaveWitness) {
                for (size_t i = 0; i < block.vtx.size(); i++) {
                    if (!block.vtx[i].wit.IsNull()) {
                        return state.DoS(100, error("%s : unexpected witness data found", __func__), REJECT_INVALID, "unexpected-witness", true);
                    }
                }
            }

            // After the coinbase witness nonce and commitment are verified,
            // we can check if the block cost passes (before we've checked the
            // coinbase witness, it would be possible for the cost to be too
            // large by filling up the coinbase witness, which doesn't change
            // the block hash, so we couldn't mark the block as permanently
            // failed).
            if (GetBlockCost(block) > MAX_BLOCK_COST) {
                return state.DoS(100, error("ContextualCheckBlock(): cost limit failed"), REJECT_INVALID, "bad-blk-cost");
            }

            return true;
        }

        bool AcceptBlockHeader(const CBlock& block, CValidationState& state, CBlockIndex** ppindex)
        {
            AssertLockHeld(cs_main);
            // Check for duplicate
            uint256 hash = block.GetHash();
            BlockMap::iterator miSelf = mapBlockIndex.find(hash);
            CBlockIndex* pindex = NULL;

            // TODO : ENABLE BLOCK CACHE IN SPECIFIC CASES
            if (miSelf != mapBlockIndex.end()) {
                // Block header is already known.
                pindex = miSelf->second;
                if (ppindex)
                    *ppindex = pindex;
                if (pindex->nStatus & BLOCK_FAILED_MASK)
                    return state.Invalid(error("%s : block is marked invalid", __func__), 0, "duplicate");
                return true;
            }

            if (!CheckBlockHeader(block, state, false)) {
                LogPrintf("AcceptBlockHeader(): CheckBlockHeader failed \n");
                return false;
            }

            // Get prev block index
            CBlockIndex* pindexPrev = NULL;
            if (hash != Params().HashGenesisBlock()) {
                BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
                if (mi == mapBlockIndex.end())
                    return state.DoS(0, error("%s : prev block %s not found", __func__, block.hashPrevBlock.ToString().c_str()), 0, "bad-prevblk");
                pindexPrev = (*mi).second;
                if (pindexPrev->nStatus & BLOCK_FAILED_MASK) {
                    //If this "invalid" block is an exact match from the checkpoints, then reconsider it
                    if (pindex && Checkpoints::CheckBlock(pindex->nHeight - 1, block.hashPrevBlock, true)) {
                        LogPrintf("%s : Reconsidering block %s height %d\n", __func__, pindexPrev->GetBlockHash().GetHex(), pindexPrev->nHeight);
                        CValidationState statePrev;
                        ReconsiderBlock(statePrev, pindexPrev);
                        if (statePrev.IsValid()) {
                            ActivateBestChain(statePrev);
                            return true;
                        }
                    }

                    return state.DoS(100, error("%s : prev block height=%d hash=%s is invalid, unable to add block %s", __func__, pindexPrev->nHeight, block.hashPrevBlock.GetHex(), block.GetHash().GetHex()),
                        REJECT_INVALID, "bad-prevblk");
                }
            }

            if (!ContextualCheckBlockHeader(block, state, pindexPrev))
                return false;

            if (pindex == NULL)
                pindex = AddToBlockIndex(block);

            if (ppindex)
                *ppindex = pindex;

            return true;
        }

        bool AcceptBlock(CBlock & block, CValidationState & state, CBlockIndex * *ppindex, CDiskBlockPos * dbp, bool fAlreadyCheckedBlock)
        {
            AssertLockHeld(cs_main);

            CBlockIndex*& pindex = *ppindex;

            // Get prev block index
            CBlockIndex* pindexPrev = NULL;
            if (block.GetHash() != Params().HashGenesisBlock()) {
                BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
                if (mi == mapBlockIndex.end())
                    return state.DoS(0, error("%s : prev block %s not found", __func__, block.hashPrevBlock.ToString().c_str()), 0, "bad-prevblk");
                pindexPrev = (*mi).second;
                if (pindexPrev->nStatus & BLOCK_FAILED_MASK) {
                    //If this "invalid" block is an exact match from the checkpoints, then reconsider it
                    if (Checkpoints::CheckBlock(pindexPrev->nHeight, block.hashPrevBlock, true)) {
                        LogPrintf("%s : Reconsidering block %s height %d\n", __func__, pindexPrev->GetBlockHash().GetHex(), pindexPrev->nHeight);
                        CValidationState statePrev;
                        ReconsiderBlock(statePrev, pindexPrev);
                        if (statePrev.IsValid()) {
                            ActivateBestChain(statePrev);
                            return true;
                        }
                    }
                    return state.DoS(100, error("%s : prev block %s is invalid, unable to add block %s", __func__, block.hashPrevBlock.GetHex(), block.GetHash().GetHex()),
                        REJECT_INVALID, "bad-prevblk");
                }
            }

            if (block.GetHash() != Params().HashGenesisBlock() && !CheckWork(block, pindexPrev))
                return false;

            if (!AcceptBlockHeader(block, state, &pindex))
                return false;

            if (pindex->nStatus & BLOCK_HAVE_DATA) {
                // TODO: deal better with duplicate blocks.
                // return state.DoS(20, error("AcceptBlock() : already have block %d %s", pindex->nHeight, pindex->GetBlockHash().ToString()), REJECT_DUPLICATE, "duplicate");
                return true;
            }

            if ((!fAlreadyCheckedBlock && !CheckBlock(block, state)) || !ContextualCheckBlock(block, state, pindex->pprev)) {
                if (state.IsInvalid() && !state.CorruptionPossible()) {
                    pindex->nStatus |= BLOCK_FAILED_VALID;
                    setDirtyBlockIndex.insert(pindex);
                }
                return false;
            }

            int nHeight = pindex->nHeight;

            if (block.IsProofOfStake()) {
                LOCK(cs_main);

                CCoinsViewCache coins(pcoinsTip);

                if (!coins.HaveInputs(block.vtx[1])) {
                    // the inputs are spent at the chain tip so we should look at the recently spent outputs

                    for (CTxIn in : block.vtx[1].vin) {
                        auto it = mapStakeSpent.find(in.prevout);
                        if (it == mapStakeSpent.end()) {
                            return false;
                        }
                        if (it->second < pindexPrev->nHeight) {
                            return false;
                        }
                    }
                }

                // if this is on a fork
                if (!chainActive.Contains(pindexPrev) && pindexPrev != NULL) {
                    // start at the block we're adding on to
                    CBlockIndex* last = pindexPrev;

                    // while that block is not on the main chain
                    while (!chainActive.Contains(last) && last != NULL) {
                        CBlock bl;
                        ReadBlockFromDisk(bl, last);
                        // loop through every spent input from said block
                        for (CTransaction t : bl.vtx) {
                            for (CTxIn in : t.vin) {
                                // loop through every spent input in the staking transaction of the new block
                                for (CTxIn stakeIn : block.vtx[1].vin) {
                                    // if they spend the same input
                                    if (stakeIn.prevout == in.prevout) {
                                        // reject the block
                                        return false;
                                    }
                                }
                            }
                        }

                        // go to the parent block
                        last = last->pprev;
                    }
                }
            }

            // Write block to history file
            try {
                unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
                CDiskBlockPos blockPos;
                if (dbp != NULL)
                    blockPos = *dbp;
                if (!FindBlockPos(state, blockPos, nBlockSize + 8, nHeight, block.GetBlockTime(), dbp != NULL))
                    return error("AcceptBlock() : FindBlockPos failed");
                if (dbp == NULL)
                    if (!WriteBlockToDisk(block, blockPos))
                        return state.Error("Failed to write block");
                if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
                    return error("AcceptBlock() : ReceivedBlockTransactions failed");
            } catch (std::runtime_error& e) {
                return state.Error(std::string("System error: ") + e.what());
            }

            return true;
        }

        bool CBlockIndex::IsSuperMajority(int minVersion, const CBlockIndex* pstart, unsigned int nRequired)
        {
            unsigned int nToCheck = Params().ToCheckBlockUpgradeMajority();
            unsigned int nFound = 0;
            for (unsigned int i = 0; i < nToCheck && nFound < nRequired && pstart != NULL; i++) {
                if (pstart->nVersion >= minVersion)
                    ++nFound;
                pstart = pstart->pprev;
            }
            return (nFound >= nRequired);
        }

        /** Turn the lowest '1' bit in the binary representation of a number into a '0'. */
        int static inline InvertLowestOne(int n) { return n & (n - 1); }

        /** Compute what height to jump back to with the CBlockIndex::pskip pointer. */
        int static inline GetSkipHeight(int height)
        {
            if (height < 2)
                return 0;

            // Determine which height to jump back to. Any number strictly lower than height is acceptable,
            // but the following expression seems to perform well in simulations (max 110 steps to go back
            // up to 2**18 blocks).
            return (height & 1) ? InvertLowestOne(InvertLowestOne(height - 1)) + 1 : InvertLowestOne(height);
        }

        CBlockIndex* CBlockIndex::GetAncestor(int height)
        {
            if (height > nHeight || height < 0)
                return NULL;

            CBlockIndex* pindexWalk = this;
            int heightWalk = nHeight;
            while (heightWalk > height) {
                int heightSkip = GetSkipHeight(heightWalk);
                int heightSkipPrev = GetSkipHeight(heightWalk - 1);
                if (heightSkip == height ||
                    (heightSkip > height && !(heightSkipPrev < heightSkip - 2 && heightSkipPrev >= height))) {
                    // Only follow pskip if pprev->pskip isn't better than pskip->pprev.
                    pindexWalk = pindexWalk->pskip;
                    heightWalk = heightSkip;
                } else {
                    pindexWalk = pindexWalk->pprev;
                    heightWalk--;
                }
            }
            return pindexWalk;
        }

        const CBlockIndex* CBlockIndex::GetAncestor(int height) const
        {
            return const_cast<CBlockIndex*>(this)->GetAncestor(height);
        }

        void CBlockIndex::BuildSkip()
        {
            if (pprev)
                pskip = pprev->GetAncestor(GetSkipHeight(nHeight));
        }

        bool ProcessNewBlock(CValidationState & state, CNode * pfrom, CBlock * pblock, CDiskBlockPos * dbp)
        {
            // Preliminary checks
            int64_t nStartTime = GetTimeMillis();
            bool checked = CheckBlock(*pblock, state);

            int nMints = 0;
            int nSpends = 0;
            for (const CTransaction tx : pblock->vtx) {
                if (tx.ContainsZerocoins()) {
                    for (const CTxIn in : tx.vin) {
                        if (in.scriptSig.IsZerocoinSpend())
                            nSpends++;
                    }
                    for (const CTxOut out : tx.vout) {
                        if (out.IsZerocoinMint())
                            nMints++;
                    }
                }
            }
            if (nMints || nSpends)
                LogPrintf("%s : block contains %d zABET mints and %d zABET spends\n", __func__, nMints, nSpends);

            // ppcoin: check proof-of-stake
            // Limited duplicity on stake: prevents block flood attack
            // Duplicate stake allowed only when there is orphan child block
            //if (pblock->IsProofOfStake() && setStakeSeen.count(pblock->GetProofOfStake())/* && !mapOrphanBlocksByPrev.count(hash)*/)
            //    return error("ProcessNewBlock() : duplicate proof-of-stake (%s, %d) for block %s", pblock->GetProofOfStake().first.ToString().c_str(), pblock->GetProofOfStake().second, pblock->GetHash().ToString().c_str());

            // NovaCoin: check proof-of-stake block signature
            if (!pblock->CheckBlockSignature())
                return error("ProcessNewBlock() : bad proof-of-stake block signature");

            if (pblock->GetHash() != Params().HashGenesisBlock() && pfrom != NULL) {
                //if we get this far, check if the prev block is our prev block, if not then request sync and return false
                BlockMap::iterator mi = mapBlockIndex.find(pblock->hashPrevBlock);
                if (mi == mapBlockIndex.end()) {
                    pfrom->PushMessage(NetMsgType::GETBLOCKS, chainActive.GetLocator(), uint256(0));
                    return false;
                }
            }

            {
                LOCK(cs_main); // Replaces the former TRY_LOCK loop because busy waiting wastes too much resources

                MarkBlockAsReceived(pblock->GetHash());
                if (!checked) {
                    return error("%s : CheckBlock FAILED for block %s", __func__, pblock->GetHash().GetHex());
                }

                // Store to disk
                CBlockIndex* pindex = NULL;
                bool ret = AcceptBlock(*pblock, state, &pindex, dbp, checked);
                if (pindex && pfrom) {
                    mapBlockSource[pindex->GetBlockHash()] = pfrom->GetId();
                }
                CheckBlockIndex();
                if (!ret)
                    return error("%s : AcceptBlock FAILED", __func__);
            }

            if (!ActivateBestChain(state, pblock, checked))
                return error("%s : ActivateBestChain failed", __func__);

            if (!fLiteMode) {
                if (masternodeSync.RequestedMasternodeAssets > MASTERNODE_SYNC_LIST) {
                    obfuScationPool.NewBlock();
                    masternodePayments.ProcessBlock(GetHeight() + 10);
                    budget.NewBlock();
                }
            }

            if (pwalletMain) {
                // If turned on MultiSend will send a transaction (or more) on the after maturity of a stake
                if (pwalletMain->isMultiSendEnabled())
                    pwalletMain->MultiSend();

                // If turned on Auto Combine will scan wallet for dust to combine
                if (pwalletMain->fCombineDust)
                    pwalletMain->AutoCombineDust();
            }

            LogPrintf("%s : ACCEPTED in %ld milliseconds with size=%d\n", __func__, GetTimeMillis() - nStartTime,
                pblock->GetSerializeSize(SER_DISK, CLIENT_VERSION));

            return true;
        }

        bool TestBlockValidity(CValidationState & state, const CBlock& block, CBlockIndex* const pindexPrev, bool fCheckPOW, bool fCheckMerkleRoot)
        {
            AssertLockHeld(cs_main);
            assert(pindexPrev == chainActive.Tip());

            CCoinsViewCache viewNew(pcoinsTip);
            CBlockIndex indexDummy(block);
            indexDummy.pprev = pindexPrev;
            indexDummy.nHeight = pindexPrev->nHeight + 1;

            // NOTE: CheckBlockHeader is called by CheckBlock
            if (!ContextualCheckBlockHeader(block, state, pindexPrev))
                return false;
            if (!CheckBlock(block, state, fCheckPOW, fCheckMerkleRoot))
                return false;
            if (!ContextualCheckBlock(block, state, pindexPrev))
                return false;
            if (!ConnectBlock(block, state, &indexDummy, viewNew, true))
                return false;
            assert(state.IsValid());

            return true;
        }


        bool AbortNode(const std::string& strMessage, const std::string& userMessage)
        {
            strMiscWarning = strMessage;
            LogPrintf("*** %s\n", strMessage);
            uiInterface.ThreadSafeMessageBox(
                userMessage.empty() ? _("Error: A fatal internal error occured, see debug.log for details") : userMessage,
                "", CClientUIInterface::MSG_ERROR);
            StartShutdown();
            return false;
        }

        bool CheckDiskSpace(uint64_t nAdditionalBytes)
        {
            uint64_t nFreeBytesAvailable = filesystem::space(GetDataDir()).available;

            // Check for nMinDiskSpace bytes (currently 50MB)
            if (nFreeBytesAvailable < nMinDiskSpace + nAdditionalBytes)
                return AbortNode("Disk space is low!", _("Error: Disk space is low!"));

            return true;
        }

        FILE* OpenDiskFile(const CDiskBlockPos& pos, const char* prefix, bool fReadOnly)
        {
            if (pos.IsNull())
                return NULL;
            boost::filesystem::path path = GetBlockPosFilename(pos, prefix);
            boost::filesystem::create_directories(path.parent_path());
            FILE* file = fopen(path.string().c_str(), "rb+");
            if (!file && !fReadOnly)
                file = fopen(path.string().c_str(), "wb+");
            if (!file) {
                LogPrintf("Unable to open file %s\n", path.string());
                return NULL;
            }
            if (pos.nPos) {
                if (fseek(file, pos.nPos, SEEK_SET)) {
                    LogPrintf("Unable to seek to position %u of %s\n", pos.nPos, path.string());
                    fclose(file);
                    return NULL;
                }
            }
            return file;
        }

        FILE* OpenBlockFile(const CDiskBlockPos& pos, bool fReadOnly)
        {
            return OpenDiskFile(pos, "blk", fReadOnly);
        }

        FILE* OpenUndoFile(const CDiskBlockPos& pos, bool fReadOnly)
        {
            return OpenDiskFile(pos, "rev", fReadOnly);
        }

        boost::filesystem::path GetBlockPosFilename(const CDiskBlockPos& pos, const char* prefix)
        {
            return GetDataDir() / "blocks" / strprintf("%s%05u.dat", prefix, pos.nFile);
        }

        CBlockIndex* InsertBlockIndex(uint256 hash)
        {
            if (hash == 0)
                return NULL;

            // Return existing
            BlockMap::iterator mi = mapBlockIndex.find(hash);
            if (mi != mapBlockIndex.end())
                return (*mi).second;

            // Create new
            CBlockIndex* pindexNew = new CBlockIndex();
            if (!pindexNew)
                throw runtime_error("LoadBlockIndex() : new CBlockIndex failed");
            mi = mapBlockIndex.insert(make_pair(hash, pindexNew)).first;

            //mark as PoS seen
            if (pindexNew->IsProofOfStake())
                setStakeSeen.insert(make_pair(pindexNew->prevoutStake, pindexNew->nStakeTime));

            pindexNew->phashBlock = &((*mi).first);

            return pindexNew;
        }

        bool static LoadBlockIndexDB(string & strError)
        {
            if (!pblocktree->LoadBlockIndexGuts())
                return false;

            boost::this_thread::interruption_point();

            // Calculate nChainWork
            vector<pair<int, CBlockIndex*> > vSortedByHeight;
            vSortedByHeight.reserve(mapBlockIndex.size());
            for (const PAIRTYPE(uint256, CBlockIndex*) & item : mapBlockIndex) {
                CBlockIndex* pindex = item.second;
                vSortedByHeight.push_back(make_pair(pindex->nHeight, pindex));
            }
            sort(vSortedByHeight.begin(), vSortedByHeight.end());
            BOOST_FOREACH (const PAIRTYPE(int, CBlockIndex*) & item, vSortedByHeight) {
                CBlockIndex* pindex = item.second;
                pindex->nChainWork = (pindex->pprev ? pindex->pprev->nChainWork : 0) + GetBlockProof(*pindex);
                if (pindex->nStatus & BLOCK_HAVE_DATA) {
                    if (pindex->pprev) {
                        if (pindex->pprev->nChainTx) {
                            pindex->nChainTx = pindex->pprev->nChainTx + pindex->nTx;
                        } else {
                            pindex->nChainTx = 0;
                            mapBlocksUnlinked.insert(std::make_pair(pindex->pprev, pindex));
                        }
                    } else {
                        pindex->nChainTx = pindex->nTx;
                    }
                }
                if (pindex->IsValid(BLOCK_VALID_TRANSACTIONS) && (pindex->nChainTx || pindex->pprev == NULL))
                    setBlockIndexCandidates.insert(pindex);
                if (pindex->nStatus & BLOCK_FAILED_MASK && (!pindexBestInvalid || pindex->nChainWork > pindexBestInvalid->nChainWork))
                    pindexBestInvalid = pindex;
                if (pindex->pprev)
                    pindex->BuildSkip();
                if (pindex->IsValid(BLOCK_VALID_TREE) && (pindexBestHeader == NULL || CBlockIndexWorkComparator()(pindexBestHeader, pindex)))
                    pindexBestHeader = pindex;
            }

            // Load block file info
            pblocktree->ReadLastBlockFile(nLastBlockFile);
            vinfoBlockFile.resize(nLastBlockFile + 1);
            LogPrintf("%s: last block file = %i\n", __func__, nLastBlockFile);
            for (int nFile = 0; nFile <= nLastBlockFile; nFile++) {
                pblocktree->ReadBlockFileInfo(nFile, vinfoBlockFile[nFile]);
            }
            LogPrintf("%s: last block file info: %s\n", __func__, vinfoBlockFile[nLastBlockFile].ToString());
            for (int nFile = nLastBlockFile + 1; true; nFile++) {
                CBlockFileInfo info;
                if (pblocktree->ReadBlockFileInfo(nFile, info)) {
                    vinfoBlockFile.push_back(info);
                } else {
                    break;
                }
            }

            // Check presence of blk files
            LogPrintf("Checking all blk files are present...\n");
            set<int> setBlkDataFiles;
            for (const PAIRTYPE(uint256, CBlockIndex*) & item : mapBlockIndex) {
                CBlockIndex* pindex = item.second;
                if (pindex->nStatus & BLOCK_HAVE_DATA) {
                    setBlkDataFiles.insert(pindex->nFile);
                }
            }
            for (std::set<int>::iterator it = setBlkDataFiles.begin(); it != setBlkDataFiles.end(); it++) {
                CDiskBlockPos pos(*it, 0);
                if (CAutoFile(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION).IsNull()) {
                    return false;
                }
            }

            //Check if the shutdown procedure was followed on last client exit
            bool fLastShutdownWasPrepared = true;
            pblocktree->ReadFlag("shutdown", fLastShutdownWasPrepared);
            LogPrintf("%s: Last shutdown was prepared: %s\n", __func__, fLastShutdownWasPrepared);

            // Check whether we need to continue reindexing
            bool fReindexing = false;
            pblocktree->ReadReindexing(fReindexing);
            fReindex |= fReindexing;

            // Check whether we have a transaction index
            pblocktree->ReadFlag("txindex", fTxIndex);
            LogPrintf("LoadBlockIndexDB(): transaction index %s\n", fTxIndex ? "enabled" : "disabled");

            pblocktree->ReadFlag("addrindex", fAddrIndex);
            LogPrintf("LoadBlockIndexDB(): address index %s\n", fAddrIndex ? "enabled" : "disabled");

            // If this is written true before the next client init, then we know the shutdown process failed
            pblocktree->WriteFlag("shutdown", false);

            // Load pointer to end of best chain
            BlockMap::iterator it = mapBlockIndex.find(pcoinsTip->GetBestBlock());
            if (it == mapBlockIndex.end())
                return true;
            chainActive.SetTip(it->second);

            PruneBlockIndexCandidates();

            LogPrintf("LoadBlockIndexDB(): hashBestChain=%s height=%d date=%s progress=%f\n",
                chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(),
                DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
                Checkpoints::GuessVerificationProgress(chainActive.Tip()));

            return true;
        }

        CVerifyDB::CVerifyDB()
        {
            uiInterface.ShowProgress(_("Verifying blocks..."), 0);
        }

        CVerifyDB::~CVerifyDB()
        {
            uiInterface.ShowProgress("", 100);
        }

        bool CVerifyDB::VerifyDB(CCoinsView * coinsview, int nCheckLevel, int nCheckDepth)
        {
            LOCK(cs_main);
            if (chainActive.Tip() == NULL || chainActive.Tip()->pprev == NULL)
                return true;

            // Verify blocks in the best chain
            if (nCheckDepth <= 0)
                nCheckDepth = 1000000000; // suffices until the year 19000
            if (nCheckDepth > chainActive.Height())
                nCheckDepth = chainActive.Height();
            nCheckLevel = std::max(0, std::min(4, nCheckLevel));
            LogPrintf("Verifying last %i blocks at level %i\n", nCheckDepth, nCheckLevel);
            CCoinsViewCache coins(coinsview);
            CBlockIndex* pindexState = chainActive.Tip();
            CBlockIndex* pindexFailure = NULL;
            int nGoodTransactions = 0;
            CValidationState state;
            for (CBlockIndex* pindex = chainActive.Tip(); pindex && pindex->pprev; pindex = pindex->pprev) {
                boost::this_thread::interruption_point();
                uiInterface.ShowProgress(_("Verifying blocks..."), std::max(1, std::min(99, (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * (nCheckLevel >= 4 ? 50 : 100)))));
                if (pindex->nHeight < chainActive.Height() - nCheckDepth)
                    break;
                CBlock block;
                // check level 0: read from disk
                if (!ReadBlockFromDisk(block, pindex))
                    return error("VerifyDB() : *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
                // check level 1: verify block validity
                if (nCheckLevel >= 1 && !CheckBlock(block, state))
                    return error("VerifyDB() : *** found bad block at %d, hash=%s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                // check level 2: verify undo validity
                if (nCheckLevel >= 2 && pindex) {
                    CBlockUndo undo;
                    CDiskBlockPos pos = pindex->GetUndoPos();
                    if (!pos.IsNull()) {
                        if (!undo.ReadFromDisk(pos, pindex->pprev->GetBlockHash()))
                            return error("VerifyDB() : *** found bad undo data at %d, hash=%s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                    }
                }
                // check level 3: check for inconsistencies during memory-only disconnect of tip blocks
                if (nCheckLevel >= 3 && pindex == pindexState && (coins.GetCacheSize() + pcoinsTip->GetCacheSize()) <= nCoinCacheSize) {
                    bool fClean = true;
                    if (!DisconnectBlock(block, state, pindex, coins, &fClean))
                        return error("VerifyDB() : *** irrecoverable inconsistency in block data at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
                    pindexState = pindex->pprev;
                    if (!fClean) {
                        nGoodTransactions = 0;
                        pindexFailure = pindex;
                    } else
                        nGoodTransactions += block.vtx.size();
                }
                if (ShutdownRequested())
                    return true;
            }
            if (pindexFailure)
                return error("VerifyDB() : *** coin database inconsistencies found (last %i blocks, %i good transactions before that)\n", chainActive.Height() - pindexFailure->nHeight + 1, nGoodTransactions);

            // check level 4: try reconnecting blocks
            if (nCheckLevel >= 4) {
                CBlockIndex* pindex = pindexState;
                while (pindex != chainActive.Tip()) {
                    boost::this_thread::interruption_point();
                    uiInterface.ShowProgress(_("Verifying blocks..."), std::max(1, std::min(99, 100 - (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * 50))));
                    pindex = chainActive.Next(pindex);
                    CBlock block;
                    if (!ReadBlockFromDisk(block, pindex))
                        return error("VerifyDB() : *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
                    if (!ConnectBlock(block, state, pindex, coins, false))
                        return error("VerifyDB() : *** found unconnectable block at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
                }
            }

            LogPrintf("No coin database inconsistencies in last %i blocks (%i transactions)\n", chainActive.Height() - pindexState->nHeight, nGoodTransactions);

            return true;
        }

        bool RewindBlockIndex(const CChainParams& params)
        {
            LOCK(cs_main);

            int nHeight = 1;
            while (nHeight <= chainActive.Height()) {
                if (GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < chainActive[nHeight - 1]->nTime && !(chainActive[nHeight]->nStatus & BLOCK_OPT_WITNESS)) {
                    break;
                }
                nHeight++;
            }

            // nHeight is now the height of the first insufficiently-validated block, or tipheight + 1
            CValidationState state;
            CBlockIndex* pindex = chainActive.Tip();
            while (chainActive.Height() >= nHeight) {
                if (!DisconnectTip(state, true)) {
                    return error("RewindBlockIndex: unable to disconnect block at height %i", pindex->nHeight);
                }
                // Occasionally flush state to disk.
                if (!FlushStateToDisk(state, FLUSH_STATE_PERIODIC))
                    return false;
            }

            // Reduce validity flag and have-data flags.
            // We do this after actual disconnecting, otherwise we'll end up writing the lack of data
            // to disk before writing the chainstate, resulting in a failure to continue if interrupted.
            for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); it++) {
                CBlockIndex* pindexIter = it->second;
                if (GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) < pindexIter->nTime && !(pindexIter->nStatus & BLOCK_OPT_WITNESS)) {
                    // Reduce validity
                    pindexIter->nStatus = std::min<unsigned int>(pindexIter->nStatus & BLOCK_VALID_MASK, BLOCK_VALID_TREE) | (pindexIter->nStatus & ~BLOCK_VALID_MASK);
                    // Remove have-data flags.
                    pindexIter->nStatus &= ~(BLOCK_HAVE_DATA | BLOCK_HAVE_UNDO);
                    // Remove storage location.
                    pindexIter->nFile = 0;
                    pindexIter->nDataPos = 0;
                    pindexIter->nUndoPos = 0;
                    // Remove various other things
                    pindexIter->nTx = 0;
                    pindexIter->nChainTx = 0;
                    pindexIter->nSequenceId = 0;
                    // Make sure it gets written.
                    setDirtyBlockIndex.insert(pindexIter);
                    // Update indexes
                    setBlockIndexCandidates.erase(pindexIter);
                    std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> ret = mapBlocksUnlinked.equal_range(pindexIter->pprev);
                    while (ret.first != ret.second) {
                        if (ret.first->second == pindexIter) {
                            mapBlocksUnlinked.erase(ret.first++);
                        } else {
                            ++ret.first;
                        }
                    }
                } else if (pindexIter->IsValid(BLOCK_VALID_TRANSACTIONS) && pindexIter->nChainTx) {
                    setBlockIndexCandidates.insert(pindexIter);
                }
            }

            PruneBlockIndexCandidates();

            CheckBlockIndex();

            if (!FlushStateToDisk(state, FLUSH_STATE_ALWAYS)) {
                return false;
            }

            return true;
        }

        void UnloadBlockIndex()
        {
            mapBlockIndex.clear();
            setBlockIndexCandidates.clear();
            chainActive.SetTip(NULL);
            pindexBestInvalid = NULL;
        }

        bool LoadBlockIndex(string & strError)
        {
            // Load block index from databases
            if (!fReindex && !LoadBlockIndexDB(strError))
                return false;
            return true;
        }


        bool InitBlockIndex()
        {
            LOCK(cs_main);
            // Check whether we're already initialized
            if (chainActive.Genesis() != NULL)
                return true;

            // Use the provided setting for -txindex in the new database
            fTxIndex = GetBoolArg("-txindex", true);
            pblocktree->WriteFlag("txindex", fTxIndex);
            fAddrIndex = GetBoolArg("-addrindex", true);
            pblocktree->WriteFlag("addrindex", fAddrIndex);
            LogPrintf("Initializing databases...\n");

            // Only add the genesis block if not reindexing (in which case we reuse the one already on disk)
            if (!fReindex) {
                try {
                    CBlock& block = const_cast<CBlock&>(Params().GenesisBlock());
                    // Start new block file
                    unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
                    CDiskBlockPos blockPos;
                    CValidationState state;
                    if (!FindBlockPos(state, blockPos, nBlockSize + 8, 0, block.GetBlockTime()))
                        return error("LoadBlockIndex() : FindBlockPos failed");
                    if (!WriteBlockToDisk(block, blockPos))
                        return error("LoadBlockIndex() : writing genesis block to disk failed");
                    CBlockIndex* pindex = AddToBlockIndex(block);
                    if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
                        return error("LoadBlockIndex() : genesis block not accepted");
                    if (!ActivateBestChain(state, &block))
                        return error("LoadBlockIndex() : genesis block cannot be activated");
                    // Force a chainstate write so that when we VerifyDB in a moment, it doesnt check stale data
                    return FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
                } catch (std::runtime_error& e) {
                    return error("LoadBlockIndex() : failed to initialize block database: %s", e.what());
                }
            }

            return true;
        }


        bool LoadExternalBlockFile(FILE * fileIn, CDiskBlockPos * dbp)
        {
            // Map of disk positions for blocks with unknown parent (only used for reindex)
            static std::multimap<uint256, CDiskBlockPos> mapBlocksUnknownParent;
            int64_t nStart = GetTimeMillis();

            int nLoaded = 0;
            try {
                // This takes over fileIn and calls fclose() on it in the CBufferedFile destructor
                CBufferedFile blkdat(fileIn, 2 * MAX_BLOCK_SIZE_CURRENT, MAX_BLOCK_SIZE_CURRENT + 8, SER_DISK, CLIENT_VERSION);
                uint64_t nRewind = blkdat.GetPos();
                while (!blkdat.eof()) {
                    boost::this_thread::interruption_point();

                    blkdat.SetPos(nRewind);
                    nRewind++;         // start one byte further next time, in case of failure
                    blkdat.SetLimit(); // remove former limit
                    unsigned int nSize = 0;
                    try {
                        // locate a header
                        unsigned char buf[MESSAGE_START_SIZE];
                        blkdat.FindByte(Params().MessageStart()[0]);
                        nRewind = blkdat.GetPos() + 1;
                        blkdat >> FLATDATA(buf);
                        if (memcmp(buf, Params().MessageStart(), MESSAGE_START_SIZE))
                            continue;
                        // read size
                        blkdat >> nSize;
                        if (nSize < 80 || nSize > MAX_BLOCK_SIZE_CURRENT)
                            continue;
                    } catch (const std::exception&) {
                        // no valid block header found; don't complain
                        break;
                    }
                    try {
                        // read block
                        uint64_t nBlockPos = blkdat.GetPos();
                        if (dbp)
                            dbp->nPos = nBlockPos;
                        blkdat.SetLimit(nBlockPos + nSize);
                        blkdat.SetPos(nBlockPos);
                        CBlock block;
                        blkdat >> block;
                        nRewind = blkdat.GetPos();

                        // detect out of order blocks, and store them for later
                        uint256 hash = block.GetHash();
                        if (hash != Params().HashGenesisBlock() && mapBlockIndex.find(block.hashPrevBlock) == mapBlockIndex.end()) {
                            LogPrint("reindex", "%s: Out of order block %s, parent %s not known\n", __func__, hash.ToString(),
                                block.hashPrevBlock.ToString());
                            if (dbp)
                                mapBlocksUnknownParent.insert(std::make_pair(block.hashPrevBlock, *dbp));
                            continue;
                        }

                        // process in case the block isn't known yet
                        if (mapBlockIndex.count(hash) == 0 || (mapBlockIndex[hash]->nStatus & BLOCK_HAVE_DATA) == 0) {
                            CValidationState state;
                            if (ProcessNewBlock(state, NULL, &block, dbp))
                                nLoaded++;
                            if (state.IsError())
                                break;
                        } else if (hash != Params().HashGenesisBlock() && mapBlockIndex[hash]->nHeight % 1000 == 0) {
                            LogPrintf("Block Import: already had block %s at height %d\n", hash.ToString(), mapBlockIndex[hash]->nHeight);
                        }

                        // Recursively process earlier encountered successors of this block
                        deque<uint256> queue;
                        queue.push_back(hash);
                        while (!queue.empty()) {
                            uint256 head = queue.front();
                            queue.pop_front();
                            std::pair<std::multimap<uint256, CDiskBlockPos>::iterator, std::multimap<uint256, CDiskBlockPos>::iterator> range = mapBlocksUnknownParent.equal_range(head);
                            while (range.first != range.second) {
                                std::multimap<uint256, CDiskBlockPos>::iterator it = range.first;
                                if (ReadBlockFromDisk(block, it->second)) {
                                    LogPrintf("%s: Processing out of order child %s of %s\n", __func__, block.GetHash().ToString(),
                                        head.ToString());
                                    CValidationState dummy;
                                    if (ProcessNewBlock(dummy, NULL, &block, &it->second)) {
                                        nLoaded++;
                                        queue.push_back(block.GetHash());
                                    }
                                }
                                range.first++;
                                mapBlocksUnknownParent.erase(it);
                            }
                        }
                    } catch (std::exception& e) {
                        LogPrintf("%s : Deserialize or I/O error - %s", __func__, e.what());
                    }
                }
            } catch (std::runtime_error& e) {
                AbortNode(std::string("System error: ") + e.what());
            }
            if (nLoaded > 0)
                LogPrintf("Loaded %i blocks from external file in %dms\n", nLoaded, GetTimeMillis() - nStart);
            return nLoaded > 0;
        }

        void static CheckBlockIndex()
        {
            if (!fCheckBlockIndex) {
                return;
            }

            LOCK(cs_main);

            // During a reindex, we read the genesis block and call CheckBlockIndex before ActivateBestChain,
            // so we have the genesis block in mapBlockIndex but no active chain.  (A few of the tests when
            // iterating the block tree require that chainActive has been initialized.)
            if (chainActive.Height() < 0) {
                assert(mapBlockIndex.size() <= 1);
                return;
            }

            // Build forward-pointing map of the entire block tree.
            std::multimap<CBlockIndex*, CBlockIndex*> forward;
            for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); it++) {
                forward.insert(std::make_pair(it->second->pprev, it->second));
            }

            assert(forward.size() == mapBlockIndex.size());

            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangeGenesis = forward.equal_range(NULL);
            CBlockIndex* pindex = rangeGenesis.first->second;
            rangeGenesis.first++;
            assert(rangeGenesis.first == rangeGenesis.second); // There is only one index entry with parent NULL.

            // Iterate over the entire block tree, using depth-first search.
            // Along the way, remember whether there are blocks on the path from genesis
            // block being explored which are the first to have certain properties.
            size_t nNodes = 0;
            int nHeight = 0;
            CBlockIndex* pindexFirstInvalid = NULL;         // Oldest ancestor of pindex which is invalid.
            CBlockIndex* pindexFirstMissing = NULL;         // Oldest ancestor of pindex which does not have BLOCK_HAVE_DATA.
            CBlockIndex* pindexFirstNotTreeValid = NULL;    // Oldest ancestor of pindex which does not have BLOCK_VALID_TREE (regardless of being valid or not).
            CBlockIndex* pindexFirstNotChainValid = NULL;   // Oldest ancestor of pindex which does not have BLOCK_VALID_CHAIN (regardless of being valid or not).
            CBlockIndex* pindexFirstNotScriptsValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_SCRIPTS (regardless of being valid or not).
            while (pindex != NULL) {
                nNodes++;
                if (pindexFirstInvalid == NULL && pindex->nStatus & BLOCK_FAILED_VALID) pindexFirstInvalid = pindex;
                if (pindexFirstMissing == NULL && !(pindex->nStatus & BLOCK_HAVE_DATA)) pindexFirstMissing = pindex;
                if (pindex->pprev != NULL && pindexFirstNotTreeValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_TREE) pindexFirstNotTreeValid = pindex;
                if (pindex->pprev != NULL && pindexFirstNotChainValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_CHAIN) pindexFirstNotChainValid = pindex;
                if (pindex->pprev != NULL && pindexFirstNotScriptsValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_SCRIPTS) pindexFirstNotScriptsValid = pindex;

                // Begin: actual consistency checks.
                if (pindex->pprev == NULL) {
                    // Genesis block checks.
                    assert(pindex->GetBlockHash() == Params().HashGenesisBlock()); // Genesis block's hash must match.
                    assert(pindex == chainActive.Genesis());                       // The current active chain's genesis block must be this block.
                }
                // HAVE_DATA is equivalent to VALID_TRANSACTIONS and equivalent to nTx > 0 (we stored the number of transactions in the block)
                assert(!(pindex->nStatus & BLOCK_HAVE_DATA) == (pindex->nTx == 0));
                assert(((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TRANSACTIONS) == (pindex->nTx > 0));
                if (pindex->nChainTx == 0) assert(pindex->nSequenceId == 0); // nSequenceId can't be set for blocks that aren't linked
                // All parents having data is equivalent to all parents being VALID_TRANSACTIONS, which is equivalent to nChainTx being set.
                assert((pindexFirstMissing != NULL) == (pindex->nChainTx == 0));                                             // nChainTx == 0 is used to signal that all parent block's transaction data is available.
                assert(pindex->nHeight == nHeight);                                                                          // nHeight must be consistent.
                assert(pindex->pprev == NULL || pindex->nChainWork >= pindex->pprev->nChainWork);                            // For every block except the genesis block, the chainwork must be larger than the parent's.
                assert(nHeight < 2 || (pindex->pskip && (pindex->pskip->nHeight < nHeight)));                                // The pskip pointer must point back for all but the first 2 blocks.
                assert(pindexFirstNotTreeValid == NULL);                                                                     // All mapBlockIndex entries must at least be TREE valid
                if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TREE) assert(pindexFirstNotTreeValid == NULL);       // TREE valid implies all parents are TREE valid
                if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_CHAIN) assert(pindexFirstNotChainValid == NULL);     // CHAIN valid implies all parents are CHAIN valid
                if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_SCRIPTS) assert(pindexFirstNotScriptsValid == NULL); // SCRIPTS valid implies all parents are SCRIPTS valid
                if (pindexFirstInvalid == NULL) {
                    // Checks for not-invalid blocks.
                    assert((pindex->nStatus & BLOCK_FAILED_MASK) == 0); // The failed mask cannot be set for blocks without invalid parents.
                }
                if (!CBlockIndexWorkComparator()(pindex, chainActive.Tip()) && pindexFirstMissing == NULL) {
                    if (pindexFirstInvalid == NULL) { // If this block sorts at least as good as the current tip and is valid, it must be in setBlockIndexCandidates.
                        assert(setBlockIndexCandidates.count(pindex));
                    }
                } else { // If this block sorts worse than the current tip, it cannot be in setBlockIndexCandidates.
                    assert(setBlockIndexCandidates.count(pindex) == 0);
                }
                // Check whether this block is in mapBlocksUnlinked.
                std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangeUnlinked = mapBlocksUnlinked.equal_range(pindex->pprev);
                bool foundInUnlinked = false;
                while (rangeUnlinked.first != rangeUnlinked.second) {
                    assert(rangeUnlinked.first->first == pindex->pprev);
                    if (rangeUnlinked.first->second == pindex) {
                        foundInUnlinked = true;
                        break;
                    }
                    rangeUnlinked.first++;
                }
                if (pindex->pprev && pindex->nStatus & BLOCK_HAVE_DATA && pindexFirstMissing != NULL) {
                    if (pindexFirstInvalid == NULL) { // If this block has block data available, some parent doesn't, and has no invalid parents, it must be in mapBlocksUnlinked.
                        assert(foundInUnlinked);
                    }
                } else { // If this block does not have block data available, or all parents do, it cannot be in mapBlocksUnlinked.
                    assert(!foundInUnlinked);
                }
                // assert(pindex->GetBlockHash() == pindex->GetBlockHeader().GetHash()); // Perhaps too slow
                // End: actual consistency checks.

                // Try descending into the first subnode.
                std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = forward.equal_range(pindex);
                if (range.first != range.second) {
                    // A subnode was found.
                    pindex = range.first->second;
                    nHeight++;
                    continue;
                }
                // This is a leaf node.
                // Move upwards until we reach a node of which we have not yet visited the last child.
                while (pindex) {
                    // We are going to either move to a parent or a sibling of pindex.
                    // If pindex was the first with a certain property, unset the corresponding variable.
                    if (pindex == pindexFirstInvalid) pindexFirstInvalid = NULL;
                    if (pindex == pindexFirstMissing) pindexFirstMissing = NULL;
                    if (pindex == pindexFirstNotTreeValid) pindexFirstNotTreeValid = NULL;
                    if (pindex == pindexFirstNotChainValid) pindexFirstNotChainValid = NULL;
                    if (pindex == pindexFirstNotScriptsValid) pindexFirstNotScriptsValid = NULL;
                    // Find our parent.
                    CBlockIndex* pindexPar = pindex->pprev;
                    // Find which child we just visited.
                    std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangePar = forward.equal_range(pindexPar);
                    while (rangePar.first->second != pindex) {
                        assert(rangePar.first != rangePar.second); // Our parent must have at least the node we're coming from as child.
                        rangePar.first++;
                    }
                    // Proceed to the next one.
                    rangePar.first++;
                    if (rangePar.first != rangePar.second) {
                        // Move to the sibling.
                        pindex = rangePar.first->second;
                        break;
                    } else {
                        // Move up further.
                        pindex = pindexPar;
                        nHeight--;
                        continue;
                    }
                }
            }

            // Check that we actually traversed the entire map.
            assert(nNodes == forward.size());
        }

        //////////////////////////////////////////////////////////////////////////////
        //
        // CAlert
        //

        string GetWarnings(string strFor)
        {
            int nPriority = 0;
            string strStatusBar;
            string strRPC;

            if (!CLIENT_VERSION_IS_RELEASE)
                strStatusBar = _("This is a pre-release test build - use at your own risk - do not use for staking or merchant applications!");

            if (GetBoolArg("-testsafemode", false))
                strStatusBar = strRPC = "testsafemode enabled";

            // Misc warnings like out of disk space and clock is wrong
            if (strMiscWarning != "") {
                nPriority = 1000;
                strStatusBar = strMiscWarning;
            }

            if (fLargeWorkForkFound) {
                nPriority = 2000;
                strStatusBar = strRPC = _("Warning: The network does not appear to fully agree! Some miners appear to be experiencing issues.");
            } else if (fLargeWorkInvalidChainFound) {
                nPriority = 2000;
                strStatusBar = strRPC = _("Warning: We do not appear to fully agree with our peers! You may need to upgrade, or other nodes may need to upgrade.");
            }

            // Alerts
            {
                LOCK(cs_mapAlerts);
                BOOST_FOREACH (PAIRTYPE(const uint256, CAlert) & item, mapAlerts) {
                    const CAlert& alert = item.second;
                    if (alert.AppliesToMe() && alert.nPriority > nPriority) {
                        nPriority = alert.nPriority;
                        strStatusBar = alert.strStatusBar;
                    }
                }
            }

            if (strFor == "statusbar")
                return strStatusBar;
            else if (strFor == "rpc")
                return strRPC;
            assert(!"GetWarnings() : invalid parameter");
            return "error";
        }


        //////////////////////////////////////////////////////////////////////////////
        //
        // Messages
        //


        bool static AlreadyHave(const CInv& inv)
        {
            switch (inv.type) {
            case MSG_WITNESS_TX:
            case MSG_TX: {
                bool txInMap = false;
                txInMap = mempool.exists(inv.hash);
                return txInMap || mapOrphanTransactions.count(inv.hash) ||
                       pcoinsTip->HaveCoins(inv.hash);
            }
            case MSG_BLOCK:
            case MSG_WITNESS_BLOCK:
                return mapBlockIndex.count(inv.hash);
            case MSG_TXLOCK_REQUEST:
                return mapTxLockReq.count(inv.hash) ||
                       mapTxLockReqRejected.count(inv.hash);
            case MSG_TXLOCK_VOTE:
                return mapTxLockVote.count(inv.hash);
            case MSG_SPORK:
                return mapSporks.count(inv.hash);
            case MSG_MASTERNODE_WINNER:
                if (masternodePayments.mapMasternodePayeeVotes.count(inv.hash)) {
                    masternodeSync.AddedMasternodeWinner(inv.hash);
                    return true;
                }
                return false;
            case MSG_BUDGET_VOTE:
                if (budget.mapSeenMasternodeBudgetVotes.count(inv.hash)) {
                    masternodeSync.AddedBudgetItem(inv.hash);
                    return true;
                }
                return false;
            case MSG_BUDGET_PROPOSAL:
                if (budget.mapSeenMasternodeBudgetProposals.count(inv.hash)) {
                    masternodeSync.AddedBudgetItem(inv.hash);
                    return true;
                }
                return false;
            case MSG_BUDGET_FINALIZED_VOTE:
                if (budget.mapSeenFinalizedBudgetVotes.count(inv.hash)) {
                    masternodeSync.AddedBudgetItem(inv.hash);
                    return true;
                }
                return false;
            case MSG_BUDGET_FINALIZED:
                if (budget.mapSeenFinalizedBudgets.count(inv.hash)) {
                    masternodeSync.AddedBudgetItem(inv.hash);
                    return true;
                }
                return false;
            case MSG_MASTERNODE_ANNOUNCE:
                if (mnodeman.mapSeenMasternodeBroadcast.count(inv.hash)) {
                    masternodeSync.AddedMasternodeList(inv.hash);
                    return true;
                }
                return false;
            case MSG_MASTERNODE_PING:
                return mnodeman.mapSeenMasternodePing.count(inv.hash);
            }
            // Don't know what it is, just say we already got one
            return true;
        }


        void static ProcessGetData(CNode * pfrom)
        {
            std::deque<CInv>::iterator it = pfrom->vRecvGetData.begin();

            vector<CInv> vNotFound;

            LOCK(cs_main);

            while (it != pfrom->vRecvGetData.end()) {
                // Don't bother if send buffer is too full to respond anyway
                if (pfrom->nSendSize >= SendBufferSize())
                    break;

                const CInv& inv = *it;
                {
                    boost::this_thread::interruption_point();
                    it++;

                    if (inv.type == MSG_BLOCK || inv.type == MSG_FILTERED_BLOCK || inv.type == MSG_WITNESS_BLOCK) {
                        bool send = false;
                        BlockMap::iterator mi = mapBlockIndex.find(inv.hash);
                        if (mi != mapBlockIndex.end()) {
                            if (chainActive.Contains(mi->second)) {
                                send = true;
                            } else {
                                // To prevent fingerprinting attacks, only send blocks outside of the active
                                // chain if they are valid, and no more than a max reorg depth than the best header
                                // chain we know about.
                                send = mi->second->IsValid(BLOCK_VALID_SCRIPTS) && (pindexBestHeader != NULL) &&
                                       (chainActive.Height() - mi->second->nHeight < Params().MaxReorganizationDepth());
                                if (!send) {
                                    LogPrintf("ProcessGetData(): ignoring request from peer=%i for old block that isn't in the main chain\n", pfrom->GetId());
                                }
                            }
                        }
                        // Don't send not-validated blocks
                        if (send && (mi->second->nStatus & BLOCK_HAVE_DATA)) {
                            // Send block from disk
                            CBlock block;
                            if (!ReadBlockFromDisk(block, (*mi).second))
                                assert(!"cannot load block from disk");
                            if (inv.type == MSG_BLOCK)
                                pfrom->PushMessageWithFlag(SERIALIZE_TRANSACTION_NO_WITNESS, NetMsgType::BLOCK, block);
                            else if (inv.type == MSG_WITNESS_BLOCK)
                                pfrom->PushMessage(NetMsgType::BLOCK, block);
                            else // MSG_FILTERED_BLOCK)
                            {
                                LOCK(pfrom->cs_filter);
                                if (pfrom->pfilter) {
                                    CMerkleBlock merkleBlock(block, *pfrom->pfilter);
                                    pfrom->PushMessage(NetMsgType::MERKLEBLOCK, merkleBlock);
                                    // CMerkleBlock just contains hashes, so also push any transactions in the block the client did not see
                                    // This avoids hurting performance by pointlessly requiring a round-trip
                                    // Note that there is currently no way for a node to request any single transactions we didnt send here -
                                    // they must either disconnect and retry or request the full block.
                                    // Thus, the protocol spec specified allows for us to provide duplicate txn here,
                                    // however we MUST always provide at least what the remote peer needs
                                    typedef std::pair<unsigned int, uint256> PairType;
                                    BOOST_FOREACH (PairType& pair, merkleBlock.vMatchedTxn)
                                        if (!pfrom->setInventoryKnown.count(CInv(MSG_TX, pair.second)))
                                            pfrom->PushMessageWithFlag(SERIALIZE_TRANSACTION_NO_WITNESS, NetMsgType::TX, block.vtx[pair.first]);
                                }
                                // else
                                // no response
                            }

                            // Trigger them to send a getblocks request for the next batch of inventory
                            if (inv.hash == pfrom->hashContinue) {
                                // Bypass PushInventory, this must send even if redundant,
                                // and we want it right after the last block so they don't
                                // wait for other stuff first.
                                vector<CInv> vInv;
                                vInv.push_back(CInv(MSG_BLOCK, chainActive.Tip()->GetBlockHash()));
                                pfrom->PushMessage(NetMsgType::INV, vInv);
                                pfrom->hashContinue = 0;
                            }
                        }
                    } else if (inv.IsKnownType()) {
                        // Send stream from relay memory
                        bool pushed = false;
                        {
                            LOCK(cs_mapRelay);
                            map<CInv, CDataStream>::iterator mi = mapRelay.find(inv);
                            if (mi != mapRelay.end()) {
                                pfrom->PushMessageWithFlag(inv.type == MSG_WITNESS_TX ? 0 : SERIALIZE_TRANSACTION_NO_WITNESS, inv.GetCommand(), (*mi).second);
                                pushed = true;
                            }
                        }

                        if (!pushed && (inv.type == MSG_TX || inv.type == MSG_WITNESS_TX)) {
                            CTransaction tx;
                            if (mempool.lookup(inv.hash, tx)) {
                                pfrom->PushMessageWithFlag(inv.type == MSG_WITNESS_TX ? 0 : SERIALIZE_TRANSACTION_NO_WITNESS, NetMsgType::TX, tx);
                                pushed = true;
                            }
                        }
                        if (!pushed && inv.type == MSG_TXLOCK_VOTE) {
                            if (mapTxLockVote.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mapTxLockVote[inv.hash];
                                pfrom->PushMessage(NetMsgType::TXLVOTE, ss);
                                pushed = true;
                            }
                        }
                        if (!pushed && inv.type == MSG_TXLOCK_REQUEST) {
                            if (mapTxLockReq.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mapTxLockReq[inv.hash];
                                pfrom->PushMessage(NetMsgType::IX, ss);
                                pushed = true;
                            }
                        }
                        if (!pushed && inv.type == MSG_SPORK) {
                            if (mapSporks.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mapSporks[inv.hash];
                                pfrom->PushMessage(NetMsgType::SPORK, ss);
                                pushed = true;
                            }
                        }
                        if (!pushed && inv.type == MSG_MASTERNODE_WINNER) {
                            if (masternodePayments.mapMasternodePayeeVotes.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << masternodePayments.mapMasternodePayeeVotes[inv.hash];
                                pfrom->PushMessage(NetMsgType::MNW, ss);
                                pushed = true;
                            }
                        }
                        if (!pushed && inv.type == MSG_BUDGET_VOTE) {
                            if (budget.mapSeenMasternodeBudgetVotes.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << budget.mapSeenMasternodeBudgetVotes[inv.hash];
                                pfrom->PushMessage(NetMsgType::MVOTE, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_BUDGET_PROPOSAL) {
                            if (budget.mapSeenMasternodeBudgetProposals.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << budget.mapSeenMasternodeBudgetProposals[inv.hash];
                                pfrom->PushMessage(NetMsgType::MPROP, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_BUDGET_FINALIZED_VOTE) {
                            if (budget.mapSeenFinalizedBudgetVotes.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << budget.mapSeenFinalizedBudgetVotes[inv.hash];
                                pfrom->PushMessage(NetMsgType::FBVOTE, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_BUDGET_FINALIZED) {
                            if (budget.mapSeenFinalizedBudgets.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << budget.mapSeenFinalizedBudgets[inv.hash];
                                pfrom->PushMessage(NetMsgType::FBS, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_MASTERNODE_ANNOUNCE) {
                            if (mnodeman.mapSeenMasternodeBroadcast.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mnodeman.mapSeenMasternodeBroadcast[inv.hash];
                                pfrom->PushMessage(NetMsgType::MNB, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_MASTERNODE_PING) {
                            if (mnodeman.mapSeenMasternodePing.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mnodeman.mapSeenMasternodePing[inv.hash];
                                pfrom->PushMessage(NetMsgType::MNP, ss);
                                pushed = true;
                            }
                        }

                        if (!pushed && inv.type == MSG_DSTX) {
                            if (mapObfuscationBroadcastTxes.count(inv.hash)) {
                                CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                                ss.reserve(1000);
                                ss << mapObfuscationBroadcastTxes[inv.hash].tx << mapObfuscationBroadcastTxes[inv.hash].vin << mapObfuscationBroadcastTxes[inv.hash].vchSig << mapObfuscationBroadcastTxes[inv.hash].sigTime;

                                pfrom->PushMessage(NetMsgType::DSTX, ss);
                                pushed = true;
                            }
                        }


                        if (!pushed) {
                            vNotFound.push_back(inv);
                        }
                    }

                    // Track requests for our stuff.
                    GetMainSignals().Inventory(inv.hash);

                    if (inv.type == MSG_BLOCK || inv.type == MSG_FILTERED_BLOCK || inv.type == MSG_WITNESS_BLOCK)
                        break;
                }
            }

            pfrom->vRecvGetData.erase(pfrom->vRecvGetData.begin(), it);

            if (!vNotFound.empty()) {
                // Let the peer know that we didn't find what it asked for, so it doesn't
                // have to wait around forever. Currently only SPV clients actually care
                // about this message: it's needed when they are recursively walking the
                // dependencies of relevant unconfirmed transactions. SPV clients want to
                // do that because they want to know about (and store and rebroadcast and
                // risk analyze) the dependencies of transactions relevant to them, without
                // having to download the entire memory pool.
                pfrom->PushMessage(NetMsgType::NOTFOUND, vNotFound);
            }
        }

        bool fRequestedSporksIDB = false;
        bool static ProcessMessage(CNode * pfrom, string strCommand, CDataStream & vRecv, int64_t nTimeReceived)
        {
            if (fDebug)
                LogPrintf("received: %s (%u bytes) peer=%d\n", SanitizeString(strCommand), vRecv.size(), pfrom->id);
            if (mapArgs.count("-dropmessagestest") && GetRand(atoi(mapArgs["-dropmessagestest"])) == 0) {
                LogPrintf("dropmessagestest DROPPING RECV MESSAGE\n");
                return true;
            }

            if (strCommand == NetMsgType::VERSION) {
                // Each connection can only send one version message
                if (pfrom->nVersion != 0) {
                    pfrom->PushMessage(NetMsgType::REJECT, strCommand, REJECT_DUPLICATE, string("Duplicate version message"));
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 1);
                    return false;
                }

                int64_t nTime;
                CAddress addrMe;
                CAddress addrFrom;
                uint64_t nNonce = 1;
                vRecv >> pfrom->nVersion >> pfrom->nServices >> nTime >> addrMe;
                if (!pfrom->fInbound) {
                    addrman.SetServices(pfrom->addr, pfrom->nServices);
                }
                if (pfrom->nServicesExpected & ~pfrom->nServices) {
                    LogPrint("net", "peer=%d does not offer the expected services (%08x offered, %08x expected); disconnecting\n", pfrom->id, pfrom->nServices, pfrom->nServicesExpected);
                    pfrom->PushMessage(NetMsgType::REJECT, strCommand, REJECT_NONSTANDARD,
                        strprintf("Expected to offer services %08x", pfrom->nServicesExpected));
                    pfrom->fDisconnect = true;
                }

                if (pfrom->DisconnectOldProtocol(ActiveProtocol(), strCommand))
                    return false;

                if (!vRecv.empty())
                    vRecv >> addrFrom >> nNonce;
                if (!vRecv.empty()) {
                    vRecv >> LIMITED_STRING(pfrom->strSubVer, 256);
                    pfrom->cleanSubVer = SanitizeString(pfrom->strSubVer);
                }
                // broken releases with wrong blockchain data
                if (pfrom->cleanSubVer == "/Altbet Core:1.1.0/" ||
                    pfrom->cleanSubVer == "/Altbet Core:1.3.0/") {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 100); // instantly ban them because they have bad block data
                    return false;
                }
                if (!vRecv.empty())
                    vRecv >> pfrom->nStartingHeight;
                if (!vRecv.empty())
                    vRecv >> pfrom->fRelayTxes; // set to true after we get the first filter* message
                else
                    pfrom->fRelayTxes = true;

                // Disconnect if we connected to ourself
                if (nNonce == nLocalHostNonce && nNonce > 1) {
                    LogPrintf("connected to self at %s, disconnecting\n", pfrom->addr.ToString());
                    pfrom->fDisconnect = true;
                    return true;
                }

                pfrom->addrLocal = addrMe;
                if (pfrom->fInbound && addrMe.IsRoutable()) {
                    SeenLocal(addrMe);
                }

                // Send version eagerly
                if (pfrom->fInbound)
                    pfrom->PushVersion();

                pfrom->fClient = !(pfrom->nServices & NODE_NETWORK);

                if ((pfrom->nServices & NODE_WITNESS)) {
                    LOCK(cs_main);
                    State(pfrom->GetId())->fHaveWitness = true;
                }

                // Potentially mark this peer as a preferred download peer.
                UpdatePreferredDownload(pfrom, State(pfrom->GetId()));

                // Change version
                pfrom->PushMessage(NetMsgType::VERACK);
                pfrom->ssSend.SetVersion(min(pfrom->nVersion, PROTOCOL_VERSION));

                // Altbet: We use certain sporks during IBD, so check to see if they are
                // available. If not, ask the first peer connected for them.
                bool fMissingSporks = !pSporkDB->SporkExists(SPORK_23_ZEROCOIN_MAINTENANCE_MODE);

                if (fMissingSporks || !fRequestedSporksIDB) {
                    LogPrintf("asking peer for sporks\n");
                    pfrom->PushMessage(NetMsgType::GETSPORKS);
                    fRequestedSporksIDB = true;
                }

                if (!pfrom->fInbound) {
                    // Advertise our address
                    if (fListen && !IsInitialBlockDownload()) {
                        CAddress addr = GetLocalAddress(&pfrom->addr);
                        if (addr.IsRoutable()) {
                            LogPrintf("ProcessMessages: advertizing address %s\n", addr.ToString());
                            pfrom->PushAddress(addr);
                        } else if (IsPeerAddrLocalGood(pfrom)) {
                            addr.SetIP(pfrom->addrLocal);
                            LogPrintf("ProcessMessages: advertizing address %s\n", addr.ToString());
                            pfrom->PushAddress(addr);
                        }
                    }

                    // Get recent addresses
                    if (pfrom->fOneShot || pfrom->nVersion >= CADDR_TIME_VERSION || addrman.size() < 1000) {
                        pfrom->PushMessage(NetMsgType::GETADDR);
                        pfrom->fGetAddr = true;
                    }
                    addrman.Good(pfrom->addr);
                } else {
                    if (((CNetAddr)pfrom->addr) == (CNetAddr)addrFrom) {
                        addrman.Add(addrFrom, addrFrom);
                        addrman.Good(addrFrom);
                    }
                }

                // Relay alerts
                {
                    LOCK(cs_mapAlerts);
                    BOOST_FOREACH (PAIRTYPE(const uint256, CAlert) & item, mapAlerts)
                        item.second.RelayTo(pfrom);
                }

                pfrom->fSuccessfullyConnected = true;

                string remoteAddr;
                if (fLogIPs)
                    remoteAddr = ", peeraddr=" + pfrom->addr.ToString();

                LogPrintf("receive version message: %s: version %d, blocks=%d, us=%s, peer=%d%s\n",
                    pfrom->cleanSubVer, pfrom->nVersion,
                    pfrom->nStartingHeight, addrMe.ToString(), pfrom->id,
                    remoteAddr);

                int64_t nTimeOffset = nTime - GetTime();
                pfrom->nTimeOffset = nTimeOffset;
                AddTimeData(pfrom->addr, nTimeOffset);
            }


            else if (pfrom->nVersion == 0) {
                // Must have a version message before anything else
                LOCK(cs_main);
                Misbehaving(pfrom->GetId(), 1);
                return false;
            }


            else if (strCommand == NetMsgType::VERACK) {
                pfrom->SetRecvVersion(min(pfrom->nVersion, PROTOCOL_VERSION));

                // Mark this node as currently connected, so we update its timestamp later.
                if (pfrom->fNetworkNode) {
                    LOCK(cs_main);
                    State(pfrom->GetId())->fCurrentlyConnected = true;
                }
            }


            else if (strCommand == NetMsgType::ADDR) {
                vector<CAddress> vAddr;
                vRecv >> vAddr;

                // Don't want addr from older versions unless seeding
                if (pfrom->nVersion < CADDR_TIME_VERSION && addrman.size() > 1000)
                    return true;
                if (vAddr.size() > 1000) {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 20);
                    return error("message addr size() = %u", vAddr.size());
                }

                // Store the new addresses
                vector<CAddress> vAddrOk;
                int64_t nNow = GetAdjustedTime();
                int64_t nSince = nNow - 10 * 60;
                BOOST_FOREACH (CAddress& addr, vAddr) {
                    boost::this_thread::interruption_point();

                    if (!(addr.nServices & NODE_NETWORK))
                        continue;

                    if (addr.nTime <= 100000000 || addr.nTime > nNow + 10 * 60)
                        addr.nTime = nNow - 5 * 24 * 60 * 60;
                    pfrom->AddAddressKnown(addr);
                    bool fReachable = IsReachable(addr);
                    if (addr.nTime > nSince && !pfrom->fGetAddr && vAddr.size() <= 10 && addr.IsRoutable()) {
                        // Relay to a limited number of other nodes
                        {
                            LOCK(cs_vNodes);
                            // Use deterministic randomness to send to the same nodes for 24 hours
                            // at a time so the setAddrKnowns of the chosen nodes prevent repeats
                            static uint256 hashSalt;
                            if (hashSalt == 0)
                                hashSalt = GetRandHash();
                            uint64_t hashAddr = addr.GetHash();
                            uint256 hashRand = hashSalt ^ (hashAddr << 32) ^ ((GetTime() + hashAddr) / (24 * 60 * 60));
                            hashRand = Hash(BEGIN(hashRand), END(hashRand));
                            multimap<uint256, CNode*> mapMix;
                            BOOST_FOREACH (CNode* pnode, vNodes) {
                                if (pnode->nVersion < CADDR_TIME_VERSION)
                                    continue;
                                unsigned int nPointer;
                                memcpy(&nPointer, &pnode, sizeof(nPointer));
                                uint256 hashKey = hashRand ^ nPointer;
                                hashKey = Hash(BEGIN(hashKey), END(hashKey));
                                mapMix.insert(make_pair(hashKey, pnode));
                            }
                            int nRelayNodes = fReachable ? 2 : 1; // limited relaying of addresses outside our network(s)
                            for (multimap<uint256, CNode*>::iterator mi = mapMix.begin(); mi != mapMix.end() && nRelayNodes-- > 0; ++mi)
                                ((*mi).second)->PushAddress(addr);
                        }
                    }
                    // Do not store addresses outside our network
                    if (fReachable)
                        vAddrOk.push_back(addr);
                }
                addrman.Add(vAddrOk, pfrom->addr, 2 * 60 * 60);
                if (vAddr.size() < 1000)
                    pfrom->fGetAddr = false;
                if (pfrom->fOneShot)
                    pfrom->fDisconnect = true;
            }


            else if (strCommand == NetMsgType::INV) {
                vector<CInv> vInv;
                vRecv >> vInv;
                if (vInv.size() > MAX_INV_SZ) {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 20);
                    return error("message inv size() = %u", vInv.size());
                }

                LOCK(cs_main);

                std::vector<CInv> vToFetch;

                for (unsigned int nInv = 0; nInv < vInv.size(); nInv++) {
                    CInv& inv = vInv[nInv];

                    boost::this_thread::interruption_point();
                    pfrom->AddInventoryKnown(inv);

                    bool fAlreadyHave = AlreadyHave(inv);
                    LogPrint("net", "got inv: %s  %s peer=%d\n", inv.ToString(), fAlreadyHave ? "have" : "new", pfrom->id);

                    if (!fAlreadyHave && !fImporting && !fReindex && inv.type != MSG_BLOCK)
                        pfrom->AskFor(inv);

                    if (inv.type == MSG_TX && State(pfrom->GetId())->fHaveWitness) {
                        inv.type = MSG_WITNESS_TX;
                    }

                    if (inv.type == MSG_BLOCK) {
                        UpdateBlockAvailability(pfrom->GetId(), inv.hash);
                        if (!fAlreadyHave && !fImporting && !fReindex && !mapBlocksInFlight.count(inv.hash)) {
                            // First request the headers preceding the announced block. In the normal fully-synced
                            // case where a new block is announced that succeeds the current tip (no reorganization),
                            // there are no such headers.
                            // Secondly, and only when we are close to being synced, we request the announced block directly,
                            // to avoid an extra round-trip. Note that we must *first* ask for the headers, so by the
                            // time the block arrives, the header chain leading up to it is already validated. Not
                            // doing this will result in the received block being rejected as an orphan in case it is
                            // not a direct successor.
                            if (State(pfrom->GetId())->fHaveWitness &&
                                (GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) > chainActive.Tip()->nTime || State(pfrom->GetId())->fHaveWitness)) {
                                inv.type = MSG_WITNESS_BLOCK;
                            }
                            vToFetch.push_back(inv);
                            LogPrint("net", "getblocks (%d) %s to peer=%d\n", pindexBestHeader->nHeight, inv.hash.ToString(), pfrom->id);
                        }
                    }

                    // Track requests for our stuff
                    GetMainSignals().Inventory(inv.hash);

                    if (pfrom->nSendSize > (SendBufferSize() * 2)) {
                        LOCK(cs_main);
                        return error("send buffer size() = %u", pfrom->nSendSize);
                    }
                }

                if (!vToFetch.empty())
                    pfrom->PushMessage(NetMsgType::GETDATA, vToFetch);
            }


            else if (strCommand == NetMsgType::GETDATA) {
                vector<CInv> vInv;
                vRecv >> vInv;
                if (vInv.size() > MAX_INV_SZ) {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 20);
                    return error("message getdata size() = %u", vInv.size());
                }

                if (fDebug || (vInv.size() != 1))
                    LogPrint("net", "received getdata (%u invsz) peer=%d\n", vInv.size(), pfrom->id);

                if ((fDebug && vInv.size() > 0) || (vInv.size() == 1))
                    LogPrint("net", "received getdata for: %s peer=%d\n", vInv[0].ToString(), pfrom->id);

                pfrom->vRecvGetData.insert(pfrom->vRecvGetData.end(), vInv.begin(), vInv.end());
                ProcessGetData(pfrom);
            }


            else if (strCommand == NetMsgType::GETBLOCKS || strCommand == NetMsgType::GETHEADERS) {
                CBlockLocator locator;
                uint256 hashStop;
                vRecv >> locator >> hashStop;

                LOCK(cs_main);

                // Find the last block the caller has in the main chain
                CBlockIndex* pindex = FindForkInGlobalIndex(chainActive, locator);

                // Send the rest of the chain
                if (pindex)
                    pindex = chainActive.Next(pindex);
                int nLimit = 500;
                LogPrint("net", "getblocks %d to %s limit %d from peer=%d\n", (pindex ? pindex->nHeight : -1), hashStop == uint256(0) ? "end" : hashStop.ToString(), nLimit, pfrom->id);
                for (; pindex; pindex = chainActive.Next(pindex)) {
                    if (pindex->GetBlockHash() == hashStop) {
                        LogPrint("net", "  getblocks stopping at %d %s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                        break;
                    }
                    pfrom->PushInventory(CInv(MSG_BLOCK, pindex->GetBlockHash()));
                    if (--nLimit <= 0) {
                        // When this block is requested, we'll send an inv that'll make them
                        // getblocks the next batch of inventory.
                        LogPrint("net", "  getblocks stopping at limit %d %s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                        pfrom->hashContinue = pindex->GetBlockHash();
                        break;
                    }
                }
            }


            else if (strCommand == NetMsgType::HEADERS && Params().HeadersFirstSyncingActive()) {
                CBlockLocator locator;
                uint256 hashStop;
                vRecv >> locator >> hashStop;

                LOCK(cs_main);

                if (IsInitialBlockDownload())
                    return true;

                CBlockIndex* pindex = NULL;
                if (locator.IsNull()) {
                    // If locator is null, return the hashStop block
                    BlockMap::iterator mi = mapBlockIndex.find(hashStop);
                    if (mi == mapBlockIndex.end())
                        return true;
                    pindex = (*mi).second;
                } else {
                    // Find the last block the caller has in the main chain
                    pindex = FindForkInGlobalIndex(chainActive, locator);
                    if (pindex)
                        pindex = chainActive.Next(pindex);
                }

                // we must use CBlocks, as CBlockHeaders won't include the 0x00 nTx count at the end
                vector<CBlock> vHeaders;
                int nLimit = MAX_HEADERS_RESULTS;
                if (fDebug)
                    LogPrintf("getheaders %d to %s from peer=%d\n", (pindex ? pindex->nHeight : -1), hashStop.ToString(), pfrom->id);
                for (; pindex; pindex = chainActive.Next(pindex)) {
                    vHeaders.push_back(pindex->GetBlockHeader());
                    if (--nLimit <= 0 || pindex->GetBlockHash() == hashStop)
                        break;
                }
                pfrom->PushMessage(NetMsgType::HEADERS, vHeaders);
            }


            else if (strCommand == NetMsgType::TX || strCommand == NetMsgType::DSTX) {
                vector<uint256> vWorkQueue;
                vector<uint256> vEraseQueue;
                CTransaction tx;

                //masternode signed transaction
                bool ignoreFees = false;
                CTxIn vin;
                vector<unsigned char> vchSig;
                int64_t sigTime;

                if (strCommand == NetMsgType::TX) {
                    vRecv >> tx;
                } else if (strCommand == NetMsgType::DSTX) {
                    //these allow masternodes to publish a limited amount of free transactions
                    vRecv >> tx >> vin >> vchSig >> sigTime;

                    CMasternode* pmn = mnodeman.Find(vin);
                    if (pmn != NULL) {
                        if (!pmn->allowFreeTx) {
                            //multiple peers can send us a valid masternode transaction
                            if (fDebug) LogPrintf("dstx: Masternode sending too many transactions %s\n", tx.GetHash().ToString());
                            return true;
                        }

                        std::string strMessage = tx.GetHash().ToString() + std::to_string(sigTime);

                        std::string errorMessage = "";
                        if (!obfuScationSigner.VerifyMessage(pmn->pubKeyMasternode, vchSig, strMessage, errorMessage)) {
                            LogPrintf("dstx: Got bad masternode address signature %s \n", vin.ToString());
                            //pfrom->Misbehaving(20);
                            return false;
                        }

                        LogPrintf("dstx: Got Masternode transaction %s\n", tx.GetHash().ToString());

                        ignoreFees = true;
                        pmn->allowFreeTx = false;

                        if (!mapObfuscationBroadcastTxes.count(tx.GetHash())) {
                            CObfuscationBroadcastTx dstx;
                            dstx.tx = tx;
                            dstx.vin = vin;
                            dstx.vchSig = vchSig;
                            dstx.sigTime = sigTime;

                            mapObfuscationBroadcastTxes.insert(make_pair(tx.GetHash(), dstx));
                        }
                    }
                }

                CInv inv(MSG_TX, tx.GetHash());
                pfrom->AddInventoryKnown(inv);

                LOCK(cs_main);

                bool fMissingInputs = false;
                bool fMissingZerocoinInputs = false;
                CValidationState state;

                mapAlreadyAskedFor.erase(inv);

                if (!tx.IsZerocoinSpend() && AcceptToMemoryPool(mempool, state, tx, true, &fMissingInputs, false, ignoreFees)) {
                    mempool.check(pcoinsTip);
                    RelayTransaction(tx);
                    vWorkQueue.push_back(inv.hash);

                    LogPrint("mempool", "AcceptToMemoryPool: peer=%d %s : accepted %s (poolsz %u)\n",
                        pfrom->id, pfrom->cleanSubVer,
                        tx.GetHash().ToString(),
                        mempool.mapTx.size());

                    uiInterface.NotifyTransaction(tx.GetHash());

                    // Recursively process any orphan transactions that depended on this one
                    set<NodeId> setMisbehaving;
                    for (unsigned int i = 0; i < vWorkQueue.size(); i++) {
                        map<uint256, set<uint256> >::iterator itByPrev = mapOrphanTransactionsByPrev.find(vWorkQueue[i]);
                        if (itByPrev == mapOrphanTransactionsByPrev.end())
                            continue;
                        for (set<uint256>::iterator mi = itByPrev->second.begin();
                             mi != itByPrev->second.end();
                             ++mi) {
                            const uint256& orphanHash = *mi;
                            const CTransaction& orphanTx = mapOrphanTransactions[orphanHash].tx;
                            NodeId fromPeer = mapOrphanTransactions[orphanHash].fromPeer;
                            bool fMissingInputs2 = false;
                            // Use a dummy CValidationState so someone can't setup nodes to counter-DoS based on orphan
                            // resolution (that is, feeding people an invalid transaction based on LegitTxX in order to get
                            // anyone relaying LegitTxX banned)
                            CValidationState stateDummy;


                            if (setMisbehaving.count(fromPeer))
                                continue;
                            if (AcceptToMemoryPool(mempool, stateDummy, orphanTx, true, &fMissingInputs2)) {
                                LogPrint("mempool", "   accepted orphan tx %s\n", orphanHash.ToString());
                                RelayTransaction(orphanTx);
                                vWorkQueue.push_back(orphanHash);
                                vEraseQueue.push_back(orphanHash);
                            } else if (!fMissingInputs2) {
                                int nDos = 0;
                                if (stateDummy.IsInvalid(nDos) && nDos > 0 && (!state.CorruptionPossible() || State(fromPeer)->fHaveWitness)) {
                                    // Punish peer that gave us an invalid orphan tx
                                    Misbehaving(fromPeer, nDos);
                                    setMisbehaving.insert(fromPeer);
                                    LogPrint("mempool", "   invalid orphan tx %s\n", orphanHash.ToString());
                                }
                                // Has inputs but not accepted to mempool
                                // Probably non-standard or insufficient fee/priority
                                LogPrint("mempool", "   removed orphan tx %s\n", orphanHash.ToString());
                                vEraseQueue.push_back(orphanHash);
                            }
                            mempool.check(pcoinsTip);
                        }
                    }

                    BOOST_FOREACH (uint256 hash, vEraseQueue)
                        EraseOrphanTx(hash);
                } else if (tx.IsZerocoinSpend() && AcceptToMemoryPool(mempool, state, tx, true, &fMissingZerocoinInputs, false, ignoreFees)) {
                    //Presstab: ZCoin has a bunch of code commented out here. Is this something that should have more going on?
                    //Also there is nothing that handles fMissingZerocoinInputs. Does there need to be?
                    RelayTransaction(tx);
                    LogPrint("mempool", "AcceptToMemoryPool: Zerocoinspend peer=%d %s : accepted %s (poolsz %u)\n",
                        pfrom->id, pfrom->cleanSubVer,
                        tx.GetHash().ToString(),
                        mempool.mapTx.size());
                } else if (fMissingInputs) {
                    AddOrphanTx(tx, pfrom->GetId());

                    // DoS prevention: do not allow mapOrphanTransactions to grow unbounded
                    unsigned int nMaxOrphanTx = (unsigned int)std::max((int64_t)0, GetArg("-maxorphantx", DEFAULT_MAX_ORPHAN_TRANSACTIONS));
                    unsigned int nEvicted = LimitOrphanTxSize(nMaxOrphanTx);
                    if (nEvicted > 0)
                        LogPrint("mempool", "mapOrphan overflow, removed %u tx\n", nEvicted);
                } else {
                    if (pfrom->fWhitelisted) {
                        // Always relay transactions received from whitelisted peers, even
                        // if they were already in the mempool or rejected from it due
                        // to policy, allowing the node to function as a gateway for
                        // nodes hidden behind it.
                        //
                        // Never relay transactions that we would assign a non-zero DoS
                        // score for, as we expect peers to do the same with us in that
                        // case.
                        int nDoS = 0;
                        if (!state.IsInvalid(nDoS) || nDoS == 0) {
                            LogPrintf("Force relaying tx %s from whitelisted peer=%d\n", tx.GetHash().ToString(), pfrom->id);
                            RelayTransaction(tx);
                        } else {
                            LogPrintf("Not relaying invalid transaction %s from whitelisted peer=%d (%s)\n", tx.GetHash().ToString(), pfrom->id, state.GetRejectReason());
                        }
                    }
                }

                if (strCommand == NetMsgType::DSTX) {
                    CInv inv(MSG_DSTX, tx.GetHash());
                    RelayInv(inv);
                }

                int nDoS = 0;
                if (state.IsInvalid(nDoS)) {
                    LogPrint("mempoolrej", "%s from peer=%d %s was not accepted into the memory pool: %s\n", tx.GetHash().ToString(),
                        pfrom->id, pfrom->cleanSubVer,
                        state.GetRejectReason());
                    if (state.GetRejectCode() < REJECT_INTERNAL)
                        pfrom->PushMessage(NetMsgType::REJECT, strCommand, state.GetRejectCode(),
                            state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), inv.hash);
                    if (nDoS > 0 && (!state.CorruptionPossible() || State(pfrom->id)->fHaveWitness))
                        Misbehaving(pfrom->GetId(), nDoS);
                }
            }


            else if (strCommand == "headers" && Params().HeadersFirstSyncingActive() && !fImporting && !fReindex) // Ignore headers received while importing
            {
                std::vector<CBlockHeader> headers;

                // Bypass the normal CBlock deserialization, as we don't want to risk deserializing 2000 full blocks.
                unsigned int nCount = ReadCompactSize(vRecv);
                if (nCount > MAX_HEADERS_RESULTS) {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 20);
                    return error("headers message size = %u", nCount);
                }
                headers.resize(nCount);
                for (unsigned int n = 0; n < nCount; n++) {
                    vRecv >> headers[n];
                    ReadCompactSize(vRecv); // ignore tx count; assume it is 0.
                }

                LOCK(cs_main);

                if (nCount == 0) {
                    // Nothing interesting. Stop asking this peers for more headers.
                    return true;
                }
                CBlockIndex* pindexLast = NULL;
                BOOST_FOREACH (const CBlockHeader& header, headers) {
                    CValidationState state;
                    if (pindexLast != NULL && header.hashPrevBlock != pindexLast->GetBlockHash()) {
                        LOCK(cs_main);
                        Misbehaving(pfrom->GetId(), 20);
                        return error("non-continuous headers sequence");
                    }

                    /*TODO: this has a CBlock cast on it so that it will compile. There should be a solution for this
             * before headers are reimplemented on mainnet
             */
                    if (!AcceptBlockHeader((CBlock)header, state, &pindexLast)) {
                        int nDoS;
                        if (state.IsInvalid(nDoS)) {
                            if (nDoS > 0)
                                Misbehaving(pfrom->GetId(), nDoS);
                            std::string strError = "invalid header received " + header.GetHash().ToString();
                            return error(strError.c_str());
                        }
                    }
                }

                if (pindexLast)
                    UpdateBlockAvailability(pfrom->GetId(), pindexLast->GetBlockHash());

                if (nCount == MAX_HEADERS_RESULTS && pindexLast) {
                    // Headers message had its maximum size; the peer may have more headers.
                    // TODO: optimize: if pindexLast is an ancestor of chainActive.Tip or pindexBestHeader, continue
                    // from there instead.
                    LogPrintf("more getheaders (%d) to end to peer=%d (startheight:%d)\n", pindexLast->nHeight, pfrom->id, pfrom->nStartingHeight);
                    pfrom->PushMessage(NetMsgType::GETHEADERS, chainActive.GetLocator(pindexLast), uint256(0));
                }

                CheckBlockIndex();
            }

            else if (strCommand == NetMsgType::BLOCK && !fImporting && !fReindex) // Ignore blocks received while importing
            {
                CBlock block;
                vRecv >> block;

                CInv inv(MSG_BLOCK, block.GetHash());
                LogPrint("net", "received block %s peer=%d\n", inv.hash.ToString(), pfrom->id);

                //sometimes we will be sent their most recent block and its not the one we want, in that case tell where we are
                if (!mapBlockIndex.count(block.hashPrevBlock)) {
                    if (find(pfrom->vBlockRequested.begin(), pfrom->vBlockRequested.end(), block.GetHash()) != pfrom->vBlockRequested.end()) {
                        //we already asked for this block, so lets work backwards and ask for the previous block
                        pfrom->PushMessage(NetMsgType::GETBLOCKS, chainActive.GetLocator(), block.hashPrevBlock);
                        pfrom->vBlockRequested.push_back(block.hashPrevBlock);
                    } else {
                        //ask to sync to this block
                        pfrom->PushMessage(NetMsgType::GETBLOCKS, chainActive.GetLocator(), block.GetHash());
                        pfrom->vBlockRequested.push_back(block.GetHash());
                    }
                } else {
                    pfrom->AddInventoryKnown(inv);

                    CValidationState state;
                    if (!mapBlockIndex.count(block.GetHash())) {
                        ProcessNewBlock(state, pfrom, &block);
                        int nDoS;
                        if (state.IsInvalid(nDoS)) {
                            pfrom->PushMessage(NetMsgType::REJECT, strCommand, state.GetRejectCode(),
                                state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), inv.hash);
                            if (nDoS > 0) {
                                TRY_LOCK(cs_main, lockMain);
                                if (lockMain) Misbehaving(pfrom->GetId(), nDoS);
                            }
                        }
                        //disconnect this node if its old protocol version
                        pfrom->DisconnectOldProtocol(ActiveProtocol(), strCommand);
                    } else {
                        LogPrint("net", "%s : Already processed block %s, skipping ProcessNewBlock()\n", __func__, block.GetHash().GetHex());
                    }
                }
            }


            // This asymmetric behavior for inbound and outbound connections was introduced
            // to prevent a fingerprinting attack: an attacker can send specific fake addresses
            // to users' AddrMan and later request them by sending getaddr messages.
            // Making users (which are behind NAT and can only make outgoing connections) ignore
            // getaddr message mitigates the attack.
            else if ((strCommand == NetMsgType::GETADDR) && (pfrom->fInbound)) {
                pfrom->vAddrToSend.clear();
                vector<CAddress> vAddr = addrman.GetAddr();
                BOOST_FOREACH (const CAddress& addr, vAddr)
                    pfrom->PushAddress(addr);
            }


            else if (strCommand == NetMsgType::MEMPOOL) {
                LOCK2(cs_main, pfrom->cs_filter);

                std::vector<uint256> vtxid;
                mempool.queryHashes(vtxid);
                vector<CInv> vInv;
                BOOST_FOREACH (uint256& hash, vtxid) {
                    CInv inv(MSG_TX, hash);
                    CTransaction tx;
                    bool fInMemPool = mempool.lookup(hash, tx);
                    if (!fInMemPool) continue; // another thread removed since queryHashes, maybe...
                    if ((pfrom->pfilter && pfrom->pfilter->IsRelevantAndUpdate(tx)) ||
                        (!pfrom->pfilter))
                        vInv.push_back(inv);
                    if (vInv.size() == MAX_INV_SZ) {
                        pfrom->PushMessage(NetMsgType::INV, vInv);
                        vInv.clear();
                    }
                }
                if (vInv.size() > 0)
                    pfrom->PushMessage(NetMsgType::INV, vInv);
            }


            else if (strCommand == NetMsgType::PING) {
                if (pfrom->nVersion > BIP0031_VERSION) {
                    uint64_t nonce = 0;
                    vRecv >> nonce;
                    // Echo the message back with the nonce. This allows for two useful features:
                    //
                    // 1) A remote node can quickly check if the connection is operational
                    // 2) Remote nodes can measure the latency of the network thread. If this node
                    //    is overloaded it won't respond to pings quickly and the remote node can
                    //    avoid sending us more work, like chain download requests.
                    //
                    // The nonce stops the remote getting confused between different pings: without
                    // it, if the remote node sends a ping once per second and this node takes 5
                    // seconds to respond to each, the 5th ping the remote sends would appear to
                    // return very quickly.
                    pfrom->PushMessage(NetMsgType::PONG, nonce);
                }
            }


            else if (strCommand == NetMsgType::PONG) {
                int64_t pingUsecEnd = nTimeReceived;
                uint64_t nonce = 0;
                size_t nAvail = vRecv.in_avail();
                bool bPingFinished = false;
                std::string sProblem;

                if (nAvail >= sizeof(nonce)) {
                    vRecv >> nonce;

                    // Only process pong message if there is an outstanding ping (old ping without nonce should never pong)
                    if (pfrom->nPingNonceSent != 0) {
                        if (nonce == pfrom->nPingNonceSent) {
                            // Matching pong received, this ping is no longer outstanding
                            bPingFinished = true;
                            int64_t pingUsecTime = pingUsecEnd - pfrom->nPingUsecStart;
                            if (pingUsecTime > 0) {
                                // Successful ping time measurement, replace previous
                                pfrom->nPingUsecTime = pingUsecTime;
                            } else {
                                // This should never happen
                                sProblem = "Timing mishap";
                            }
                        } else {
                            // Nonce mismatches are normal when pings are overlapping
                            sProblem = "Nonce mismatch";
                            if (nonce == 0) {
                                // This is most likely a bug in another implementation somewhere, cancel this ping
                                bPingFinished = true;
                                sProblem = "Nonce zero";
                            }
                        }
                    } else {
                        sProblem = "Unsolicited pong without ping";
                    }
                } else {
                    // This is most likely a bug in another implementation somewhere, cancel this ping
                    bPingFinished = true;
                    sProblem = "Short payload";
                }

                if (!(sProblem.empty())) {
                    LogPrint("net", "pong peer=%d %s: %s, %x expected, %x received, %u bytes\n",
                        pfrom->id,
                        pfrom->cleanSubVer,
                        sProblem,
                        pfrom->nPingNonceSent,
                        nonce,
                        nAvail);
                }
                if (bPingFinished) {
                    pfrom->nPingNonceSent = 0;
                }
            }

            else if (fAlerts && strCommand == NetMsgType::ALERT) {
                CAlert alert;
                vRecv >> alert;

                uint256 alertHash = alert.GetHash();
                if (pfrom->setKnown.count(alertHash) == 0) {
                    if (alert.ProcessAlert()) {
                        // Relay
                        pfrom->setKnown.insert(alertHash);
                        {
                            LOCK(cs_vNodes);
                            BOOST_FOREACH (CNode* pnode, vNodes)
                                alert.RelayTo(pnode);
                        }
                    } else {
                        // Small DoS penalty so peers that send us lots of
                        // duplicate/expired/invalid-signature/whatever alerts
                        // eventually get banned.
                        // This isn't a Misbehaving(100) (immediate ban) because the
                        // peer might be an older or different implementation with
                        // a different signature key, etc.
                        LOCK(cs_main);
                        Misbehaving(pfrom->GetId(), 10);
                    }
                }
            }

            else if (!(nLocalServices & NODE_BLOOM) &&
                     (strCommand == NetMsgType::FILTERLOAD ||
                         strCommand == NetMsgType::FILTERADD ||
                         strCommand == NetMsgType::FILTERCLEAR)) {
                LogPrintf("bloom message=%s\n", strCommand);
                LOCK(cs_main);
                Misbehaving(pfrom->GetId(), 100);
            }

            else if (strCommand == NetMsgType::FILTERLOAD) {
                CBloomFilter filter;
                vRecv >> filter;

                if (!filter.IsWithinSizeConstraints()) {
                    // There is no excuse for sending a too-large filter
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 100);
                } else {
                    LOCK(pfrom->cs_filter);
                    delete pfrom->pfilter;
                    pfrom->pfilter = new CBloomFilter(filter);
                    pfrom->pfilter->UpdateEmptyFull();
                }
                pfrom->fRelayTxes = true;
            }


            else if (strCommand == NetMsgType::FILTERADD) {
                vector<unsigned char> vData;
                vRecv >> vData;

                // Nodes must NEVER send a data item > 520 bytes (the max size for a script data object,
                // and thus, the maximum size any matched object can have) in a filteradd message
                if (vData.size() > MAX_SCRIPT_ELEMENT_SIZE) {
                    LOCK(cs_main);
                    Misbehaving(pfrom->GetId(), 100);
                } else {
                    LOCK(pfrom->cs_filter);
                    if (pfrom->pfilter)
                        pfrom->pfilter->insert(vData);
                    else {
                        LOCK(cs_main);
                        Misbehaving(pfrom->GetId(), 100);
                    }
                }
            }


            else if (strCommand == NetMsgType::FILTERCLEAR) {
                LOCK(pfrom->cs_filter);
                delete pfrom->pfilter;
                pfrom->pfilter = new CBloomFilter();
                pfrom->fRelayTxes = true;
            }


            else if (strCommand == NetMsgType::REJECT) {
                if (fDebug) {
                    try {
                        string strMsg;
                        unsigned char ccode;
                        string strReason;
                        vRecv >> LIMITED_STRING(strMsg, CMessageHeader::COMMAND_SIZE) >> ccode >> LIMITED_STRING(strReason, MAX_REJECT_MESSAGE_LENGTH);

                        ostringstream ss;
                        ss << strMsg << " code " << itostr(ccode) << ": " << strReason;

                        if (strMsg == NetMsgType::BLOCK || strMsg == NetMsgType::TX) {
                            uint256 hash;
                            vRecv >> hash;
                            ss << ": hash " << hash.ToString();
                        }
                        LogPrint("net", "Reject %s\n", SanitizeString(ss.str()));
                    } catch (std::ios_base::failure& e) {
                        // Avoid feedback loops by preventing reject messages from triggering a new reject message.
                        LogPrint("net", "Unparseable reject message received\n");
                    }
                }
            } else {
                //probably one the extensions
                obfuScationPool.ProcessMessageObfuscation(pfrom, strCommand, vRecv);
                mnodeman.ProcessMessage(pfrom, strCommand, vRecv);
                budget.ProcessMessage(pfrom, strCommand, vRecv);
                masternodePayments.ProcessMessageMasternodePayments(pfrom, strCommand, vRecv);
                ProcessMessageSwiftTX(pfrom, strCommand, vRecv);
                ProcessSpork(pfrom, strCommand, vRecv);
                masternodeSync.ProcessMessage(pfrom, strCommand, vRecv);
            }


            return true;
        }

        // Note: whenever a protocol update is needed toggle between both implementations (comment out the formerly active one)
        //       so we can leave the existing clients untouched (old SPORK will stay on so they don't see even older clients).
        //       Those old clients won't react to the changes of the other (new) SPORK because at the time of their implementation
        //       it was the one which was commented out
        int ActiveProtocol()
        {
            if (IsSporkActive(SPORK_18_NEW_PROTOCOL_ENFORCEMENT_4))
                return MIN_PEER_PROTO_VERSION_AFTER_ENFORCEMENT;
            return MIN_PEER_PROTO_VERSION_BEFORE_ENFORCEMENT;
        }

        // requires LOCK(cs_vRecvMsg)
        bool ProcessMessages(CNode * pfrom)
        {
            //if (fDebug)
            //    LogPrintf("ProcessMessages(%u messages)\n", pfrom->vRecvMsg.size());

            //
            // Message format
            //  (4) message start
            //  (12) command
            //  (4) size
            //  (4) checksum
            //  (x) data
            //
            bool fOk = true;

            if (!pfrom->vRecvGetData.empty())
                ProcessGetData(pfrom);

            // this maintains the order of responses
            if (!pfrom->vRecvGetData.empty()) return fOk;

            std::deque<CNetMessage>::iterator it = pfrom->vRecvMsg.begin();
            while (!pfrom->fDisconnect && it != pfrom->vRecvMsg.end()) {
                // Don't bother if send buffer is too full to respond anyway
                if (pfrom->nSendSize >= SendBufferSize())
                    break;

                // get next message
                CNetMessage& msg = *it;

                //if (fDebug)
                //    LogPrintf("ProcessMessages(message %u msgsz, %u bytes, complete:%s)\n",
                //            msg.hdr.nMessageSize, msg.vRecv.size(),
                //            msg.complete() ? "Y" : "N");

                // end, if an incomplete message is found
                if (!msg.complete())
                    break;

                // at this point, any failure means we can delete the current message
                it++;

                // Scan for message start
                if (memcmp(msg.hdr.pchMessageStart, Params().MessageStart(), MESSAGE_START_SIZE) != 0) {
                    LogPrintf("PROCESSMESSAGE: INVALID MESSAGESTART %s peer=%d\n", SanitizeString(msg.hdr.GetCommand()), pfrom->id);
                    fOk = false;
                    break;
                }

                // Read header
                CMessageHeader& hdr = msg.hdr;
                if (!hdr.IsValid()) {
                    LogPrintf("PROCESSMESSAGE: ERRORS IN HEADER %s peer=%d\n", SanitizeString(hdr.GetCommand()), pfrom->id);
                    continue;
                }
                string strCommand = hdr.GetCommand();

                // Message size
                unsigned int nMessageSize = hdr.nMessageSize;

                // Checksum
                CDataStream& vRecv = msg.vRecv;
                uint256 hash = Hash(vRecv.begin(), vRecv.begin() + nMessageSize);
                unsigned int nChecksum = 0;
                memcpy(&nChecksum, &hash, sizeof(nChecksum));
                if (nChecksum != hdr.nChecksum) {
                    LogPrintf("ProcessMessages(%s, %u bytes): CHECKSUM ERROR nChecksum=%08x hdr.nChecksum=%08x\n",
                        SanitizeString(strCommand), nMessageSize, nChecksum, hdr.nChecksum);
                    continue;
                }

                // Process message
                bool fRet = false;
                try {
                    fRet = ProcessMessage(pfrom, strCommand, vRecv, msg.nTime);
                    boost::this_thread::interruption_point();
                } catch (std::ios_base::failure& e) {
                    pfrom->PushMessage(NetMsgType::REJECT, strCommand, REJECT_MALFORMED, string("error parsing message"));
                    if (strstr(e.what(), "end of data")) {
                        // Allow exceptions from under-length message on vRecv
                        LogPrintf("ProcessMessages(%s, %u bytes): Exception '%s' caught, normally caused by a message being shorter than its stated length\n", SanitizeString(strCommand), nMessageSize, e.what());
                    } else if (strstr(e.what(), "size too large")) {
                        // Allow exceptions from over-long size
                        LogPrintf("ProcessMessages(%s, %u bytes): Exception '%s' caught\n", SanitizeString(strCommand), nMessageSize, e.what());
                    } else {
                        PrintExceptionContinue(&e, "ProcessMessages()");
                    }
                } catch (boost::thread_interrupted) {
                    throw;
                } catch (std::exception& e) {
                    PrintExceptionContinue(&e, "ProcessMessages()");
                } catch (...) {
                    PrintExceptionContinue(NULL, "ProcessMessages()");
                }

                if (!fRet)
                    LogPrintf("ProcessMessage(%s, %u bytes) FAILED peer=%d\n", SanitizeString(strCommand), nMessageSize, pfrom->id);

                break;
            }

            // In case the connection got shut down, its receive buffer was wiped
            if (!pfrom->fDisconnect)
                pfrom->vRecvMsg.erase(pfrom->vRecvMsg.begin(), it);

            return fOk;
        }


        bool SendMessages(CNode * pto, bool fSendTrickle)
        {
            {
                // Don't send anything until we get their version message
                if (pto->nVersion == 0)
                    return true;

                //
                // Message: ping
                //
                bool pingSend = false;
                if (pto->fPingQueued) {
                    // RPC ping request by user
                    pingSend = true;
                }
                if (pto->nPingNonceSent == 0 && pto->nPingUsecStart + PING_INTERVAL * 1000000 < GetTimeMicros()) {
                    // Ping automatically sent as a latency probe & keepalive.
                    pingSend = true;
                }
                if (pingSend) {
                    uint64_t nonce = 0;
                    while (nonce == 0) {
                        GetRandBytes((unsigned char*)&nonce, sizeof(nonce));
                    }
                    pto->fPingQueued = false;
                    pto->nPingUsecStart = GetTimeMicros();
                    if (pto->nVersion > BIP0031_VERSION) {
                        pto->nPingNonceSent = nonce;
                        pto->PushMessage(NetMsgType::PING, nonce);
                    } else {
                        // Peer is too old to support ping command with nonce, pong will never arrive.
                        pto->nPingNonceSent = 0;
                        pto->PushMessage(NetMsgType::PING);
                    }
                }

                TRY_LOCK(cs_main, lockMain); // Acquire cs_main for IsInitialBlockDownload() and CNodeState()
                if (!lockMain)
                    return true;

                // Address refresh broadcast
                static int64_t nLastRebroadcast;
                if (!IsInitialBlockDownload() && (GetTime() - nLastRebroadcast > 24 * 60 * 60)) {
                    LOCK(cs_vNodes);
                    BOOST_FOREACH (CNode* pnode, vNodes) {
                        // Periodically clear setAddrKnown to allow refresh broadcasts
                        if (nLastRebroadcast)
                            pnode->setAddrKnown.clear();

                        // Rebroadcast our address
                        AdvertizeLocal(pnode);
                    }
                    if (!vNodes.empty())
                        nLastRebroadcast = GetTime();
                }

                //
                // Message: addr
                //
                if (fSendTrickle) {
                    vector<CAddress> vAddr;
                    vAddr.reserve(pto->vAddrToSend.size());
                    BOOST_FOREACH (const CAddress& addr, pto->vAddrToSend) {
                        // returns true if wasn't already contained in the set
                        if (pto->setAddrKnown.insert(addr).second) {
                            vAddr.push_back(addr);
                            // receiver rejects addr messages larger than 1000
                            if (vAddr.size() >= 1000) {
                                pto->PushMessage(NetMsgType::ADDR, vAddr);
                                vAddr.clear();
                            }
                        }
                    }
                    pto->vAddrToSend.clear();
                    if (!vAddr.empty())
                        pto->PushMessage(NetMsgType::ADDR, vAddr);
                }

                CNodeState& state = *State(pto->GetId());
                if (state.fShouldBan) {
                    if (pto->fWhitelisted)
                        LogPrintf("Warning: not punishing whitelisted peer %s!\n", pto->addr.ToString());
                    else {
                        pto->fDisconnect = true;
                        if (pto->addr.IsLocal())
                            LogPrintf("Warning: not banning local peer %s!\n", pto->addr.ToString());
                        else {
                            CNode::Ban(pto->addr, BanReasonNodeMisbehaving);
                        }
                    }
                    state.fShouldBan = false;
                }

                BOOST_FOREACH (const CBlockReject& reject, state.rejects)
                    pto->PushMessage(NetMsgType::REJECT, (string) "block", reject.chRejectCode, reject.strRejectReason, reject.hashBlock);
                state.rejects.clear();

                // Start block sync
                if (pindexBestHeader == NULL)
                    pindexBestHeader = chainActive.Tip();
                bool fFetch = state.fPreferredDownload || (nPreferredDownload == 0 && !pto->fClient && !pto->fOneShot); // Download if this is a nice peer, or we have no nice peers and this one might do.
                if (!state.fSyncStarted && !pto->fClient && fFetch /*&& !fImporting*/ && !fReindex) {
                    // Only actively request headers from a single peer, unless we're close to end of initial download.
                    if (nSyncStarted == 0 || pindexBestHeader->GetBlockTime() > GetAdjustedTime() - 6 * 60 * 60) { // NOTE: was "close to today" and 24h in Bitcoin
                        state.fSyncStarted = true;
                        nSyncStarted++;
                        //CBlockIndex *pindexStart = pindexBestHeader->pprev ? pindexBestHeader->pprev : pindexBestHeader;
                        //LogPrint("net", "initial getheaders (%d) to peer=%d (startheight:%d)\n", pindexStart->nHeight, pto->id, pto->nStartingHeight);
                        //pto->PushMessage(NetMsgType::GETHEADERS, chainActive.GetLocator(pindexStart), uint256(0));
                        pto->PushMessage(NetMsgType::GETBLOCKS, chainActive.GetLocator(chainActive.Tip()), uint256(0));
                    }
                }

                // Resend wallet transactions that haven't gotten in a block yet
                // Except during reindex, importing and IBD, when old wallet
                // transactions become unconfirmed and spams other nodes.
                if (!fReindex /*&& !fImporting && !IsInitialBlockDownload()*/) {
                    GetMainSignals().Broadcast();
                }

                //
                // Message: inventory
                //
                vector<CInv> vInv;
                vector<CInv> vInvWait;
                {
                    LOCK(pto->cs_inventory);
                    vInv.reserve(pto->vInventoryToSend.size());
                    vInvWait.reserve(pto->vInventoryToSend.size());
                    BOOST_FOREACH (const CInv& inv, pto->vInventoryToSend) {
                        if ((inv.type == MSG_TX || inv.type == MSG_WITNESS_TX) && pto->setInventoryKnown.count(inv))
                            continue;

                        // trickle out tx inv to protect privacy
                        if ((inv.type == MSG_TX || inv.type == MSG_WITNESS_TX) && !fSendTrickle) {
                            // 1/4 of tx invs blast to all immediately
                            static uint256 hashSalt;
                            if (hashSalt == 0)
                                hashSalt = GetRandHash();
                            uint256 hashRand = inv.hash ^ hashSalt;
                            hashRand = Hash(BEGIN(hashRand), END(hashRand));
                            bool fTrickleWait = ((hashRand & 3) != 0);

                            if (fTrickleWait) {
                                vInvWait.push_back(inv);
                                continue;
                            }
                        }

                        // returns true if wasn't already contained in the set
                        if (pto->setInventoryKnown.insert(inv).second) {
                            vInv.push_back(inv);
                            if (vInv.size() >= 1000) {
                                pto->PushMessage(NetMsgType::INV, vInv);
                                vInv.clear();
                            }
                        }
                    }
                    pto->vInventoryToSend = vInvWait;
                }
                if (!vInv.empty())
                    pto->PushMessage(NetMsgType::INV, vInv);

                // Detect whether we're stalling
                int64_t nNow = GetTimeMicros();
                if (!pto->fDisconnect && state.nStallingSince && state.nStallingSince < nNow - 1000000 * BLOCK_STALLING_TIMEOUT) {
                    // Stalling only triggers when the block download window cannot move. During normal steady state,
                    // the download window should be much larger than the to-be-downloaded set of blocks, so disconnection
                    // should only happen during initial block download.
                    LogPrintf("Peer=%d is stalling block download, disconnecting\n", pto->id);
                    pto->fDisconnect = true;
                }
                // In case there is a block that has been in flight from this peer for (2 + 0.5 * N) times the block interval
                // (with N the number of validated blocks that were in flight at the time it was requested), disconnect due to
                // timeout. We compensate for in-flight blocks to prevent killing off peers due to our own downstream link
                // being saturated. We only count validated in-flight blocks so peers can't advertize nonexisting block hashes
                // to unreasonably increase our timeout.
                if (!pto->fDisconnect && state.vBlocksInFlight.size() > 0 && state.vBlocksInFlight.front().nTime < nNow - 500000 * Params().TargetSpacing() * (4 + state.vBlocksInFlight.front().nValidatedQueuedBefore)) {
                    LogPrintf("Timeout downloading block %s from peer=%d, disconnecting\n", state.vBlocksInFlight.front().hash.ToString(), pto->id);
                    pto->fDisconnect = true;
                }

                //
                // Message: getdata (blocks)
                //
                vector<CInv> vGetData;
                if (!pto->fDisconnect && !pto->fClient && fFetch && state.nBlocksInFlight < MAX_BLOCKS_IN_TRANSIT_PER_PEER) {
                    vector<CBlockIndex*> vToDownload;
                    NodeId staller = -1;
                    FindNextBlocksToDownload(pto->GetId(), MAX_BLOCKS_IN_TRANSIT_PER_PEER - state.nBlocksInFlight, vToDownload, staller);
                    BOOST_FOREACH (CBlockIndex* pindex, vToDownload) {
                        if (State(pto->GetId())->fHaveWitness || GetSporkValue(SPORK_22_SEGWIT_ACTIVATION) > pindex->pprev->nTime) {
                            vGetData.push_back(CInv(State(staller)->fHaveWitness ? MSG_WITNESS_BLOCK : MSG_BLOCK, pindex->GetBlockHash()));
                            MarkBlockAsInFlight(pto->GetId(), pindex->GetBlockHash(), pindex);
                            LogPrint("net", "Requesting block %s (%d) peer=%d\n", pindex->GetBlockHash().ToString(),
                                pindex->nHeight, pto->id);
                        }
                    }
                    if (state.nBlocksInFlight == 0 && staller != -1) {
                        if (State(staller)->nStallingSince == 0) {
                            State(staller)->nStallingSince = nNow;
                            LogPrint("net", "Stall started peer=%d\n", staller);
                        }
                    }
                }

                //
                // Message: getdata (non-blocks)
                //
                while (!pto->fDisconnect && !pto->mapAskFor.empty() && (*pto->mapAskFor.begin()).first <= nNow) {
                    const CInv& inv = (*pto->mapAskFor.begin()).second;
                    if (!AlreadyHave(inv)) {
                        if (fDebug)
                            LogPrint("net", "Requesting %s peer=%d\n", inv.ToString(), pto->id);
                        vGetData.push_back(inv);
                        if (vGetData.size() >= 1000) {
                            pto->PushMessage(NetMsgType::GETDATA, vGetData);
                            vGetData.clear();
                        }
                    }
                    pto->mapAskFor.erase(pto->mapAskFor.begin());
                }
                if (!vGetData.empty())
                    pto->PushMessage(NetMsgType::GETDATA, vGetData);
            }
            return true;
        }


        bool CBlockUndo::WriteToDisk(CDiskBlockPos & pos, const uint256& hashBlock)
        {
            // Open history file to append
            CAutoFile fileout(OpenUndoFile(pos), SER_DISK, CLIENT_VERSION);
            if (fileout.IsNull())
                return error("CBlockUndo::WriteToDisk : OpenUndoFile failed");

            // Write index header
            unsigned int nSize = fileout.GetSerializeSize(*this);
            fileout << FLATDATA(Params().MessageStart()) << nSize;

            // Write undo data
            long fileOutPos = ftell(fileout.Get());
            if (fileOutPos < 0)
                return error("CBlockUndo::WriteToDisk : ftell failed");
            pos.nPos = (unsigned int)fileOutPos;
            fileout << *this;

            // calculate & write checksum
            CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
            hasher << hashBlock;
            hasher << *this;
            fileout << hasher.GetHash();

            return true;
        }

        bool CBlockUndo::ReadFromDisk(const CDiskBlockPos& pos, const uint256& hashBlock)
        {
            // Open history file to read
            CAutoFile filein(OpenUndoFile(pos, true), SER_DISK, CLIENT_VERSION);
            if (filein.IsNull())
                return error("CBlockUndo::ReadFromDisk : OpenBlockFile failed");

            // Read block
            uint256 hashChecksum;
            try {
                filein >> *this;
                filein >> hashChecksum;
            } catch (std::exception& e) {
                return error("%s : Deserialize or I/O error - %s", __func__, e.what());
            }

            // Verify checksum
            CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
            hasher << hashBlock;
            hasher << *this;
            if (hashChecksum != hasher.GetHash())
                return error("CBlockUndo::ReadFromDisk : Checksum mismatch");

            return true;
        }

        std::string CBlockFileInfo::ToString() const
        {
            return strprintf("CBlockFileInfo(blocks=%u, size=%u, heights=%u...%u, time=%s...%s)", nBlocks, nSize, nHeightFirst, nHeightLast, DateTimeStrFormat("%Y-%m-%d", nTimeFirst), DateTimeStrFormat("%Y-%m-%d", nTimeLast));
        }


        class CMainCleanup
        {
        public:
            CMainCleanup() {}
            ~CMainCleanup()
            {
                // block headers
                BlockMap::iterator it1 = mapBlockIndex.begin();
                for (; it1 != mapBlockIndex.end(); it1++)
                    delete (*it1).second;
                mapBlockIndex.clear();

                // orphan transactions
                mapOrphanTransactions.clear();
                mapOrphanTransactionsByPrev.clear();
            }
        } instance_of_cmaincleanup;
