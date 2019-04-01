// Copyright (c) 2012-2014 The Bitcoin developers
// Copyright (c) 2014-2015 The Dash developers
// Copyright (c) 2015-2017 The PIVX developers
// Copyright (c) 2019 The Altbet Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_VERSION_H
#define BITCOIN_VERSION_H

/**
 * network protocol versioning
 */
// Initial Release was 72000
// Initial Rewards Fix on 72001 by TFinch
// Exchange version, GUI update with chart 72004 TFinch
// Min Stake Amount changed to 15 coins 72005 TFinch
static const int PROTOCOL_VERSION = 72006;

//! initial proto version, to be increased after version/verack negotiation
static const int INIT_PROTO_VERSION = 209;

//! In this version, 'getheaders' was introduced.
static const int GETHEADERS_VERSION = 70077;

//! disconnect from peers older than this proto version
static const int MIN_PEER_PROTO_VERSION_BEFORE_ENFORCEMENT = 72005;
static const int MIN_PEER_PROTO_VERSION_AFTER_ENFORCEMENT = 72006;

static const int MIN_PEER_VERSION_FIXED_SIGTIME = 72006;

//! masternodes older than this proto version use old strMessage format for mnannounce
static const int MIN_PEER_MNANNOUNCE = 70003;
//! In this version, "Fake Stake" vulnerability mitigations were introduced.
// Corrected to last current release 72004 instead of 72002
// Both 72002 and 72004 correlate to the same Fake Stake update.
static const int FAKE_STAKE_VERSION = 72004;

// In this version we change the min amount to stake with from any amount to 15 coins
static const int STAKEV2_VERSION = 72005;

//! nTime field added to CAddress, starting with this version;
//! if possible, avoid requesting addresses nodes older than this
static const int CADDR_TIME_VERSION = 31402;

//! only request blocks from nodes outside this range of versions
static const int NOBLKS_VERSION_START = 32000;
static const int NOBLKS_VERSION_END = 70700;

//! BIP 0031, pong message, is enabled for all versions AFTER this one
static const int BIP0031_VERSION = 60000;

//! "mempool" command, enhanced "getdata" behavior starts with this version
static const int MEMPOOL_GD_VERSION = 60002;

//! "filter*" commands are disabled without NODE_BLOOM after and including this version
static const int NO_BLOOM_VERSION = 70005;


#endif // BITCOIN_VERSION_H
