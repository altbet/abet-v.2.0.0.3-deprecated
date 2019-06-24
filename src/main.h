// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Copyright (c) 2014-2015 The Dash developers
// Copyright (c) 2015-2018 The PIVX developers
// Copyright (c) 2018 - 2019 The Phore Developers
// Copyright (c) 2019 The Altbet Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_MAIN_H
#define BITCOIN_MAIN_H

#if defined(HAVE_CONFIG_H)
#include "config/altbet-config.h"
#endif

#include "amount.h"
#include "base58.h"
#include "chain.h"
#include "chainparams.h"
#include "coins.h"
#include "consensus/validation.h"
#include "net.h"
#include "pow.h"
#include "primitives/block.h"
#include "primitives/transaction.h"
#include "primitives/zerocoin.h"
#include "script/script.h"
#include "script/sigcache.h"
#include "script/standard.h"
#include "sync.h"
#include "tinyformat.h"
#include "txmempool.h"
#include "uint256.h"
#include "undo.h"
#include "validationinterface.h"

#include <algorithm>
#include <exception>
#include <map>
#include <set>
#include <stdint.h>
#include <string>
#include <utility>
#include <vector>

#include "libzerocoin/CoinSpend.h"

#include <boost/unordered_map.hpp>

class CBlockIndex;
class CBlockTreeDB;
class CZerocoinDB;
class CSporkDB;
class CBloomFilter;
class CInv;
class CScriptCheck;
class CValidationInterface;

struct CBlockTemplate;
struct CNodeStateStats;

static const std::set<std::string> BadAddr = {
	"AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7", "AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv",
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
	"ASt6SJUdLEQjFwyE2ifnVuoKq9TwGq3vn1", "AMHUKYfjNAgHzBLz6fEhLW5WJg6weRPZ4m", "AQJqFgQkv7KLbxbBWFJFkwDFJD7AFx3eHP"
};

/** Default for -blockmaxsize and -blockminsize, which control the range of sizes the mining code will create **/
static const unsigned int DEFAULT_BLOCK_MAX_SIZE = 750000;
static const unsigned int DEFAULT_BLOCK_MIN_SIZE = 0;
/** Default for -blockmaxcost, which control the range of block costs the mining code will create **/
static const unsigned int DEFAULT_BLOCK_MAX_COST = 3000000;
/** Default for -blockprioritysize, maximum space for zero/low-fee transactions **/
static const unsigned int DEFAULT_BLOCK_PRIORITY_SIZE = 50000;
/** Default for accepting alerts from the P2P network. */
static const bool DEFAULT_ALERTS = true;
/** The maximum size for transactions we're willing to relay/mine */
static const unsigned int MAX_STANDARD_TX_COST = 400000;
/** The maximum allowed number of signature check operations in a block (network rule) */
static const unsigned int MAX_BLOCK_SIGOPS_COST = 80000;
/** The maximum number of sigops we're willing to relay/mine in a single tx */
static const unsigned int MAX_STANDARD_TX_SIGOPS_COST = MAX_BLOCK_SIGOPS_COST / 5;
/** Maximum number of signature check operations in an IsStandard() P2SH script */
static const unsigned int MAX_P2SH_SIGOPS = 15;
/** The maximum number of sigops we're willing to relay/mine in a single tx */
static const int64_t MAX_TX_SIGOPS_COST = MAX_BLOCK_SIGOPS_COST / 5;
/** The maximum allowed size for a serialized block, in bytes (only for buffer size limits) */
static const unsigned int MAX_BLOCK_SERIALIZED_SIZE = 4000000;
/** The maximum allowed cost for a block, see BIP 141 (network rule) */
static const int64_t MAX_BLOCK_COST = 4000000;
/** The maximum allowed size for a block excluding witness data, in bytes (network rule) */
static const unsigned int MAX_BLOCK_BASE_SIZE = 1000000;
/** Default for -maxorphantx, maximum number of orphan transactions kept in memory */
static const unsigned int DEFAULT_MAX_ORPHAN_TRANSACTIONS = 100;
/** The maximum size of a blk?????.dat file (since 0.8) */
static const unsigned int MAX_BLOCKFILE_SIZE = 0x8000000; // 128 MiB
/** The pre-allocation chunk size for blk?????.dat files (since 0.8) */
static const unsigned int BLOCKFILE_CHUNK_SIZE = 0x1000000; // 16 MiB
/** The pre-allocation chunk size for rev?????.dat files (since 0.8) */
static const unsigned int UNDOFILE_CHUNK_SIZE = 0x100000; // 1 MiB
/** Coinbase transaction outputs can only be spent after this number of new blocks (network rule) */
static const int COINBASE_MATURITY = 50;
/** Maximum number of script-checking threads allowed */
static const int MAX_SCRIPTCHECK_THREADS = 16;
/** -par default (number of script-checking threads, 0 = auto) */
static const int DEFAULT_SCRIPTCHECK_THREADS = 0;
/** Number of blocks that can be requested at any given time from a single peer. */
static const int MAX_BLOCKS_IN_TRANSIT_PER_PEER = 256;
/** Timeout in seconds during which a peer must stall block download progress before being disconnected. */
static const unsigned int BLOCK_STALLING_TIMEOUT = 2;
/** Number of headers sent in one getheaders result. We rely on the assumption that if a peer sends
 *  less than this number, we reached their tip. Changing this value is a protocol upgrade. */
static const unsigned int MAX_HEADERS_RESULTS = 2000;
/** Size of the "block download window": how far ahead of our current height do we fetch?
 *  Larger windows tolerate larger download speed differences between peer, but increase the potential
 *  degree of disordering of blocks on disk (which make reindexing and in the future perhaps pruning
 *  harder). We'll probably want to make this a per-peer adaptive value at some point. */
static const unsigned int BLOCK_DOWNLOAD_WINDOW = 1024;
/** Time to wait (in seconds) between writing blockchain state to disk. */
static const unsigned int DATABASE_WRITE_INTERVAL = 3600;
/** Maximum length of reject messages. */
static const unsigned int MAX_REJECT_MESSAGE_LENGTH = 111;
/** Default for -bytespersigop */
static const unsigned int DEFAULT_BYTES_PER_SIGOP = 20;
/** The maximum number of witness stack items in a standard P2WSH script */
static const unsigned int MAX_STANDARD_P2WSH_STACK_ITEMS = 100;
/** The maximum size of each witness stack item in a standard P2WSH script */
static const unsigned int MAX_STANDARD_P2WSH_STACK_ITEM_SIZE = 80;
/** The maximum size of a standard witnessScript */
static const unsigned int MAX_STANDARD_P2WSH_SCRIPT_SIZE = 3600;

/** Enable bloom filter */
static const bool DEFAULT_PEERBLOOMFILTERS = true;

struct BlockHasher {
    size_t operator()(const uint256& hash) const { return hash.GetLow64(); }
};

extern CScript COINBASE_FLAGS;
extern CCriticalSection cs_main;
extern CTxMemPool mempool;
typedef boost::unordered_map<uint256, CBlockIndex*, BlockHasher> BlockMap;
extern BlockMap mapBlockIndex;
extern uint64_t nLastBlockTx;
extern uint64_t nLastBlockCost;
extern const std::string strMessageMagic;
extern int64_t nTimeBestReceived;
extern CWaitableCriticalSection csBestBlock;
extern CConditionVariable cvBlockChange;
extern bool fImporting;
extern bool fReindex;
extern int nScriptCheckThreads;
extern bool fTxIndex;
extern bool fAddrIndex;
extern bool fIsBareMultisigStd;
extern bool fCheckBlockIndex;
extern unsigned int nCoinCacheSize;
extern CFeeRate minRelayTxFee;
extern bool fAlerts;
extern bool fVerifyingBlocks;

extern bool fLargeWorkForkFound;
extern bool fLargeWorkInvalidChainFound;

extern unsigned int StakeMinAgev2();
extern int64_t nLastCoinStakeSearchInterval;
extern int64_t nLastCoinStakeSearchTime;
extern int64_t nReserveBalance;

extern std::map<uint256, int64_t> mapRejectedBlocks;
extern std::map<unsigned int, unsigned int> mapHashedBlocks;
extern std::set<std::pair<COutPoint, unsigned int> > setStakeSeen;
extern std::map<uint256, int64_t> mapZerocoinspends; //txid, time received

/** Best header we've seen so far (used for getheaders queries' starting points). */
extern CBlockIndex* pindexBestHeader;

/** Minimum disk space required - used in CheckDiskSpace() */
static const uint64_t nMinDiskSpace = 52428800;

/** Register a wallet to receive updates from core */
void RegisterValidationInterface(CValidationInterface* pwalletIn);
/** Unregister a wallet from core */
void UnregisterValidationInterface(CValidationInterface* pwalletIn);
/** Unregister all wallets from core */
void UnregisterAllValidationInterfaces();
/** Push an updated transaction to all registered wallets */
void SyncWithWallets(const CTransaction& tx, const CBlock* pblock = NULL);

/** Register with a network node to receive its signals */
void RegisterNodeSignals(CNodeSignals& nodeSignals);
/** Unregister a network node */
void UnregisterNodeSignals(CNodeSignals& nodeSignals);

/**
 * Process an incoming block. This only returns after the best known valid
 * block is made active. Note that it does not, however, guarantee that the
 * specific block passed to it has been checked for validity!
 *
 * @param[out]  state   This may be set to an Error state if any error occurred processing it, including during validation/connection/etc of otherwise unrelated blocks during reorganisation; or it may be set to an Invalid state if pblock is itself invalid (but this is not guaranteed even when the block is checked). If you want to *possibly* get feedback on whether pblock is valid, you must also install a CValidationInterface - this will have its BlockChecked method called whenever *any* block completes validation.
 * @param[in]   pfrom   The node which we are receiving the block from; it is added to mapBlockSource and may be penalised if the block is invalid.
 * @param[in]   pblock  The block we want to process.
 * @param[out]  dbp     If pblock is stored to disk (or already there), this will be set to its location.
 * @return True if state.IsValid()
 */
bool ProcessNewBlock(CValidationState& state, CNode* pfrom, CBlock* pblock, CDiskBlockPos* dbp = NULL);
/** Check whether enough disk space is available for an incoming block */
bool CheckDiskSpace(uint64_t nAdditionalBytes = 0);
/** Open a block file (blk?????.dat) */
FILE* OpenBlockFile(const CDiskBlockPos& pos, bool fReadOnly = false);
/** Open an undo file (rev?????.dat) */
FILE* OpenUndoFile(const CDiskBlockPos& pos, bool fReadOnly = false);
/** Translation to a filesystem path */
boost::filesystem::path GetBlockPosFilename(const CDiskBlockPos& pos, const char* prefix);
/** Import blocks from an external file */
bool LoadExternalBlockFile(FILE* fileIn, CDiskBlockPos* dbp = NULL);
/** Initialize a new block tree database + block data on disk */
bool InitBlockIndex();
/** Load the block tree and coins database from disk */
bool LoadBlockIndex(std::string& strError);
/** Unload database information */
void UnloadBlockIndex();
/** See whether the protocol update is enforced for connected nodes */
int ActiveProtocol();
/** Process protocol messages received from a given node */
bool ProcessMessages(CNode* pfrom);
/**
 * Send queued protocol messages to be sent to a give node.
 *
 * @param[in]   pto             The node which we are sending messages to.
 * @param[in]   fSendTrickle    When true send the trickled data, otherwise trickle the data until true.
 */
bool SendMessages(CNode* pto, bool fSendTrickle);
/** Run an instance of the script checking thread */
void ThreadScriptCheck();

// ***TODO*** probably not the right place for these 2
/** Check whether a block hash satisfies the proof-of-work requirement specified by nBits */
bool CheckProofOfWork(uint256 hash, unsigned int nBits);

/** Check whether we are doing an initial block download (synchronizing from disk or network) */
bool IsInitialBlockDownload();
/** Format a string that describes several potential problems detected by the core */
std::string GetWarnings(std::string strFor);
/** Retrieve a transaction (from memory pool, or from disk, if possible) */
bool GetTransaction(const uint256& hash, CTransaction& tx, uint256& hashBlock, bool fAllowSlow = false);
/** Find the best known block, and make it the tip of the block chain */

bool DisconnectBlocksAndReprocess(int blocks);

// ***TODO***
double ConvertBitsToDouble(unsigned int nBits);
int64_t GetMasternodePayment(int nHeight, int64_t blockValue, int nMasternodeCount = 0);
unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader* pblock, bool fProofOfStake);

bool ActivateBestChain(CValidationState& state, CBlock* pblock = NULL, bool fAlreadyChecked = false);
CAmount GetBlockValue(int nHeight);
bool IsTreasuryBlock(int nHeight);
bool IsPaybackBlock(int nHeight);
int64_t GetTreasuryAward(int nHeight);

/** Create a new block index entry for a given block hash */
CBlockIndex* InsertBlockIndex(uint256 hash);
/** Abort with a message */
bool AbortNode(const std::string& msg, const std::string& userMessage = "");
/** Get statistics from node state */
bool GetNodeStateStats(NodeId nodeid, CNodeStateStats& stats);
/** Increase a node's misbehavior score. */
void Misbehaving(NodeId nodeid, int howmuch);
/** Flush all state, indexes and buffers to disk. */
void FlushStateToDisk();


/** (try to) add transaction to memory pool **/
bool AcceptToMemoryPool(CTxMemPool& pool, CValidationState& state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee = false, bool ignoreFees = false);

bool AcceptableInputs(CTxMemPool& pool, CValidationState& state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee = false, bool isDSTX = false);

int GetInputAge(CTxIn& vin);
int GetInputAgeIX(uint256 nTXHash, CTxIn& vin);
bool GetCoinAge(const CTransaction& tx, unsigned int nTxTime, uint64_t& nCoinAge);
int GetIXConfirmations(uint256 nTXHash);

struct CNodeStateStats {
    int nMisbehavior;
    int nSyncHeight;
    int nCommonHeight;
    std::vector<int> vHeightInFlight;
};

struct CDiskTxPos : public CDiskBlockPos {
    unsigned int nTxOffset; // after header

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(*(CDiskBlockPos*)this);
        READWRITE(VARINT(nTxOffset));
    }

    CDiskTxPos(const CDiskBlockPos& blockIn, unsigned int nTxOffsetIn) : CDiskBlockPos(blockIn.nFile, blockIn.nPos), nTxOffset(nTxOffsetIn)
    {
    }

    CDiskTxPos()
    {
        SetNull();
    }

    void SetNull()
    {
        CDiskBlockPos::SetNull();
        nTxOffset = 0;
    }

    friend bool operator<(const CDiskTxPos& a, const CDiskTxPos& b)
    {
        return (a.nFile < b.nFile || ((a.nFile == b.nFile) && (a.nPos < b.nPos || ((a.nPos == b.nPos) && (a.nTxOffset < b.nTxOffset)))));
    }
};

struct CExtDiskTxPos : public CDiskTxPos {
    unsigned int nHeight;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(*(CDiskTxPos*)this);
        READWRITE(VARINT(nHeight));
    }

    CExtDiskTxPos(const CDiskTxPos& pos, int nHeightIn) : CDiskTxPos(pos), nHeight(nHeightIn)
    {
    }

    CExtDiskTxPos()
    {
        SetNull();
    }

    void SetNull()
    {
        CDiskTxPos::SetNull();
        nHeight = 0;
    }

    friend bool operator==(const CExtDiskTxPos& a, const CExtDiskTxPos& b)
    {
        return (a.nHeight == b.nHeight && a.nFile == b.nFile && a.nPos == b.nPos && a.nTxOffset == b.nTxOffset);
    }

    friend bool operator!=(const CExtDiskTxPos& a, const CExtDiskTxPos& b)
    {
        return !(a == b);
    }

    friend bool operator<(const CExtDiskTxPos& a, const CExtDiskTxPos& b)
    {
        if (a.nHeight < b.nHeight) return true;
        if (a.nHeight > b.nHeight) return false;
        return ((const CDiskTxPos)a < (const CDiskTxPos)b);
    }
};

CAmount GetMinRelayFee(const CTransaction& tx, unsigned int nBytes, bool fAllowFree);
bool MoneyRange(CAmount nValueOut);

/**
 * Check transaction inputs, and make sure any
 * pay-to-script-hash transactions are evaluating IsStandard scripts
 *
 * Why bother? To avoid denial-of-service attacks; an attacker
 * can submit a standard HASH... OP_EQUAL transaction,
 * which will get accepted into blocks. The redemption
 * script can be anything; an attacker could use a very
 * expensive-to-check-upon-redemption script like:
 *   DUP CHECKSIG DROP ... repeated 100 times... OP_1
 */

/**
 * Check for standard transaction types
 * @param[in] mapInputs    Map of previous transactions that have outputs we're spending
 * @return True if all inputs (scriptSigs) use only standard transaction forms
 */
bool AreInputsStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs);

/**
 * Count ECDSA signature operations the old-fashioned (pre-0.6) way
 * @return number of sigops this transaction's outputs will produce when spent
 * @see CTransaction::FetchInputs
 */
unsigned int GetLegacySigOpCount(const CTransaction& tx);

/**
 * Count ECDSA signature operations in pay-to-script-hash inputs.
 *
 * @param[in] mapInputs Map of previous transactions that have outputs we're spending
 * @return maximum number of sigops required to validate this transaction's inputs
 * @see CTransaction::FetchInputs
 */
unsigned int GetP2SHSigOpCount(const CTransaction& tx, const CCoinsViewCache& mapInputs);

/**
 * Compute total signature operation cost of a transaction.
 * @param[in] tx     Transaction for which we are computing the cost
 * @param[in] inputs Map of previous transactions that have outputs we're spending
 * @param[out] flags Script verification flags
 * @return Total signature operation cost of tx
 */
int64_t GetTransactionSigOpCost(const CTransaction& tx, const CCoinsViewCache& inputs, int flags);

/**
 * Check whether all inputs of this transaction are valid (no double spends, scripts & sigs, amounts)
 * This does not modify the UTXO set. If pvChecks is not NULL, script checks are pushed onto it
 * instead of being performed inline.
 */
bool CheckInputs(const CTransaction& tx, CValidationState& state, const CCoinsViewCache& view, bool fScriptChecks, unsigned int flags, bool cacheStore, std::vector<CScriptCheck>* pvChecks = NULL);

/** Apply the effects of this transaction on the UTXO set represented by view */
void UpdateCoins(const CTransaction& tx, CValidationState& state, CCoinsViewCache& inputs, CTxUndo& txundo, int nHeight);

/** Context-independent validity checks */
bool CheckTransaction(const CTransaction& tx, bool fZerocoinActive, bool fRejectBadUTXO, CValidationState& state, bool fWitnessActive);
bool CheckZerocoinMint(const uint256& txHash, const CTxOut& txout, CValidationState& state, bool fCheckOnly = false);
bool CheckZerocoinSpend(const CTransaction& tx, bool fVerifySignature, CValidationState& state);
bool ContextualCheckZerocoinSpend(const CTransaction& tx, const libzerocoin::CoinSpend& spend, CBlockIndex* pindex);
libzerocoin::CoinSpend TxInToZerocoinSpend(const CTxIn& txin);
bool TxOutToPublicCoin(const CTxOut txout, libzerocoin::PublicCoin& pubCoin, CValidationState& state);
bool BlockToPubcoinList(const CBlock& block, list<libzerocoin::PublicCoin>& listPubcoins);
bool BlockToZerocoinMintList(const CBlock& block, std::list<CZerocoinMint>& vMints);
bool BlockToMintValueVector(const CBlock& block, const libzerocoin::CoinDenomination denom, std::vector<CBigNum>& vValues);
std::list<libzerocoin::CoinDenomination> ZerocoinSpendListFromBlock(const CBlock& block);
void FindMints(vector<CMintMeta> vMintsToFind, vector<CMintMeta>& vMintsToUpdate, vector<CMintMeta>& vMissingMints);
bool GetZerocoinMint(const CBigNum& bnPubcoin, uint256& txHash);
bool IsSerialKnown(const CBigNum& bnSerial);
bool IsSerialInBlockchain(const CBigNum& bnSerial, int& nHeightTx);
bool IsSerialInBlockchain(const uint256& hashSerial, int& nHeightTx, uint256& txidSpend);
bool IsSerialInBlockchain(const uint256& hashSerial, int& nHeightTx, uint256& txidSpend, CTransaction& tx);
bool IsPubcoinInBlockchain(const uint256& hashPubcoin, uint256& txid);
bool RemoveSerialFromDB(const CBigNum& bnSerial);
int GetZerocoinStartHeight();
libzerocoin::ZerocoinParams* GetZerocoinParams(int nHeight);
bool IsTransactionInChain(const uint256& txId, int& nHeightTx, CTransaction& tx);
bool IsTransactionInChain(const uint256& txId, int& nHeightTx);
bool IsBlockHashInChain(const uint256& hashBlock);
void RecalculateZABETSpent();
void RecalculateZABETMinted();
bool RecalculateABETSupply(int nHeightStart);
bool ReindexAccumulators(list<uint256>& listMissingCheckpoints, string& strError);


/**
 * Check if transaction will be final in the next block to be created.
 *
 * Calls IsFinalTx() with current block height and appropriate block time.
 *
 * See consensus/consensus.h for flag definitions.
 */
bool CheckFinalTx(const CTransaction& tx, int flags = -1);

/** Check for standard transaction types
 * @return True if all outputs (scriptPubKeys) use only standard transaction forms
 */
bool IsStandardTx(const CTransaction& tx, std::string& reason);

bool IsFinalTx(const CTransaction& tx, int nBlockHeight = 0, int64_t nBlockTime = 0);

/** Undo information for a CBlock */
class CBlockUndo
{
public:
    std::vector<CTxUndo> vtxundo; // for all but the coinbase

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(vtxundo);
    }

    bool WriteToDisk(CDiskBlockPos& pos, const uint256& hashBlock);
    bool ReadFromDisk(const CDiskBlockPos& pos, const uint256& hashBlock);
};


/**
 * Closure representing one script verification
 * Note that this stores references to the spending transaction
 */
class CScriptCheck
{
private:
    CScript scriptPubKey;
    CAmount amount;
    const CTransaction* ptxTo;
    unsigned int nIn;
    unsigned int nFlags;
    bool cacheStore;
    ScriptError error;

public:
    CScriptCheck() : amount(0), ptxTo(0), nIn(0), nFlags(0), cacheStore(false), error(SCRIPT_ERR_UNKNOWN_ERROR) {}
    CScriptCheck(const CCoins& txFromIn, const CTransaction& txToIn, unsigned int nInIn, unsigned int nFlagsIn, bool cacheIn) : scriptPubKey(txFromIn.vout[txToIn.vin[nInIn].prevout.n].scriptPubKey), amount(txFromIn.vout[txToIn.vin[nInIn].prevout.n].nValue),
                                                                                                                                ptxTo(&txToIn), nIn(nInIn), nFlags(nFlagsIn), cacheStore(cacheIn), error(SCRIPT_ERR_UNKNOWN_ERROR) {}

    bool operator()();

    void swap(CScriptCheck& check)
    {
        scriptPubKey.swap(check.scriptPubKey);
        std::swap(ptxTo, check.ptxTo);
        std::swap(amount, check.amount);
        std::swap(nIn, check.nIn);
        std::swap(nFlags, check.nFlags);
        std::swap(cacheStore, check.cacheStore);
        std::swap(error, check.error);
    }

    ScriptError GetScriptError() const { return error; }
};


/** Functions for disk access for blocks */
bool WriteBlockToDisk(CBlock& block, CDiskBlockPos& pos);
bool ReadBlockFromDisk(CBlock& block, const CDiskBlockPos& pos);
bool ReadBlockFromDisk(CBlock& block, const CBlockIndex* pindex);
bool ReadTransaction(CTransaction& tx, const CDiskTxPos& pos, uint256& hashBlock);
bool FindTransactionsByDestination(const CTxDestination& dest, std::set<CExtDiskTxPos>& setpos);


/** Functions for validating blocks and updating the block tree */

/** Undo the effects of this block (with given index) on the UTXO set represented by coins.
 *  In case pfClean is provided, operation will try to be tolerant about errors, and *pfClean
 *  will be true if no problems were found. Otherwise, the return value will be false in case
 *  of problems. Note that in any case, coins may be modified. */
bool DisconnectBlock(CBlock& block, CValidationState& state, CBlockIndex* pindex, CCoinsViewCache& coins, bool* pfClean = NULL);

/** Reprocess a number of blocks to try and get on the correct chain again **/
bool DisconnectBlocksAndReprocess(int blocks);

/** Apply the effects of this block (with given index) on the UTXO set represented by coins */
bool ConnectBlock(const CBlock& block, CValidationState& state, CBlockIndex* pindex, CCoinsViewCache& coins, bool fJustCheck, bool fAlreadyChecked = false);

/** Context-independent validity checks */
bool CheckBlockHeader(const CBlockHeader& block, CValidationState& state, bool fCheckPOW = true);
bool CheckBlock(const CBlock& block, CValidationState& state, bool fCheckPOW = true, bool fCheckMerkleRoot = true, bool fCheckSig = true);
bool CheckWork(const CBlock block, CBlockIndex* const pindexPrev);

/** Context-dependent validity checks */
bool ContextualCheckBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex* pindexPrev);
bool ContextualCheckBlock(const CBlock& block, CValidationState& state, CBlockIndex* pindexPrev);

/** Check a block is completely valid from start to finish (only works on top of our current best block, with cs_main held) */
bool TestBlockValidity(CValidationState& state, const CBlock& block, CBlockIndex* pindexPrev, bool fCheckPOW = true, bool fCheckMerkleRoot = true);

/** Store block on disk. If dbp is provided, the file is known to already reside on disk */
bool AcceptBlock(CBlock& block, CValidationState& state, CBlockIndex** pindex, CDiskBlockPos* dbp = NULL, bool fAlreadyCheckedBlock = false);
bool AcceptBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex** ppindex = NULL);

bool RewindBlockIndex(const CChainParams& params);

/** Update uncommitted block structures (currently: only the witness nonce). This is safe for submitted blocks. */
void UpdateUncommittedBlockStructures(CBlock& block, const CBlockIndex* pindexPrev);

/** Produce the necessary coinbase commitment for a block (modifies the hash, don't call for mined blocks). */
std::vector<unsigned char> GenerateCoinbaseCommitment(CBlock& block, const CBlockIndex* pindexPrev);


class CBlockFileInfo
{
public:
    unsigned int nBlocks;      //! number of blocks stored in file
    unsigned int nSize;        //! number of used bytes of block file
    unsigned int nUndoSize;    //! number of used bytes in the undo file
    unsigned int nHeightFirst; //! lowest height of block in file
    unsigned int nHeightLast;  //! highest height of block in file
    uint64_t nTimeFirst;       //! earliest time of block in file
    uint64_t nTimeLast;        //! latest time of block in file

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(VARINT(nBlocks));
        READWRITE(VARINT(nSize));
        READWRITE(VARINT(nUndoSize));
        READWRITE(VARINT(nHeightFirst));
        READWRITE(VARINT(nHeightLast));
        READWRITE(VARINT(nTimeFirst));
        READWRITE(VARINT(nTimeLast));
    }

    void SetNull()
    {
        nBlocks = 0;
        nSize = 0;
        nUndoSize = 0;
        nHeightFirst = 0;
        nHeightLast = 0;
        nTimeFirst = 0;
        nTimeLast = 0;
    }

    CBlockFileInfo()
    {
        SetNull();
    }

    std::string ToString() const;

    /** update statistics (does not update nSize) */
    void AddBlock(unsigned int nHeightIn, uint64_t nTimeIn)
    {
        if (nBlocks == 0 || nHeightFirst > nHeightIn)
            nHeightFirst = nHeightIn;
        if (nBlocks == 0 || nTimeFirst > nTimeIn)
            nTimeFirst = nTimeIn;
        nBlocks++;
        if (nHeightIn > nHeightLast)
            nHeightLast = nHeightIn;
        if (nTimeIn > nTimeLast)
            nTimeLast = nTimeIn;
    }
};

/** RAII wrapper for VerifyDB: Verify consistency of the block and coin databases */
class CVerifyDB
{
public:
    CVerifyDB();
    ~CVerifyDB();
    bool VerifyDB(CCoinsView* coinsview, int nCheckLevel, int nCheckDepth);
};

/** Find the last common block between the parameter chain and a locator. */
CBlockIndex* FindForkInGlobalIndex(const CChain& chain, const CBlockLocator& locator);

/** Mark a block as invalid. */
bool InvalidateBlock(CValidationState& state, CBlockIndex* pindex);

/** Remove invalidity status from a block and its descendants. */
bool ReconsiderBlock(CValidationState& state, CBlockIndex* pindex);

/** The currently-connected chain of blocks. */
extern CChain chainActive;

/** Global variable that points to the active CCoinsView (protected by cs_main) */
extern CCoinsViewCache* pcoinsTip;

/** Global variable that points to the active block tree (protected by cs_main) */
extern CBlockTreeDB* pblocktree;

/** Global variable that points to the zerocoin database (protected by cs_main) */
extern CZerocoinDB* zerocoinDB;

/** Global variable that points to the spork database (protected by cs_main) */
extern CSporkDB* pSporkDB;

struct CBlockTemplate {
    CBlock block;
    std::vector<CAmount> vTxFees;
    std::vector<int64_t> vTxSigOpsCost;
    std::vector<unsigned char> vchCoinbaseCommitment;
};

int64_t GetVirtualTransactionSize(const CTransaction& tx);
int64_t GetVirtualTransactionSize(int64_t nCost);

#endif // BITCOIN_MAIN_H
