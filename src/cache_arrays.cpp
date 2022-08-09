/** $lic$
 * Copyright (C) 2012-2015 by Massachusetts Institute of Technology
 * Copyright (C) 2010-2013 by The Board of Trustees of Stanford University
 *
 * This file is part of zsim.
 *
 * zsim is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, version 2.
 *
 * If you use this software in your research, we request that you reference
 * the zsim paper ("ZSim: Fast and Accurate Microarchitectural Simulation of
 * Thousand-Core Systems", Sanchez and Kozyrakis, ISCA-40, June 2013) as the
 * source of the simulator in any publications that use this software, and that
 * you send us a citation of your work.
 *
 * zsim is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program. If not, see <http://www.gnu.org/licenses/>.
 */

#include "cache_arrays.h"
#include "hash.h"
#include "repl_policies.h"

/* Set-associative array implementation */

SetAssocArray::SetAssocArray(uint32_t _numLines, uint32_t _assoc, ReplPolicy* _rp, HashFamily* _hf) : rp(_rp), hf(_hf), numLines(_numLines), assoc(_assoc)  {
    array = gm_calloc<Address>(numLines);
    numSets = numLines/assoc;
    setMask = numSets - 1;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
}

int32_t SetAssocArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement) {
    uint32_t set = hf->hash(0, lineAddr) & setMask;
    uint32_t first = set*assoc;
    for (uint32_t id = first; id < first + assoc; id++) {
        if (array[id] ==  lineAddr) {
            if (updateReplacement) rp->update(id, req);
            return id;
        }
    }
    return -1;
}

uint32_t SetAssocArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr) { //TODO: Give out valid bit of wb cand?
    uint32_t set = hf->hash(0, lineAddr) & setMask;
    uint32_t first = set*assoc;

    uint32_t candidate = rp->rankCands(req, SetAssocCands(first, first+assoc));

    *wbLineAddr = array[candidate];
    return candidate;
}

void SetAssocArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    rp->replaced(candidate);
    array[candidate] = lineAddr;
    rp->update(candidate, req);
}


/* ZCache implementation */

ZArray::ZArray(uint32_t _numLines, uint32_t _ways, uint32_t _candidates, ReplPolicy* _rp, HashFamily* _hf) //(int _size, int _lineSize, int _assoc, int _zassoc, ReplacementPolicy<T>* _rp, int _hashType)
    : rp(_rp), hf(_hf), numLines(_numLines), ways(_ways), cands(_candidates)
{
    assert_msg(ways > 1, "zcaches need >=2 ways to work");
    assert_msg(cands >= ways, "candidates < ways does not make sense in a zcache");
    assert_msg(numLines % ways == 0, "number of lines is not a multiple of ways");

    //Populate secondary parameters
    numSets = numLines/ways;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
    setMask = numSets - 1;

    lookupArray = gm_calloc<uint32_t>(numLines);
    array = gm_calloc<Address>(numLines);
    for (uint32_t i = 0; i < numLines; i++) {
        lookupArray[i] = i;  // start with a linear mapping; with swaps, it'll get progressively scrambled
    }
    swapArray = gm_calloc<uint32_t>(cands/ways + 2);  // conservative upper bound (tight within 2 ways)
}

void ZArray::initStats(AggregateStat* parentStat) {
    AggregateStat* objStats = new AggregateStat();
    objStats->init("array", "ZArray stats");
    statSwaps.init("swaps", "Block swaps in replacement process");
    objStats->append(&statSwaps);
    parentStat->append(objStats);
}

int32_t ZArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement) {
    /* Be defensive: If the line is 0, panic instead of asserting. Now this can
     * only happen on a segfault in the main program, but when we move to full
     * system, phy page 0 might be used, and this will hit us in a very subtle
     * way if we don't check.
     */
    if (unlikely(!lineAddr)) panic("ZArray::lookup called with lineAddr==0 -- your app just segfaulted");

    for (uint32_t w = 0; w < ways; w++) {
        uint32_t lineId = lookupArray[w*numSets + (hf->hash(w, lineAddr) & setMask)];
        if (array[lineId] == lineAddr) {
            if (updateReplacement) {
                rp->update(lineId, req);
            }
            return lineId;
        }
    }
    return -1;
}

void ZArray::dfswalk(const Address lineAddr, const int cnt, int &n) {
    if (cnt == n) {
        // Cycle present. REHASH.
        return;
    }

    for (uint32_t w = 0; w < ways; w++) {
        uint32_t pos = w * numSets + (hf->hash(w, lineAddr) & setMask);
        uint32_t lineId = lookupArray[pos];
        if (array[lineId] != lineAddr)
        {
            rp->recordCandidate(lineId);
            n = n + 1;
            dfswalk(lineAddr, cnt, n);
        }
    }
}

uint32_t ZArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr) {
    rp->startReplacement(req);

    const int cnt = 20;
    int n = 0;
    dfswalk(lineAddr, cnt, n);
    uint32_t bestCandidate = rp->getBestCandidate();
    cands = n;

    //Write address of line we're replacing
    *wbLineAddr = array[bestCandidate];

    return bestCandidate;
}

void ZArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    int lookupLen = int(sizeof(lookupArray) - 1);
    int numC = 0;
    int flag = 0;
    while (numC < numLines*numSets) {
        for(uint32_t w = 0; w < ways; w++) {
            uint32_t hval = hf->hash(w, fringeAddr) & setMask;
            uint32_t pos = w * numSets + hval;
            if (lookupArray[pos] == candidate && pos != lookupLen) {
                uint32_t prev = candidate;
                for (uint32_t j = lookupLen; j >= pos; j--)
                {
                    uint32_t tmp = lookupArray[j];
                    lookupArray[j] = prev;
                    prev = tmp;
                }
                flag = 1;
                break;
            }
            numC += 1;
        }
        if (flag) {
            break;
        }
    }

    rp->replaced(candidate);
    array[candidate] = lineAddr;
    rp->update(candidate, req);
}

