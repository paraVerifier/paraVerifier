
const
    NUM_NODE: 2;
    NUM_CACHE: 2;
    NUM_ADDR: 2;
    NUM_DATA: 2;
    NUM_LOCK: 2;

type
    TYPE_NODE: 1 .. NUM_NODE;
    TYPE_CACHE: 1 .. NUM_CACHE;
    TYPE_ADDR: 1 .. NUM_ADDR;
    TYPE_DATA: 1 .. NUM_DATA;
    TYPE_LOCK: 1 .. NUM_LOCK;
    
    CACHE_STATE: enum{INVALID, DIRTY, VALID};
    
    CACHE: record
        state: CACHE_STATE;
        addr: TYPE_ADDR;
        data: TYPE_DATA;
    end;
    
    MEMORY: record
        data: TYPE_DATA;
    end;
    
    LOCK: record
        owner: TYPE_NODE;
        beUsed: boolean;
        inProtection: array [TYPE_ADDR] of boolean;
    end;
    
    NODE: record
        cache: array [TYPE_CACHE] of CACHE;
        hasLock: boolean;
        firstRead: array [TYPE_ADDR] of boolean;
    end;
    
    REPLACE_STAGE: enum{NON, REQUIRE, REQREPALL, RANDOM, RANDINV, DESIGNATED, TOREP, DONE, REPALLDONE};
    
    REPLACE_RULE: enum{NONE, NLNCR, NLNCW, LNCFR, LCFR, LNCNFR};
    
var
    memory: array [TYPE_ADDR] of MEMORY;
    lock: array [TYPE_LOCK] of LOCK;
    node: array [TYPE_NODE] of NODE;
    curNode: TYPE_NODE;
    curCache: TYPE_CACHE;
    curMemory: TYPE_ADDR;
    curData: TYPE_DATA;
    curLock: TYPE_LOCK;
    replace: REPLACE_STAGE;
    repRule: REPLACE_RULE;
    
ruleset d: TYPE_DATA do
    startstate "Init"
        for i: TYPE_NODE do
            for j: TYPE_CACHE do
                node[i].cache[j].state := INVALID;
            endfor;
            node[i].hasLock := false;
            for a: TYPE_ADDR do
                node[i].firstRead[a] := true;
            endfor;
            curNode := i;
        endfor;
        for j: TYPE_CACHE do
            curCache := j;
        endfor;
        for a: TYPE_ADDR do
            memory[a].data := d;
            curMemory := a;
        endfor;
        curData := d;
        for l: TYPE_LOCK do
            lock[l].beUsed := false;
            curLock := l;
            for a: TYPE_ADDR do
                lock[l].inProtection[a] := false;
            endfor;
        endfor;
        replace := NON;
        repRule := NONE;
    endstartstate;
endruleset;

ruleset i: TYPE_NODE do
    rule "RI"
        replace = REQUIRE &
        i = curNode &
        exists j: TYPE_CACHE do
            node[i].cache[j].state = INVALID
        endexists
    ==>
    begin
        replace := RANDINV;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "CRIC"
        replace = RANDINV &
        i = curNode &
        node[i].cache[j].state = INVALID
    ==>
    begin
        curCache := j;
        replace := DONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE do
    rule "RNI"
        replace = REQUIRE &
        i = curNode &
        forall j: TYPE_CACHE do
            node[i].cache[j].state != INVALID
        endforall
    ==>
    begin
        replace := RANDOM;
    endrule;
endruleset;

ruleset i: TYPE_CACHE do
    rule "CRC"
        replace = RANDOM
    ==>
    begin
        curCache := i;
        replace := DESIGNATED;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "DCND"
        replace = DESIGNATED &
        i = curNode &
        j = curCache &
        node[i].cache[j].state != DIRTY
    ==>
    begin
        replace := DONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE do
    rule "DCD"
        replace = DESIGNATED &
        i = curNode &
        j = curCache &
        node[i].cache[j].state = DIRTY
    ==>
    begin
        replace := TOREP;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "Replace"
        replace = TOREP &
        i = curNode &
        j = curCache &
        a = node[i].cache[j].addr
    ==>
    begin
        memory[a].data := node[i].cache[j].data;
        node[i].cache[j].state := INVALID;
        replace := DONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "RepAll"
        replace = REQREPALL &
        node[i].cache[j].state = DIRTY &
        node[i].cache[j].addr = a
    ==>
    begin
        memory[a].data := node[i].cache[j].data;
        node[i].cache[j].state := INVALID;
    endrule;
endruleset;

rule "RepAllDone"
    replace = REQREPALL &
    forall i: TYPE_NODE; j: TYPE_CACHE do
        node[i].cache[j].state != DIRTY
    endforall
==>
begin
    replace := REPALLDONE;
endrule;

ruleset i: TYPE_NODE; a: TYPE_ADDR do
    rule "NLNCRR"
        replace = NON &
        !node[i].hasLock &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        replace := REQUIRE;
        repRule := NLNCR;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
    rule "NLNCRD"
        replace = DONE &
        repRule = NLNCR &
        i = curNode &
        j = curCache &
        a = curMemory
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLCW"
        replace = NON &
        !node[i].hasLock &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a &
        forall l: TYPE_LOCK do
            !lock[l].inProtection[a]
        endforall
    ==>
    begin
        node[i].cache[j].data := d;
        node[i].cache[j].state := DIRTY;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLNCWR"
        replace = NON &
        !node[i].hasLock &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall &
        forall l: TYPE_LOCK do
            !lock[l].inProtection[a]
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curData := d;
        replace := REQUIRE;
        repRule := NLNCW;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA do
    rule "NLNCWD"
        replace = DONE &
        repRule = NLNCW &
        i = curNode &
        j = curCache &
        a = curMemory &
        d = curData
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := d;
        node[i].cache[j].state := DIRTY;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LCFRRA"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i &
        node[i].firstRead[a] &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a
    ==>
    begin
        curNode := i;
        curCache := j;
        curMemory := a;
        curLock := l;
        replace := REQREPALL;
        repRule := LCFR;
    endrule;
endruleset;

rule "LCFRAD"
    replace = REPALLDONE &
    repRule = LCFR
==>
begin
    replace := DESIGNATED;
endrule;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LCFRD"
        replace = DONE &
        repRule = LCFR &
        i = curNode &
        j = curCache &
        a = curMemory &
        l = curLock
    ==>
    begin
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        node[i].firstRead[a] := false;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCFRRA"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i &
        node[i].firstRead[a] &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQREPALL;
        repRule := LNCFR;
    endrule;
endruleset;

rule "LNCFRAD"
    replace = REPALLDONE &
    repRule = LNCFR
==>
begin
    replace := REQUIRE;
endrule;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCFRD"
        replace = DONE &
        repRule = LNCFR &
        i = curNode &
        j = curCache &
        a = curMemory &
        l = curLock
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        node[i].firstRead[a] := false;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCNFRR"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i &
        !node[i].firstRead[a] &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall
    ==>
    begin
        curNode := i;
        curMemory := a;
        curLock := l;
        replace := REQUIRE;
        repRule := LNCNFR;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; l: TYPE_LOCK do
    rule "LNCNFRD"
        replace = DONE &
        repRule = LNCNFR &
        i = curNode &
        j = curCache &
        a = curMemory &
        l = curLock
    ==>
    begin
        node[i].cache[j].addr := a;
        node[i].cache[j].data := memory[a].data;
        node[i].cache[j].state := VALID;
        lock[l].inProtection[a] := true;
        replace := NON;
        repRule := NONE;
    endrule;
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR; d: TYPE_DATA; l: TYPE_LOCK do
    rule "LCW"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i &
        node[i].cache[j].state != INVALID &
        node[i].cache[j].addr = a &
        forall m: TYPE_LOCK do
            lock[m].inProtection[a] -> m = l
        endforall
    ==>
    begin
        memory[a].data := d;
        node[i].cache[j].data := d;
        node[i].cache[j].state := VALID;
        lock[l].inProtection[a] := true;
    endrule;
endruleset;

ruleset i: TYPE_NODE; a: TYPE_ADDR; d: TYPE_DATA; l: TYPE_LOCK do
    rule "LNCW"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i &
        forall j: TYPE_CACHE do
            node[i].cache[j].state = INVALID |
            node[i].cache[j].addr != a
        endforall &
        forall m: TYPE_LOCK do
            lock[m].inProtection[a] -> m = l
        endforall
    ==>
    begin
        memory[a].data := d;
        lock[l].inProtection[a] := true;
    endrule;
endruleset;

ruleset i: TYPE_NODE; l: TYPE_LOCK do
    rule "Acquire"
        replace = NON &
        !node[i].hasLock &
        !lock[l].beUsed
    ==>
    begin
        lock[l].beUsed := true;
        lock[l].owner := i;
        node[i].hasLock := true;
        for j: TYPE_ADDR do
            node[i].firstRead[j] := true;
        endfor;
    endrule;
    
    rule "Release"
        replace = NON &
        node[i].hasLock &
        lock[l].beUsed &
        lock[l].owner = i
    ==>
    begin
        lock[l].beUsed := false;
        node[i].hasLock := false;
        for a: TYPE_ADDR do
            lock[l].inProtection[a] := false;
        endfor;
    endrule;
endruleset;

ruleset i: TYPE_NODE do
invariant "DeadlockFree"
(
    replace = NON &
    node[i].hasLock
) -> (
    exists l: TYPE_LOCK do
        lock[l].beUsed &
        lock[l].owner = i
    endexists &
    forall m: TYPE_LOCK; n: TYPE_LOCK do
        m = n |
        !lock[m].beUsed |
        !lock[n].beUsed |
        lock[m].owner != i |
        lock[n].owner != i
    endforall
);
endruleset;

ruleset i: TYPE_NODE; j: TYPE_CACHE; a: TYPE_ADDR do
invariant "Coherence"
(
    replace = NON &
    node[i].hasLock &
    !node[i].firstRead[a] &
    node[i].cache[j].state = VALID &
    node[i].cache[j].addr = a
) -> 
node[i].cache[j].data = memory[a].data;
endruleset;



