const clientNum : 3;

type channelType: enum{epsilon, req_shared, req_exclusive };
    cacheType: enum{invalid, shared, exclusive };
    client: 1 .. clientNum;
    
var home_exclusive_granted: boolean;
    home_current_command: channelType;
    home_current_client: client;
    cache: array[client] of cacheType;
    home_sharer_list: array[client] of boolean;

ruleset i : client do
rule "t1"
    home_current_command = epsilon & cache[i] = invalid ==>
    begin 
        home_current_command := req_shared;
        home_current_client := i;
    endrule;
    
rule "t2"
    home_current_command = epsilon & cache[i] != exclusive ==>
    begin
        home_current_command := req_exclusive;
        home_current_client := i;
    endrule;

rule "t3"
    home_sharer_list[i] & home_current_command = req_exclusive ==>
    begin 
        home_exclusive_granted := false;
        cache[i] := invalid;
        home_sharer_list[i] := false;
    endrule;
    
rule "t4"
    home_sharer_list[i] & home_current_command = req_shared & home_exclusive_granted ==>
    begin
        home_exclusive_granted := false;
        cache[i] := shared;
        home_sharer_list[i] := true;
    endrule;
    
rule "t5"
    home_current_client = i & home_current_command = req_shared & !home_exclusive_granted ==>
    begin
        home_current_command := epsilon;
        home_sharer_list[i] := true;
        cache[i] := shared;
    endrule;
    
rule "t6"
    home_current_command = req_exclusive & !home_exclusive_granted
    & home_current_client = i & forall c : client do home_sharer_list[c] = false endforall ==>
    begin
        home_current_command := epsilon;
        home_exclusive_granted := true;
        home_sharer_list[i] := true;
        cache[i] := exclusive;
    endrule;
endruleset;

ruleset j:client do
startstate
begin
    for i :client do
        cache[i] := invalid;
        home_sharer_list[i] := false;
    endfor;
    home_current_client := j;
    home_current_command := epsilon;
    home_exclusive_granted := false;
endstartstate;
endruleset;





