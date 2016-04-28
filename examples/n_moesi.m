const num_clients: 3;

type client : 1..num_clients;
    locationType: enum{ M, OSTATUS, E, S, I}; 

var a : array[client] of locationType;

ruleset i : client do
rule "rule_t1"
    a[i] = E ==>
begin
    a[i] := M;
endrule;

rule "rule_t2"
    a[i] = I ==>
begin
    for j: client do
    if (j = i) then a[j] := S;
    elsif (a[j] = E) then a[j] := S;
    elsif (a[j] = M) then a[j] := OSTATUS;
    else a[j] := a[j];
    endif;
    endfor;
endrule;

rule "rul_t3"
    a[i] = S ==>
begin
    for j: client do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;

rule "rul_t4"
    a[i] = OSTATUS ==>
begin
    for j: client do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;

rule "rul_t5"
    a[i] = I ==>
begin
    for j: client do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;
endruleset;

startstate
begin
 for i: client do
    a[i] := I; 
  endfor; 
endstartstate;





