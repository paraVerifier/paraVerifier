
const

  NODE_NUM : 4;
  DATA_NUM : 2;

type

  NODE : 1..NODE_NUM;

var

  a : boolean;
  b : boolean;
  c : array[NODE] of boolean;
  d : boolean;
  e : NODE;
  f : boolean;
  g : boolean;


ruleset p : NODE do
startstate "Init"
  a := true;
endstartstate;
endruleset;

ruleset src : NODE do
rule "NI_InvAck"
  a = true
==>
begin
    for p : NODE do
      if (p != src & c[p]) then
        e := p;
      else
        e := src;
      end;
    end;
endrule;
endruleset;


invariant "MemDataProp"
  !a;

















