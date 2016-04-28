const clientNUMS : 3;
type location: enum{ M, E, S, I};

     client: 1 .. clientNUMS;

var state : array [client] of location;
  
    
ruleset i : client do
rule "t1" state[i] = E ==>
begin
      state[i] := M; endrule; 

      
rule "t2"
      state[i] = I ==>
begin
      for j: client do
      if (j=i) then state[j]:=S;
      elsif (state[j]=E) then state[j]:=S;
      elsif (state[j]=M)  then state[j]:=S;
      elsif (state[j]=I) then state[j]:=I;
      else   state[j]:=S;
      endif;
      endfor; endrule;
          

rule "t3"
      state[i] = S ==>
begin
      for j: client do
      if (j=i) then state[j]:=E ;
      else   state[j]:=I;
      endif;
      endfor; endrule;
      

rule "t4"
      state[i] = I ==>
begin
      for j: client do
      if (j=i) then state[j]:=E ;
      else   state[j]:=I;
      endif;
      endfor; endrule;
endruleset;

startstate
begin
 for i: client do
    state[i] := I; 
  endfor; 
endstartstate;


