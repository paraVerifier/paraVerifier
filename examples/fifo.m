

const MSB: 63;	
const MSBA:  3;	
const LAST:  15;	 /* 2^(MSBA+1) - 1 */	

/**Address range. */ 
type value_type:     0..LAST;
type depth_type:     0..LAST;
type addr_type:      0..MSBA;
/* ------------------------------------------------------------------------ */
/* VARIABLES                                                                */
/* ------------------------------------------------------------------------ */

/**Global state of the system. 
var rst: boolean;
var push: boolean; 
var pop:boolean;*/

var tail: depth_type;
var empty: boolean;
var mem:array[depth_type] of value_type;
 

    
startstate "Init"
begin
  for i:depth_type do
	mem[i] := 0;
  endfor;
  tail := 0;
  empty := true;
endstartstate; 

ruleset dataIn: value_type; rst:boolean; push:boolean; pop:boolean do
rule "always"
  true ==>
begin
if (rst) then
   tail := 0;
   empty := true;
elsif (push & !(tail = LAST))   then   
	for i:depth_type do
	  mem[i] := (i=0)?dataIn : mem[i - 1]; 
	endfor;
	if empty then
	  tail := tail + 1;
	end;
	empty := false;
elsif (pop & !empty)  then
	if (tail = 0) then
		  empty := true;
	else
		  tail := tail - 1;
    endif;
endif;
endrule;
endruleset;
	
