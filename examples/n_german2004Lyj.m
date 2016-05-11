
const num_nodes: 3;
const num_addr:  1;
const num_data:  1;


type opcode: enum {
  op_invalid,
  read_shared,
  read_exclusive,
  req_upgrade,
  invalidate,
  invalidate_ack,
  grant_shared,
  grant_upgrade,
  grant_exclusive
};


type request_opcode: enum {
  req_read_shared,
  req_read_exclusive,
  req_req_upgrade
};


type cache_state: enum {
  cache_invalid,
  cache_shared,
  cache_exclusive
};


type addr_type: 0..num_addr;

type num_data_type: 0..num_data;

type data_type: 
  record
    values: array[num_data_type] of boolean;
  end;


type cache_record:
  record
    state: cache_state;
    data:  data_type;
  end;


type node_id: 0..num_nodes;


type channel_id: 1..3;


type message_type:
  record
    source: node_id;		
    dest:   node_id;		
    op:     opcode;		
    addr:   addr_type;		
    data:   data_type;		  
  end;


type message_buf_type:
  record
    msg:   message_type;
    valid: boolean;
  end;


type status_type: enum {
  inactive,
  pending,
  completed
};

type addr_request_type:
  record
    home:   node_id;
    op:     opcode;
    data:   data_type;
    status: status_type;
  end;

type home_request_type:
  record
    source: node_id;
    op:     opcode;
    data:   data_type;
    invalidate_list: array[node_id] of boolean;
    status: status_type;
  end;

type node_type:
  record
    memory:          array[addr_type] of data_type;
    cache:           array[addr_type] of cache_record;
    directory:       array[addr_type] of array[node_id] of cache_state;
    local_requests:  array[addr_type] of boolean;
    home_requests:   array[addr_type] of home_request_type;
    remote_requests: array[addr_type] of addr_request_type;
    inchan:          array[channel_id] of message_buf_type;
    outchan:         array[channel_id] of message_buf_type;
  end;






var
  node: array[node_id] of node_type;
  auxdata: array[addr_type] of data_type;


startstate "Init"
begin
  for i: node_id do
    for j: addr_type do
	  for k: num_data_type do
	    node[i].memory[j].values[k] := false;
	  endfor;
	  
	  node[i].cache[j].state := cache_invalid;
	  for k: num_data_type do
	    node[i].cache[j].data.values[k] := false;
	  endfor;
	  
	  for k: node_id do
	    node[i].directory[j][k] := cache_invalid;
	  endfor;
	  
	  node[i].local_requests[j] := false;
	  
	  node[i].home_requests[j].source := 0;
	  node[i].home_requests[j].op := op_invalid;
	  for k: num_data_type do
	    node[i].home_requests[j].data.values[k] := false;
	  endfor;
	  for k: node_id do
	    node[i].home_requests[j].invalidate_list[k] := false;
	  endfor;
	  node[i].home_requests[j].status := inactive;
	  
	  node[i].remote_requests[j].home := 0;
	  node[i].remote_requests[j].op := op_invalid;
	  for k: num_data_type do
	    node[i].remote_requests[j].data.values[k] := false;
	  endfor;
	  node[i].remote_requests[j].status := inactive;
	endfor;
	
	for j: channel_id do
	  node[i].inchan[j].msg.source := 0;
	  node[i].inchan[j].msg.dest := 0;
	  node[i].inchan[j].msg.op := op_invalid;
	  node[i].inchan[j].msg.addr := 0;
	  for k: num_data_type do
	    node[i].inchan[j].msg.data.values[k] := false;
	  endfor;
	  node[i].inchan[j].valid := false;
	  
	  node[i].outchan[j].msg.source := 0;
	  node[i].outchan[j].msg.dest := 0;
	  node[i].outchan[j].msg.op := op_invalid;
	  node[i].outchan[j].msg.addr := 0;
	  for k: num_data_type do
	    node[i].outchan[j].msg.data.values[k] := false;
	  endfor;
	  node[i].outchan[j].valid := false;
	endfor;
  endfor;
  for addr: addr_type; i: num_data_type do
    auxdata[addr].values[i] := false;
  endfor;
endstartstate;









ruleset source: node_id; ch: channel_id; dest: node_id do
rule "Transfer message from `source' via `ch'"
    dest = node[source].outchan[ch].msg.dest &
    node[source].outchan[ch].valid
  & !node[dest].inchan[ch].valid  ==>
begin
  node[dest].inchan[ch].msg.source := node[source].outchan[ch].msg.source;
  node[dest].inchan[ch].msg.dest := node[source].outchan[ch].msg.dest;
  node[dest].inchan[ch].msg.op := node[source].outchan[ch].msg.op;
  node[dest].inchan[ch].msg.addr := node[source].outchan[ch].msg.addr;
  for i: num_data_type do
    node[dest].inchan[ch].msg.data.values[i] := node[source].outchan[ch].msg.data.values[i];
  endfor;
  node[dest].inchan[ch].valid := node[source].outchan[ch].valid;

  node[source].outchan[ch].msg.source := 0;
  node[source].outchan[ch].msg.dest := 0;
  node[source].outchan[ch].msg.op := op_invalid;
  node[source].outchan[ch].msg.addr := 0;
  for k: num_data_type do
	node[source].outchan[ch].msg.data.values[k] := false;
  endfor;
  node[source].outchan[ch].valid := false;
endrule;
endruleset;










ruleset client: node_id; req: request_opcode; addr: addr_type; channel1: channel_id do
rule "`client' generates new `req' for `addr'"
    channel1 = 1 &
    !node[client].local_requests[addr]
  & ((req = req_read_shared    & node[client].cache[addr].state = cache_invalid) |
     (req = req_read_exclusive & node[client].cache[addr].state = cache_invalid) |
     (req = req_req_upgrade    & node[client].cache[addr].state = cache_shared))
  & !node[client].outchan[channel1].valid ==>
begin
    node[client].outchan[channel1].msg.source := client;
	if addr = 0 then
      node[client].outchan[channel1].msg.dest   := 0;
	else
      node[client].outchan[channel1].msg.dest   := 1;
	endif;
	if req = req_read_shared then
	  node[client].outchan[channel1].msg.op     := read_shared;
	elsif req = req_read_exclusive then
	  node[client].outchan[channel1].msg.op     := read_exclusive;
	else
	  node[client].outchan[channel1].msg.op     := req_upgrade;
	endif;
    node[client].outchan[channel1].msg.addr   := addr;
    node[client].outchan[channel1].valid := true;
    node[client].local_requests[addr] := true;
endrule;
endruleset;










ruleset client: node_id; addr: addr_type; channel2: channel_id do
rule "`client' accepts invalidate request"
    channel2 = 2 &
    addr = node[client].inchan[channel2].msg.addr
  & node[client].inchan[channel2].valid
  & node[client].inchan[channel2].msg.op = invalidate
  & node[client].remote_requests[addr].status = inactive ==>
begin
  node[client].remote_requests[addr].home   := node[client].inchan[channel2].msg.source;
  node[client].remote_requests[addr].op     := node[client].inchan[channel2].msg.op ;
  node[client].remote_requests[addr].status := pending;
  
  node[client].inchan[channel2].msg.source := 0;
  node[client].inchan[channel2].msg.dest := 0;
  node[client].inchan[channel2].msg.op := op_invalid;
  node[client].inchan[channel2].msg.addr := 0;
  for k: num_data_type do
	node[client].inchan[channel2].msg.data.values[k] := false;
  endfor;
  node[client].inchan[channel2].valid := false;
endrule;
endruleset;










ruleset client: node_id; addr: addr_type do
rule "`client' processes invalidate request for `addr'"
    node[client].remote_requests[addr].status = pending
  & node[client].remote_requests[addr].op = invalidate ==>
begin
    for i : num_data_type do
      node[client].remote_requests[addr].data.values[i] := node[client].cache[addr].data.values[i];
	endfor;
    node[client].remote_requests[addr].status := completed;

	  node[client].cache[addr].state := cache_invalid;
	  for k: num_data_type do
		node[client].cache[addr].data.values[k] := false;
	  endfor;
endrule;
endruleset;












ruleset client: node_id; addr: addr_type; channel3: channel_id do
rule "`client' prepares invalidate ack for `addr'"
    channel3 = 3 &
    node[client].remote_requests[addr].status = completed
  & node[client].remote_requests[addr].op = invalidate
  & !node[client].outchan[channel3].valid ==>
begin
    node[client].outchan[channel3].msg.op     := invalidate_ack;
    node[client].outchan[channel3].msg.source := client;
    node[client].outchan[channel3].msg.dest   := node[client].remote_requests[addr].home;
	for i: num_data_type do
      node[client].outchan[channel3].msg.data.values[i]   := node[client].remote_requests[addr].data.values[i];
	endfor;
    node[client].outchan[channel3].msg.addr   := addr;
    node[client].outchan[channel3].valid := true;
		  
	  node[client].remote_requests[addr].home := 0;
	  node[client].remote_requests[addr].op := op_invalid;
	  for k: num_data_type do
	    node[client].remote_requests[addr].data.values[k] := false;
	  endfor;
	  node[client].remote_requests[addr].status := inactive;
endrule;
endruleset;













ruleset client: node_id; addr: addr_type; channel2: channel_id do
rule "`client' receives reply from home"
    channel2 = 2 &
    addr = node[client].inchan[channel2].msg.addr
  & node[client].inchan[channel2].valid
  & (node[client].inchan[channel2].msg.op = grant_shared |
     node[client].inchan[channel2].msg.op = grant_upgrade | 
	 node[client].inchan[channel2].msg.op = grant_exclusive) ==>
begin
    if node[client].inchan[channel2].msg.op = grant_shared then
	  for i: num_data_type do
        node[client].cache[addr].data.values[i]  := node[client].inchan[channel2].msg.data.values[i];
	  endfor;
      node[client].cache[addr].state := cache_shared;
    elsif node[client].inchan[channel2].msg.op = grant_upgrade then
      node[client].cache[addr].state := cache_exclusive;
    elsif node[client].inchan[channel2].msg.op = grant_exclusive then
	  for i: num_data_type do
        node[client].cache[addr].data.values[i]  := node[client].inchan[channel2].msg.data.values[i];
	  endfor;
      node[client].cache[addr].state := cache_exclusive;
    endif;
    node[client].local_requests[addr] := false;
	
	  node[client].inchan[channel2].msg.source := 0;
	  node[client].inchan[channel2].msg.dest := 0;
	  node[client].inchan[channel2].msg.op := op_invalid;
	  node[client].inchan[channel2].msg.addr := 0;
	  for k: num_data_type do
	    node[client].inchan[channel2].msg.data.values[k] := false;
	  endfor;
	  node[client].inchan[channel2].valid := false;
endrule;
endruleset;












ruleset client: node_id; addr: addr_type; data: boolean; data_n: num_data_type do
rule "`client' stores data in cache for `addr'"
    node[client].remote_requests[addr].status != pending
  & node[client].cache[addr].state = cache_exclusive ==>
begin
    node[client].cache[addr].data.values[data_n]  := data;
    auxdata[addr].values[data_n] := data;    
endrule;
endruleset;







ruleset home: node_id; addr: addr_type; source: node_id; channel1: channel_id do

rule "`home' accepts a request message_req_upgradeitseNotlInv__forall_cache_invalid "
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive
    & node[home].inchan[channel1].msg.op = req_upgrade 
    & !(node[home].directory[addr][source] = cache_invalid) 
    & (forall n: node_id do 
       (n=source | node[home].directory[addr][n] = cache_invalid) endforall) ==>
begin
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := req_upgrade;
    
    for n: node_id do
      if node[home].directory[addr][n] != cache_invalid & n != source then
        node[home].home_requests[addr].invalidate_list[n] := true;
	  else
        node[home].home_requests[addr].invalidate_list[n] := false;
	  endif;
    endfor;


    for i: num_data_type do
        node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
      node[home].home_requests[addr].status := completed;
    
    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false; 

endrule;

rule "`home' accepts a request message_req_upgradeitsefInv__forall_cache_invalid "
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive
    & node[home].inchan[channel1].msg.op = req_upgrade 
    & (node[home].directory[addr][source] = cache_invalid) 
    & (forall n: node_id do 
       ( node[home].directory[addr][n] = cache_invalid) endforall) ==>
begin
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := read_exclusive;
    
    for n: node_id do
      if node[home].directory[addr][n] != cache_invalid & n != source then
        node[home].home_requests[addr].invalidate_list[n] := true;
	  else
        node[home].home_requests[addr].invalidate_list[n] := false;
	  endif;
    endfor;


    for i: num_data_type do
        node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
      node[home].home_requests[addr].status := completed;

    
    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false; 

endrule;

rule "`home' accepts a request message read_exclusive_forall_cache_invalid" 

    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive&
    node[home].inchan[channel1].msg.op = read_exclusive & 
   (forall n:node_id do (node[home].directory[addr][n] = cache_invalid ) endforall) ==>
begin
  
  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := read_exclusive;

    for s: node_id do
      if node[home].directory[addr][s] != cache_invalid then
        node[home].home_requests[addr].invalidate_list[s] := true;
    else
        node[home].home_requests[addr].invalidate_list[s] := false;
    endif;
    endfor; 

    for i: num_data_type do
        node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
      node[home].home_requests[addr].status := completed;

    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;

endrule;

rule "`home' accepts a request message read_shared home_cache_invalid-home_shared" 
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive
    & node[home].inchan[channel1].msg.op = read_shared & node[home].directory[addr][home] = cache_shared 
    ==>
begin    
  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := read_shared;
  
 
    if node[home].cache[addr].state = cache_shared then
	  for i: num_data_type do
	    node[home].home_requests[addr].data.values[i] := node[home].cache[addr].data.values[i];
	  endfor;
    else
	  for i: num_data_type do
	    node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
    endif;
    
    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule; 

rule "`home' accepts a request message read_shared home_cache_invalid-forall_not_exclusive" 
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive
    & node[home].inchan[channel1].msg.op = read_shared & 
    node[home].directory[addr][home] = cache_invalid &
    (forall n:node_id do  !(node[home].directory[addr][n] = cache_exclusive) endforall)  ==>
begin

    
  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := read_shared;
  
  for i: num_data_type do
      node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	endfor;
    node[home].home_requests[addr].status := completed;

    
    
  node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule; 



endruleset;

 

 

ruleset home: node_id; addr: addr_type; source: node_id; n: node_id; channel1: channel_id do

rule "`home' accepts a request message_req_upgrade_itselfNotInv_exits_one_not_cache_invalid "
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive &
    node[home].inchan[channel1].msg.op = req_upgrade  
    & !(node[home].directory[addr][source] = cache_invalid) 
    & (!(source=n))
    & (!(node[home].directory[addr][n] = cache_invalid ))  ==>
   
    
begin

    

    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := req_upgrade;

    for s: node_id do
    if node[home].directory[addr][s] != cache_invalid & s != source then
        node[home].home_requests[addr].invalidate_list[s] := true;
    else
        node[home].home_requests[addr].invalidate_list[s] := false;
    endif;
    endfor;

    node[home].home_requests[addr].status := pending;

   node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule;


rule "`home' accepts a request message_req_upgrade_itselfInv_exits_one_not_cache_invalid "
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive&
    node[home].inchan[channel1].msg.op = req_upgrade  
    & (node[home].directory[addr][source] = cache_invalid) 
    & (!(source=n))
    & (!(node[home].directory[addr][n] = cache_invalid ))    ==>
    
begin   
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := read_exclusive;
    for s: node_id do
    if node[home].directory[addr][s] != cache_invalid & s != source then
        node[home].home_requests[addr].invalidate_list[s] := true;
    else
        node[home].home_requests[addr].invalidate_list[s] := false;
    endif;
    endfor;

    node[home].home_requests[addr].status := pending;

   node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule;

rule "`home' accepts a request message read_exclusive_exits_one_not_cache_invalid" 
     channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive &
    node[home].inchan[channel1].msg.op = read_exclusive 
    & (!(node[home].directory[addr][n] = cache_invalid ))   ==>

begin
  
  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := read_exclusive;

    for s: node_id do
      if node[home].directory[addr][s] != cache_invalid then
        node[home].home_requests[addr].invalidate_list[s] := true;
    else
        node[home].home_requests[addr].invalidate_list[s] := false;
    endif;
    endfor;
    
     

    node[home].home_requests[addr].status := pending;

    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule; 

 
 

 

rule "`home' accepts a request message read_shared_home_invalid_exits_one_exclusive" 

    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
  	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
    & node[home].home_requests[addr].status = inactive&
    node[home].inchan[channel1].msg.op =read_shared &node[home].directory[addr][n] = cache_exclusive
    ==>
begin

  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := read_shared;
  
    for s: node_id do
    if node[home].directory[addr][s] != cache_invalid then
        node[home].home_requests[addr].invalidate_list[s] := true;
    else
        node[home].home_requests[addr].invalidate_list[s] := false;
    endif;
    endfor;
  
    node[home].home_requests[addr].status := pending;
    
   

    node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule;
endruleset;


/*ruleset home: node_id; addr: addr_type; source: node_id; channel1: channel_id do
rule "`home' accepts a request message"
    channel1 = 1 &
    addr = node[home].inchan[channel1].msg.addr &
	source = node[home].inchan[channel1].msg.source &
    node[home].inchan[channel1].valid
  & node[home].home_requests[addr].status = inactive ==>
begin
  if node[home].inchan[channel1].msg.op = req_upgrade & node[home].directory[addr][source] = cache_invalid then
    node[home].inchan[channel1].msg.op := read_exclusive;
  endif;
  node[home].home_requests[addr].source := source;
  node[home].home_requests[addr].op := node[home].inchan[channel1].msg.op;
  if node[home].inchan[channel1].msg.op = read_shared & node[home].directory[addr][home] = cache_shared 
  then
    if node[home].cache[addr].state = cache_shared then
	  for i: num_data_type do
	    node[home].home_requests[addr].data.values[i] := node[home].cache[addr].data.values[i];
	  endfor;
    else
	  for i: num_data_type do
	    node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
    endif;
    node[home].home_requests[addr].status := completed;
  elsif node[home].inchan[channel1].msg.op = read_shared  & node[home].directory[addr][home] = cache_invalid
      & !exists n:node_id do node[home].directory[addr][n] = cache_exclusive endexists then
	for i: num_data_type do
      node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	endfor;
    node[home].home_requests[addr].status := completed;
  elsif node[home].inchan[channel1].msg.op = read_shared &
	exists n:node_id do node[home].directory[addr][n] = cache_exclusive endexists then
    for n:node_id do
	  if node[home].directory[addr][n] != cache_invalid then
        node[home].home_requests[addr].invalidate_list[n] := true;
	  else
        node[home].home_requests[addr].invalidate_list[n] := false;
	  endif;
    endfor;
    node[home].home_requests[addr].status := pending;
  elsif (node[home].inchan[channel1].msg.op = req_upgrade) then
    for n: node_id do
      if node[home].directory[addr][n] != cache_invalid & n != source then
        node[home].home_requests[addr].invalidate_list[n] := true;
	  else
        node[home].home_requests[addr].invalidate_list[n] := false;
	  endif;
    endfor;
    if exists n: node_id do
	  node[home].directory[addr][n] != cache_invalid & n != source
	endexists then
      node[home].home_requests[addr].status := pending;
    else
      node[home].home_requests[addr].status := completed;
    endif;
  elsif (node[home].inchan[channel1].msg.op = read_exclusive) then
    for n: node_id do
      if node[home].directory[addr][n] != cache_invalid then
        node[home].home_requests[addr].invalidate_list[n] := true;
	  else
        node[home].home_requests[addr].invalidate_list[n] := false;
	  endif;
    endfor;
    if exists n: node_id do
	  node[home].directory[addr][n] != cache_invalid
	endexists then
      node[home].home_requests[addr].status := pending;
    else
	  for i: num_data_type do
        node[home].home_requests[addr].data.values[i]   := node[home].memory[addr].values[i];
	  endfor;
      node[home].home_requests[addr].status := completed;
    endif;
  endif;
  
	  node[home].inchan[channel1].msg.source := 0;
	  node[home].inchan[channel1].msg.dest := 0;
	  node[home].inchan[channel1].msg.op := op_invalid;
	  node[home].inchan[channel1].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel1].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel1].valid := false;
endrule;
endruleset;*/














ruleset home: node_id; addr: addr_type; dest: node_id; channel2: channel_id; n:node_id do
rule "`home' prepares invalidate for `addr'"
    channel2 = 2 &
    node[home].home_requests[addr].invalidate_list[dest] &
    node[home].home_requests[addr].status = pending
  & node[home].home_requests[addr].invalidate_list[n]
  & !node[home].outchan[channel2].valid  ==>
begin
  node[home].outchan[channel2].msg.addr   := addr;
  node[home].outchan[channel2].msg.op     := invalidate;
  node[home].outchan[channel2].msg.source := home;
  node[home].outchan[channel2].msg.dest   := dest;
  node[home].outchan[channel2].valid := true;
  node[home].home_requests[addr].invalidate_list[dest] := false;
endrule;
endruleset;










ruleset home: node_id; addr: addr_type; source: node_id; channel3: channel_id do
rule "`home' processes invalidate ack"
    channel3 = 3 &
    addr = node[home].inchan[channel3].msg.addr &
	source = node[home].inchan[channel3].msg.source &
    node[home].inchan[channel3].valid
  & node[home].home_requests[addr].status = pending
  & node[home].inchan[channel3].msg.op = invalidate_ack ==>
begin
  if node[home].directory[addr][source] = cache_exclusive then
	for i: num_data_type do
      node[home].memory[addr].values[i] := node[home].inchan[channel3].msg.data.values[i];
	endfor;
  endif;
  for i: num_data_type do
    node[home].home_requests[addr].data.values[i] := node[home].inchan[channel3].msg.data.values[i];
  endfor;
  node[home].directory[addr][source] := cache_invalid;
	if node[home].home_requests[addr].op = read_shared then
	  node[home].home_requests[addr].status := completed;
	elsif node[home].home_requests[addr].op = req_upgrade then
	  if forall n: node_id do
		n != node[home].home_requests[addr].source -> node[home].directory[addr][n] = cache_invalid endforall then
		node[home].home_requests[addr].status := completed;
	  endif;
	elsif node[home].home_requests[addr].op = read_exclusive then
	  if forall n: node_id do node[home].directory[addr][n] = cache_invalid endforall then
		node[home].home_requests[addr].status := completed;
	  endif;
    endif;
	
	  node[home].inchan[channel3].msg.source := 0;
	  node[home].inchan[channel3].msg.dest := 0;
	  node[home].inchan[channel3].msg.op := op_invalid;
	  node[home].inchan[channel3].msg.addr := 0;
	  for k: num_data_type do
	    node[home].inchan[channel3].msg.data.values[k] := false;
	  endfor;
	  node[home].inchan[channel3].valid := false;
endrule;
endruleset;









ruleset home: node_id; addr: addr_type; source: node_id; channel2: channel_id do
rule "`home' sends grant for `addr'"
    channel2 = 2 &
    source = node[home].home_requests[addr].source &
    node[home].home_requests[addr].status = completed
  & !node[home].outchan[channel2].valid ==>
begin
  node[home].outchan[channel2].msg.source := home;
  node[home].outchan[channel2].msg.dest   := node[home].home_requests[addr].source;
  if node[home].home_requests[addr].op = read_shared then
    node[home].outchan[channel2].msg.op := grant_shared;
    node[home].directory[addr][source] := cache_shared;
  elsif node[home].home_requests[addr].op = req_upgrade then
    node[home].outchan[channel2].msg.op := grant_upgrade;
    node[home].directory[addr][source] := cache_exclusive;
  elsif node[home].home_requests[addr].op = read_exclusive then
    node[home].outchan[channel2].msg.op := grant_exclusive;
    node[home].directory[addr][source] := cache_exclusive;
  endif;
  for i: num_data_type do
    node[home].outchan[channel2].msg.data.values[i] := node[home].home_requests[addr].data.values[i];
  endfor;
  node[home].outchan[channel2].msg.addr := addr;
  node[home].outchan[channel2].valid := true;
  
	  node[home].home_requests[addr].source := 0;
	  node[home].home_requests[addr].op := op_invalid;
	  for k: num_data_type do
	    node[home].home_requests[addr].data.values[k] := false;
	  endfor;
	  for k: node_id do
	    node[home].home_requests[addr].invalidate_list[k] := false;
	  endfor;
	  node[home].home_requests[addr].status := inactive;
endrule;
endruleset;





