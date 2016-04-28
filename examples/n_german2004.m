
const num_nodes: 3;		
const num_addr:  0;		
const num_data:  0;		


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
type data_type: array[num_data_type] of boolean;


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

type line_dir_type: array[node_id] of cache_state;

type node_bool_array: array[node_id] of boolean;

type home_request_type:
  record
    source: node_id;
    op:     opcode;
    data:   data_type;
    invalidate_list: node_bool_array;
    status: status_type;
  end;

type node_type:
  record
    memory:          array[addr_type] of data_type;
    cache:           array[addr_type] of cache_record;
    directory:       array[addr_type] of line_dir_type;
    local_requests:  array[addr_type] of boolean;
    home_requests:   array[addr_type] of home_request_type;
    remote_requests: array[addr_type] of addr_request_type;
    inchan:          array[channel_id] of message_buf_type;
    outchan:         array[channel_id] of message_buf_type;
  end;






var node: array[node_id] of node_type;

var auxdata: data_type;


startstate "Init"
begin
  clear node;
  clear auxdata;
endstartstate;









ruleset source: node_id; ch: channel_id; dest: node_id do
rule "Transfer message from `source' via `ch'"
    dest = node[source].outchan[ch].msg.dest &
    node[source].outchan[ch].valid
  & !node[dest].inchan[ch].valid  ==>
begin
  node[dest].inchan[ch].msg := node[source].outchan[ch].msg;
  node[dest].inchan[ch].valid := node[source].outchan[ch].valid;
  clear node[source].outchan[ch];
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
  clear node[client].inchan[channel2];
endrule;
endruleset;










ruleset client: node_id; addr: addr_type do
rule "`client' processes invalidate request for `addr'"
    node[client].remote_requests[addr].status = pending
  & node[client].remote_requests[addr].op = invalidate ==>
begin
    node[client].remote_requests[addr].data := node[client].cache[addr].data;
    clear node[client].cache[addr];
    node[client].remote_requests[addr].status := completed;
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
    node[client].outchan[channel3].msg.data   := node[client].remote_requests[addr].data;
    node[client].outchan[channel3].msg.addr   := addr;
    node[client].outchan[channel3].valid := true;
    clear node[client].remote_requests[addr];
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
      node[client].cache[addr].data  := node[client].inchan[channel2].msg.data;
      node[client].cache[addr].state := cache_shared;
    elsif node[client].inchan[channel2].msg.op = grant_upgrade then
      node[client].cache[addr].state := cache_exclusive;
    elsif node[client].inchan[channel2].msg.op = grant_exclusive then
      node[client].cache[addr].data  := node[client].inchan[channel2].msg.data;
      node[client].cache[addr].state := cache_exclusive;
    endif;
    node[client].local_requests[addr] := false;
    clear node[client].inchan[channel2];
endrule;
endruleset;












ruleset client: node_id; addr: addr_type; data: boolean do
rule "`client' stores data in cache for `addr'"
    node[client].remote_requests[addr].status != pending
  & node[client].cache[addr].state = cache_exclusive ==>
begin
    node[client].cache[addr].data[0]  := data;
    auxdata[0] := data;    
endrule;
endruleset;












ruleset home: node_id; addr: addr_type; source: node_id; channel1: channel_id do
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
    if node[home].cache[addr].state = cache_shared 
    then node[home].home_requests[addr].data := node[home].cache[addr].data;
    else  node[home].home_requests[addr].data   := node[home].memory[addr];
    endif;
    node[home].home_requests[addr].status := completed;
  elsif node[home].inchan[channel1].msg.op = read_shared  & node[home].directory[addr][home] = cache_invalid
      & !exists n:node_id do node[home].directory[addr][n] = cache_exclusive endexists then
    node[home].home_requests[addr].data   := node[home].memory[addr];
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
      node[home].home_requests[addr].data   := node[home].memory[addr];
      node[home].home_requests[addr].status := completed;
    endif;
  endif;
  clear node[home].inchan[channel1];
endrule;
endruleset;














ruleset home: node_id; addr: addr_type; dest: node_id; channel2: channel_id do
rule "`home' prepares invalidate for `addr'"
    channel2 = 2 &
    node[home].home_requests[addr].invalidate_list[dest] &
    node[home].home_requests[addr].status = pending
  & exists n:node_id do node[home].home_requests[addr].invalidate_list[n] endexists
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
    node[home].memory[addr] := node[home].inchan[channel3].msg.data;
  endif;
  node[home].home_requests[addr].data := node[home].inchan[channel3].msg.data;
  node[home].directory[addr][source] := cache_invalid;
  clear node[home].inchan[channel3];
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
  node[home].outchan[channel2].msg.data := node[home].home_requests[addr].data;
  node[home].outchan[channel2].msg.addr := addr;
  clear node[home].home_requests[addr];
  node[home].outchan[channel2].valid := true;
endrule;
endruleset;



