type
  opcode : enum{op_invalid, read_shared, read_exclusive, req_upgrade, invalidate, invalidate_ack, grant_shared, grant_upgrade, grant_exclusive};
  request_opcode : enum{req_read_shared, req_read_exclusive, req_req_upgrade};
  cache_state : enum{cache_invalid, cache_shared, cache_exclusive};
  status_type : enum{inactive, pending, completed};
  addr_type : 1..2;
  num_data_type : 1..1;
  node_id : 0..3;
  channel_id : 1..3;



record_0 : record
values : array [num_data_type] of boolean;
end;


record_1 : record
data :  record_0;
addr :  addr_type;
op :  opcode;
dest :  node_id;
source :  node_id;
end;


record_2 : record
valid :  boolean;
msg :  record_1;
end;


record_3 : record
status :  status_type;
data :  record_0;
op :  opcode;
home :  node_id;
end;


record_4 : record
status :  status_type;
invalidate_list : array [node_id] of boolean;
data :  record_0;
op :  opcode;
source :  node_id;
end;


record_5 : record
data :  record_0;
state :  cache_state;
end;


record_6 : record
outchan_3 :  record_2;
outchan_2 :  record_2;
outchan_1 :  record_2;
inchan_3 :  record_2;
inchan_2 :  record_2;
inchan_1 :  record_2;
remote_requests : array [addr_type] of record_3;
home_requests : array [addr_type] of record_4;
local_requests : array [addr_type] of boolean;
directory : array [addr_type] of array [node_id] of cache_state;
cache : array [addr_type] of record_5;
memory : array [addr_type] of record_0;
end;


var
auxdata : array [addr_type] of record_0;
node : array [node_id] of record_6;


startstate
begin
  for i : node_id do
    for j : addr_type do
      for k : num_data_type do
        node[i].memory[j].values[k] := false;
      endfor;
      node[i].cache[j].state := cache_invalid;
      for k : num_data_type do
        node[i].cache[j].data.values[k] := false;
      endfor;
      for k : node_id do
        node[i].directory[j][k] := cache_invalid;
      endfor;
      node[i].local_requests[j] := false;
      node[i].home_requests[j].source := 0;
      node[i].home_requests[j].op := op_invalid;
      for k : num_data_type do
        node[i].home_requests[j].data.values[k] := false;
      endfor;
      for k : node_id do
        node[i].home_requests[j].invalidate_list[k] := false;
      endfor;
      node[i].home_requests[j].status := inactive;
      node[i].remote_requests[j].home := 0;
      node[i].remote_requests[j].op := op_invalid;
      for k : num_data_type do
        node[i].remote_requests[j].data.values[k] := false;
      endfor;
      node[i].remote_requests[j].status := inactive;
    endfor;
    node[i].inchan_1.msg.source := 0;
    node[i].inchan_1.msg.dest := 0;
    node[i].inchan_1.msg.op := op_invalid;
    node[i].inchan_1.msg.addr := 1;
    for k : num_data_type do
      node[i].inchan_1.msg.data.values[k] := false;
    endfor;
    node[i].inchan_1.valid := false;
    node[i].outchan_1.msg.source := 0;
    node[i].outchan_1.msg.dest := 0;
    node[i].outchan_1.msg.op := op_invalid;
    node[i].outchan_1.msg.addr := 1;
    for k : num_data_type do
      node[i].outchan_1.msg.data.values[k] := false;
    endfor;
    node[i].outchan_1.valid := false;
    node[i].inchan_2.msg.source := 0;
    node[i].inchan_2.msg.dest := 0;
    node[i].inchan_2.msg.op := op_invalid;
    node[i].inchan_2.msg.addr := 1;
    for k : num_data_type do
      node[i].inchan_2.msg.data.values[k] := false;
    endfor;
    node[i].inchan_2.valid := false;
    node[i].outchan_2.msg.source := 0;
    node[i].outchan_2.msg.dest := 0;
    node[i].outchan_2.msg.op := op_invalid;
    node[i].outchan_2.msg.addr := 1;
    for k : num_data_type do
      node[i].outchan_2.msg.data.values[k] := false;
    endfor;
    node[i].outchan_2.valid := false;
    node[i].inchan_3.msg.source := 0;
    node[i].inchan_3.msg.dest := 0;
    node[i].inchan_3.msg.op := op_invalid;
    node[i].inchan_3.msg.addr := 1;
    for k : num_data_type do
      node[i].inchan_3.msg.data.values[k] := false;
    endfor;
    node[i].inchan_3.valid := false;
    node[i].outchan_3.msg.source := 0;
    node[i].outchan_3.msg.dest := 0;
    node[i].outchan_3.msg.op := op_invalid;
    node[i].outchan_3.msg.addr := 1;
    for k : num_data_type do
      node[i].outchan_3.msg.data.values[k] := false;
    endfor;
    node[i].outchan_3.valid := false;
  endfor;
  for i : addr_type do
    for j : num_data_type do
      auxdata[i].values[j] := false;
    endfor;
  endfor;
endstartstate;


ruleset source : node_id; dest : node_id do
  rule "n_Transfer_message_from_source_via_ch_ch1"
    (((dest = node[source].outchan_1.msg.dest) & (node[source].outchan_1.valid = true)) & (node[dest].inchan_1.valid = false)) ==>
  begin
    node[dest].inchan_1.msg.source := node[source].outchan_1.msg.source;
    node[dest].inchan_1.msg.dest := node[source].outchan_1.msg.dest;
    node[dest].inchan_1.msg.op := node[source].outchan_1.msg.op;
    node[dest].inchan_1.msg.addr := node[source].outchan_1.msg.addr;
    for i : num_data_type do
      node[dest].inchan_1.msg.data.values[i] := node[source].outchan_1.msg.data.values[i];
    endfor;
    node[dest].inchan_1.valid := node[source].outchan_1.valid;
    node[source].outchan_1.msg.source := 0;
    node[source].outchan_1.msg.dest := 0;
    node[source].outchan_1.msg.op := op_invalid;
    node[source].outchan_1.msg.addr := 1;
    for k : num_data_type do
      node[source].outchan_1.msg.data.values[k] := false;
    endfor;
    node[source].outchan_1.valid := false;
  endrule;
endruleset;


ruleset source : node_id; dest : node_id do
  rule "n_Transfer_message_from_source_via_ch_ch2"
    (((dest = node[source].outchan_2.msg.dest) & (node[source].outchan_2.valid = true)) & (node[dest].inchan_2.valid = false)) ==>
  begin
    node[dest].inchan_2.msg.source := node[source].outchan_2.msg.source;
    node[dest].inchan_2.msg.dest := node[source].outchan_2.msg.dest;
    node[dest].inchan_2.msg.op := node[source].outchan_2.msg.op;
    node[dest].inchan_2.msg.addr := node[source].outchan_2.msg.addr;
    for i : num_data_type do
      node[dest].inchan_2.msg.data.values[i] := node[source].outchan_2.msg.data.values[i];
    endfor;
    node[dest].inchan_2.valid := node[source].outchan_2.valid;
    node[source].outchan_2.msg.source := 0;
    node[source].outchan_2.msg.dest := 0;
    node[source].outchan_2.msg.op := op_invalid;
    node[source].outchan_2.msg.addr := 1;
    for k : num_data_type do
      node[source].outchan_2.msg.data.values[k] := false;
    endfor;
    node[source].outchan_2.valid := false;
  endrule;
endruleset;


ruleset source : node_id; dest : node_id do
  rule "n_Transfer_message_from_source_via_ch_ch3"
    (((dest = node[source].outchan_3.msg.dest) & (node[source].outchan_3.valid = true)) & (node[dest].inchan_3.valid = false)) ==>
  begin
    node[dest].inchan_3.msg.source := node[source].outchan_3.msg.source;
    node[dest].inchan_3.msg.dest := node[source].outchan_3.msg.dest;
    node[dest].inchan_3.msg.op := node[source].outchan_3.msg.op;
    node[dest].inchan_3.msg.addr := node[source].outchan_3.msg.addr;
    for i : num_data_type do
      node[dest].inchan_3.msg.data.values[i] := node[source].outchan_3.msg.data.values[i];
    endfor;
    node[dest].inchan_3.valid := node[source].outchan_3.valid;
    node[source].outchan_3.msg.source := 0;
    node[source].outchan_3.msg.dest := 0;
    node[source].outchan_3.msg.op := op_invalid;
    node[source].outchan_3.msg.addr := 1;
    for k : num_data_type do
      node[source].outchan_3.msg.data.values[k] := false;
    endfor;
    node[source].outchan_3.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_shared_channel11"
    ((((1 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_shared = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_shared = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_shared = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_1.valid = false)) ==>
  begin
    node[client].outchan_1.msg.source := client;
    node[client].outchan_1.msg.dest := 0;
    if (req_read_shared = req_read_shared) then
      node[client].outchan_1.msg.op := read_shared;
else
      if (req_read_shared = req_read_exclusive) then
        node[client].outchan_1.msg.op := read_exclusive;
else
        node[client].outchan_1.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_1.msg.addr := addr;
    node[client].outchan_1.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_exclusive_channel11"
    ((((1 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_exclusive = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_exclusive = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_exclusive = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_1.valid = false)) ==>
  begin
    node[client].outchan_1.msg.source := client;
    node[client].outchan_1.msg.dest := 0;
    if (req_read_exclusive = req_read_shared) then
      node[client].outchan_1.msg.op := read_shared;
else
      if (req_read_exclusive = req_read_exclusive) then
        node[client].outchan_1.msg.op := read_exclusive;
else
        node[client].outchan_1.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_1.msg.addr := addr;
    node[client].outchan_1.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_req_upgrade_channel11"
    ((((1 = 1) & (node[client].local_requests[addr] = false)) & ((((req_req_upgrade = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_req_upgrade = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_req_upgrade = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_1.valid = false)) ==>
  begin
    node[client].outchan_1.msg.source := client;
    node[client].outchan_1.msg.dest := 0;
    if (req_req_upgrade = req_read_shared) then
      node[client].outchan_1.msg.op := read_shared;
else
      if (req_req_upgrade = req_read_exclusive) then
        node[client].outchan_1.msg.op := read_exclusive;
else
        node[client].outchan_1.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_1.msg.addr := addr;
    node[client].outchan_1.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_shared_channel12"
    ((((2 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_shared = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_shared = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_shared = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_2.valid = false)) ==>
  begin
    node[client].outchan_2.msg.source := client;
    node[client].outchan_2.msg.dest := 0;
    if (req_read_shared = req_read_shared) then
      node[client].outchan_2.msg.op := read_shared;
else
      if (req_read_shared = req_read_exclusive) then
        node[client].outchan_2.msg.op := read_exclusive;
else
        node[client].outchan_2.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_2.msg.addr := addr;
    node[client].outchan_2.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_exclusive_channel12"
    ((((2 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_exclusive = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_exclusive = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_exclusive = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_2.valid = false)) ==>
  begin
    node[client].outchan_2.msg.source := client;
    node[client].outchan_2.msg.dest := 0;
    if (req_read_exclusive = req_read_shared) then
      node[client].outchan_2.msg.op := read_shared;
else
      if (req_read_exclusive = req_read_exclusive) then
        node[client].outchan_2.msg.op := read_exclusive;
else
        node[client].outchan_2.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_2.msg.addr := addr;
    node[client].outchan_2.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_req_upgrade_channel12"
    ((((2 = 1) & (node[client].local_requests[addr] = false)) & ((((req_req_upgrade = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_req_upgrade = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_req_upgrade = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_2.valid = false)) ==>
  begin
    node[client].outchan_2.msg.source := client;
    node[client].outchan_2.msg.dest := 0;
    if (req_req_upgrade = req_read_shared) then
      node[client].outchan_2.msg.op := read_shared;
else
      if (req_req_upgrade = req_read_exclusive) then
        node[client].outchan_2.msg.op := read_exclusive;
else
        node[client].outchan_2.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_2.msg.addr := addr;
    node[client].outchan_2.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_shared_channel13"
    ((((3 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_shared = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_shared = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_shared = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_3.valid = false)) ==>
  begin
    node[client].outchan_3.msg.source := client;
    node[client].outchan_3.msg.dest := 0;
    if (req_read_shared = req_read_shared) then
      node[client].outchan_3.msg.op := read_shared;
else
      if (req_read_shared = req_read_exclusive) then
        node[client].outchan_3.msg.op := read_exclusive;
else
        node[client].outchan_3.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_3.msg.addr := addr;
    node[client].outchan_3.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_read_exclusive_channel13"
    ((((3 = 1) & (node[client].local_requests[addr] = false)) & ((((req_read_exclusive = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_read_exclusive = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_read_exclusive = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_3.valid = false)) ==>
  begin
    node[client].outchan_3.msg.source := client;
    node[client].outchan_3.msg.dest := 0;
    if (req_read_exclusive = req_read_shared) then
      node[client].outchan_3.msg.op := read_shared;
else
      if (req_read_exclusive = req_read_exclusive) then
        node[client].outchan_3.msg.op := read_exclusive;
else
        node[client].outchan_3.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_3.msg.addr := addr;
    node[client].outchan_3.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_generates_new_req_for_addr_reqreq_req_upgrade_channel13"
    ((((3 = 1) & (node[client].local_requests[addr] = false)) & ((((req_req_upgrade = req_read_shared) & (node[client].cache[addr].state = cache_invalid)) | ((req_req_upgrade = req_read_exclusive) & (node[client].cache[addr].state = cache_invalid))) | ((req_req_upgrade = req_req_upgrade) & (node[client].cache[addr].state = cache_shared)))) & (node[client].outchan_3.valid = false)) ==>
  begin
    node[client].outchan_3.msg.source := client;
    node[client].outchan_3.msg.dest := 0;
    if (req_req_upgrade = req_read_shared) then
      node[client].outchan_3.msg.op := read_shared;
else
      if (req_req_upgrade = req_read_exclusive) then
        node[client].outchan_3.msg.op := read_exclusive;
else
        node[client].outchan_3.msg.op := req_upgrade;
      endif;
    endif;
    node[client].outchan_3.msg.addr := addr;
    node[client].outchan_3.valid := true;
    node[client].local_requests[addr] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_accepts_invalidate_request_channel21"
    (((((1 = 2) & (addr = node[client].inchan_1.msg.addr)) & (node[client].inchan_1.valid = true)) & (node[client].inchan_1.msg.op = invalidate)) & (node[client].remote_requests[addr].status = inactive)) ==>
  begin
    node[client].remote_requests[addr].home := node[client].inchan_1.msg.source;
    node[client].remote_requests[addr].op := node[client].inchan_1.msg.op;
    node[client].remote_requests[addr].status := pending;
    node[client].inchan_1.msg.source := 0;
    node[client].inchan_1.msg.dest := 0;
    node[client].inchan_1.msg.op := op_invalid;
    node[client].inchan_1.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_1.msg.data.values[k] := false;
    endfor;
    node[client].inchan_1.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_accepts_invalidate_request_channel22"
    (((((2 = 2) & (addr = node[client].inchan_2.msg.addr)) & (node[client].inchan_2.valid = true)) & (node[client].inchan_2.msg.op = invalidate)) & (node[client].remote_requests[addr].status = inactive)) ==>
  begin
    node[client].remote_requests[addr].home := node[client].inchan_2.msg.source;
    node[client].remote_requests[addr].op := node[client].inchan_2.msg.op;
    node[client].remote_requests[addr].status := pending;
    node[client].inchan_2.msg.source := 0;
    node[client].inchan_2.msg.dest := 0;
    node[client].inchan_2.msg.op := op_invalid;
    node[client].inchan_2.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_2.msg.data.values[k] := false;
    endfor;
    node[client].inchan_2.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_accepts_invalidate_request_channel23"
    (((((3 = 2) & (addr = node[client].inchan_3.msg.addr)) & (node[client].inchan_3.valid = true)) & (node[client].inchan_3.msg.op = invalidate)) & (node[client].remote_requests[addr].status = inactive)) ==>
  begin
    node[client].remote_requests[addr].home := node[client].inchan_3.msg.source;
    node[client].remote_requests[addr].op := node[client].inchan_3.msg.op;
    node[client].remote_requests[addr].status := pending;
    node[client].inchan_3.msg.source := 0;
    node[client].inchan_3.msg.dest := 0;
    node[client].inchan_3.msg.op := op_invalid;
    node[client].inchan_3.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_3.msg.data.values[k] := false;
    endfor;
    node[client].inchan_3.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_processes_invalidate_request_for_addr"
    ((node[client].remote_requests[addr].status = pending) & (node[client].remote_requests[addr].op = invalidate)) ==>
  begin
    for i : num_data_type do
      node[client].remote_requests[addr].data.values[i] := node[client].cache[addr].data.values[i];
    endfor;
    node[client].remote_requests[addr].status := completed;
    node[client].cache[addr].state := cache_invalid;
    for k : num_data_type do
      node[client].cache[addr].data.values[k] := false;
    endfor;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_prepares_invalidate_ack_for_addr_channel31"
    ((((1 = 3) & (node[client].remote_requests[addr].status = completed)) & (node[client].remote_requests[addr].op = invalidate)) & (node[client].outchan_1.valid = false)) ==>
  begin
    node[client].outchan_1.msg.op := invalidate_ack;
    node[client].outchan_1.msg.source := client;
    node[client].outchan_1.msg.dest := node[client].remote_requests[addr].home;
    for i : num_data_type do
      node[client].outchan_1.msg.data.values[i] := node[client].remote_requests[addr].data.values[i];
    endfor;
    node[client].outchan_1.msg.addr := addr;
    node[client].outchan_1.valid := true;
    node[client].remote_requests[addr].home := 0;
    node[client].remote_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[client].remote_requests[addr].data.values[k] := false;
    endfor;
    node[client].remote_requests[addr].status := inactive;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_prepares_invalidate_ack_for_addr_channel32"
    ((((2 = 3) & (node[client].remote_requests[addr].status = completed)) & (node[client].remote_requests[addr].op = invalidate)) & (node[client].outchan_2.valid = false)) ==>
  begin
    node[client].outchan_2.msg.op := invalidate_ack;
    node[client].outchan_2.msg.source := client;
    node[client].outchan_2.msg.dest := node[client].remote_requests[addr].home;
    for i : num_data_type do
      node[client].outchan_2.msg.data.values[i] := node[client].remote_requests[addr].data.values[i];
    endfor;
    node[client].outchan_2.msg.addr := addr;
    node[client].outchan_2.valid := true;
    node[client].remote_requests[addr].home := 0;
    node[client].remote_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[client].remote_requests[addr].data.values[k] := false;
    endfor;
    node[client].remote_requests[addr].status := inactive;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_prepares_invalidate_ack_for_addr_channel33"
    ((((3 = 3) & (node[client].remote_requests[addr].status = completed)) & (node[client].remote_requests[addr].op = invalidate)) & (node[client].outchan_3.valid = false)) ==>
  begin
    node[client].outchan_3.msg.op := invalidate_ack;
    node[client].outchan_3.msg.source := client;
    node[client].outchan_3.msg.dest := node[client].remote_requests[addr].home;
    for i : num_data_type do
      node[client].outchan_3.msg.data.values[i] := node[client].remote_requests[addr].data.values[i];
    endfor;
    node[client].outchan_3.msg.addr := addr;
    node[client].outchan_3.valid := true;
    node[client].remote_requests[addr].home := 0;
    node[client].remote_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[client].remote_requests[addr].data.values[k] := false;
    endfor;
    node[client].remote_requests[addr].status := inactive;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_receives_reply_from_home_channel21"
    ((((1 = 2) & (addr = node[client].inchan_1.msg.addr)) & (node[client].inchan_1.valid = true)) & (((node[client].inchan_1.msg.op = grant_shared) | (node[client].inchan_1.msg.op = grant_upgrade)) | (node[client].inchan_1.msg.op = grant_exclusive))) ==>
  begin
    if (node[client].inchan_1.msg.op = grant_shared) then
      for i : num_data_type do
        node[client].cache[addr].data.values[i] := node[client].inchan_1.msg.data.values[i];
      endfor;
      node[client].cache[addr].state := cache_shared;
else
      if (node[client].inchan_1.msg.op = grant_upgrade) then
        node[client].cache[addr].state := cache_exclusive;
else
        if (node[client].inchan_1.msg.op = grant_exclusive) then
          for i : num_data_type do
            node[client].cache[addr].data.values[i] := node[client].inchan_1.msg.data.values[i];
          endfor;
          node[client].cache[addr].state := cache_exclusive;
        endif;
      endif;
    endif;
    node[client].local_requests[addr] := false;
    node[client].inchan_1.msg.source := 0;
    node[client].inchan_1.msg.dest := 0;
    node[client].inchan_1.msg.op := op_invalid;
    node[client].inchan_1.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_1.msg.data.values[k] := false;
    endfor;
    node[client].inchan_1.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_receives_reply_from_home_channel22"
    ((((2 = 2) & (addr = node[client].inchan_2.msg.addr)) & (node[client].inchan_2.valid = true)) & (((node[client].inchan_2.msg.op = grant_shared) | (node[client].inchan_2.msg.op = grant_upgrade)) | (node[client].inchan_2.msg.op = grant_exclusive))) ==>
  begin
    if (node[client].inchan_2.msg.op = grant_shared) then
      for i : num_data_type do
        node[client].cache[addr].data.values[i] := node[client].inchan_2.msg.data.values[i];
      endfor;
      node[client].cache[addr].state := cache_shared;
else
      if (node[client].inchan_2.msg.op = grant_upgrade) then
        node[client].cache[addr].state := cache_exclusive;
else
        if (node[client].inchan_2.msg.op = grant_exclusive) then
          for i : num_data_type do
            node[client].cache[addr].data.values[i] := node[client].inchan_2.msg.data.values[i];
          endfor;
          node[client].cache[addr].state := cache_exclusive;
        endif;
      endif;
    endif;
    node[client].local_requests[addr] := false;
    node[client].inchan_2.msg.source := 0;
    node[client].inchan_2.msg.dest := 0;
    node[client].inchan_2.msg.op := op_invalid;
    node[client].inchan_2.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_2.msg.data.values[k] := false;
    endfor;
    node[client].inchan_2.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type do
  rule "n_client_receives_reply_from_home_channel23"
    ((((3 = 2) & (addr = node[client].inchan_3.msg.addr)) & (node[client].inchan_3.valid = true)) & (((node[client].inchan_3.msg.op = grant_shared) | (node[client].inchan_3.msg.op = grant_upgrade)) | (node[client].inchan_3.msg.op = grant_exclusive))) ==>
  begin
    if (node[client].inchan_3.msg.op = grant_shared) then
      for i : num_data_type do
        node[client].cache[addr].data.values[i] := node[client].inchan_3.msg.data.values[i];
      endfor;
      node[client].cache[addr].state := cache_shared;
else
      if (node[client].inchan_3.msg.op = grant_upgrade) then
        node[client].cache[addr].state := cache_exclusive;
else
        if (node[client].inchan_3.msg.op = grant_exclusive) then
          for i : num_data_type do
            node[client].cache[addr].data.values[i] := node[client].inchan_3.msg.data.values[i];
          endfor;
          node[client].cache[addr].state := cache_exclusive;
        endif;
      endif;
    endif;
    node[client].local_requests[addr] := false;
    node[client].inchan_3.msg.source := 0;
    node[client].inchan_3.msg.dest := 0;
    node[client].inchan_3.msg.op := op_invalid;
    node[client].inchan_3.msg.addr := 1;
    for k : num_data_type do
      node[client].inchan_3.msg.data.values[k] := false;
    endfor;
    node[client].inchan_3.valid := false;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type; data_n : num_data_type do
  rule "n_client_stores_data_in_cache_for_addr_dataTRUE"
    ((!(node[client].remote_requests[addr].status = pending)) & (node[client].cache[addr].state = cache_exclusive)) ==>
  begin
    node[client].cache[addr].data.values[data_n] := true;
    auxdata[addr].values[data_n] := true;
  endrule;
endruleset;


ruleset client : node_id; addr : addr_type; data_n : num_data_type do
  rule "n_client_stores_data_in_cache_for_addr_dataFALSE"
    ((!(node[client].remote_requests[addr].status = pending)) & (node[client].cache[addr].state = cache_exclusive)) ==>
  begin
    node[client].cache[addr].data.values[data_n] := false;
    auxdata[addr].values[data_n] := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_accepts_a_request_message_channel11"
    (((((1 = 1) & (addr = node[home].inchan_1.msg.addr)) & (source = node[home].inchan_1.msg.source)) & (node[home].inchan_1.valid = true)) & (node[home].home_requests[addr].status = inactive)) ==>
  begin
    if ((node[home].inchan_1.msg.op = req_upgrade) & (node[home].directory[addr][source] = cache_invalid)) then
      node[home].inchan_1.msg.op := read_exclusive;
    endif;
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := node[home].inchan_1.msg.op;
    if ((node[home].inchan_1.msg.op = read_shared) & (node[home].directory[addr][home] = cache_shared)) then
      if (node[home].cache[addr].state = cache_shared) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].cache[addr].data.values[i];
        endfor;
else
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
      endif;
      node[home].home_requests[addr].status := completed;
else
      if (((node[home].inchan_1.msg.op = read_shared) & (node[home].directory[addr][home] = cache_invalid)) & (!(exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists))) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
        node[home].home_requests[addr].status := completed;
else
        if ((node[home].inchan_1.msg.op = read_shared) & (exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists)) then
          for n : node_id do
            if (!(node[home].directory[addr][n] = cache_invalid)) then
              node[home].home_requests[addr].invalidate_list[n] := true;
else
              node[home].home_requests[addr].invalidate_list[n] := false;
            endif;
          endfor;
          node[home].home_requests[addr].status := pending;
else
          if (node[home].inchan_1.msg.op = req_upgrade) then
            for n : node_id do
              if ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) then
                node[home].home_requests[addr].invalidate_list[n] := true;
else
                node[home].home_requests[addr].invalidate_list[n] := false;
              endif;
            endfor;
            if (exists n : node_id do ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) endexists) then
              node[home].home_requests[addr].status := pending;
else
              node[home].home_requests[addr].status := completed;
            endif;
else
            if (node[home].inchan_1.msg.op = read_exclusive) then
              for n : node_id do
                if (!(node[home].directory[addr][n] = cache_invalid)) then
                  node[home].home_requests[addr].invalidate_list[n] := true;
else
                  node[home].home_requests[addr].invalidate_list[n] := false;
                endif;
              endfor;
              if (exists n : node_id do (!(node[home].directory[addr][n] = cache_invalid)) endexists) then
                node[home].home_requests[addr].status := pending;
else
                for i : num_data_type do
                  node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
                endfor;
                node[home].home_requests[addr].status := completed;
              endif;
            endif;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_1.msg.source := 0;
    node[home].inchan_1.msg.dest := 0;
    node[home].inchan_1.msg.op := op_invalid;
    node[home].inchan_1.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_1.msg.data.values[k] := false;
    endfor;
    node[home].inchan_1.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_accepts_a_request_message_channel12"
    (((((2 = 1) & (addr = node[home].inchan_2.msg.addr)) & (source = node[home].inchan_2.msg.source)) & (node[home].inchan_2.valid = true)) & (node[home].home_requests[addr].status = inactive)) ==>
  begin
    if ((node[home].inchan_2.msg.op = req_upgrade) & (node[home].directory[addr][source] = cache_invalid)) then
      node[home].inchan_2.msg.op := read_exclusive;
    endif;
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := node[home].inchan_2.msg.op;
    if ((node[home].inchan_2.msg.op = read_shared) & (node[home].directory[addr][home] = cache_shared)) then
      if (node[home].cache[addr].state = cache_shared) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].cache[addr].data.values[i];
        endfor;
else
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
      endif;
      node[home].home_requests[addr].status := completed;
else
      if (((node[home].inchan_2.msg.op = read_shared) & (node[home].directory[addr][home] = cache_invalid)) & (!(exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists))) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
        node[home].home_requests[addr].status := completed;
else
        if ((node[home].inchan_2.msg.op = read_shared) & (exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists)) then
          for n : node_id do
            if (!(node[home].directory[addr][n] = cache_invalid)) then
              node[home].home_requests[addr].invalidate_list[n] := true;
else
              node[home].home_requests[addr].invalidate_list[n] := false;
            endif;
          endfor;
          node[home].home_requests[addr].status := pending;
else
          if (node[home].inchan_2.msg.op = req_upgrade) then
            for n : node_id do
              if ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) then
                node[home].home_requests[addr].invalidate_list[n] := true;
else
                node[home].home_requests[addr].invalidate_list[n] := false;
              endif;
            endfor;
            if (exists n : node_id do ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) endexists) then
              node[home].home_requests[addr].status := pending;
else
              node[home].home_requests[addr].status := completed;
            endif;
else
            if (node[home].inchan_2.msg.op = read_exclusive) then
              for n : node_id do
                if (!(node[home].directory[addr][n] = cache_invalid)) then
                  node[home].home_requests[addr].invalidate_list[n] := true;
else
                  node[home].home_requests[addr].invalidate_list[n] := false;
                endif;
              endfor;
              if (exists n : node_id do (!(node[home].directory[addr][n] = cache_invalid)) endexists) then
                node[home].home_requests[addr].status := pending;
else
                for i : num_data_type do
                  node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
                endfor;
                node[home].home_requests[addr].status := completed;
              endif;
            endif;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_2.msg.source := 0;
    node[home].inchan_2.msg.dest := 0;
    node[home].inchan_2.msg.op := op_invalid;
    node[home].inchan_2.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_2.msg.data.values[k] := false;
    endfor;
    node[home].inchan_2.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_accepts_a_request_message_channel13"
    (((((3 = 1) & (addr = node[home].inchan_3.msg.addr)) & (source = node[home].inchan_3.msg.source)) & (node[home].inchan_3.valid = true)) & (node[home].home_requests[addr].status = inactive)) ==>
  begin
    if ((node[home].inchan_3.msg.op = req_upgrade) & (node[home].directory[addr][source] = cache_invalid)) then
      node[home].inchan_3.msg.op := read_exclusive;
    endif;
    node[home].home_requests[addr].source := source;
    node[home].home_requests[addr].op := node[home].inchan_3.msg.op;
    if ((node[home].inchan_3.msg.op = read_shared) & (node[home].directory[addr][home] = cache_shared)) then
      if (node[home].cache[addr].state = cache_shared) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].cache[addr].data.values[i];
        endfor;
else
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
      endif;
      node[home].home_requests[addr].status := completed;
else
      if (((node[home].inchan_3.msg.op = read_shared) & (node[home].directory[addr][home] = cache_invalid)) & (!(exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists))) then
        for i : num_data_type do
          node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
        endfor;
        node[home].home_requests[addr].status := completed;
else
        if ((node[home].inchan_3.msg.op = read_shared) & (exists n : node_id do (node[home].directory[addr][n] = cache_exclusive) endexists)) then
          for n : node_id do
            if (!(node[home].directory[addr][n] = cache_invalid)) then
              node[home].home_requests[addr].invalidate_list[n] := true;
else
              node[home].home_requests[addr].invalidate_list[n] := false;
            endif;
          endfor;
          node[home].home_requests[addr].status := pending;
else
          if (node[home].inchan_3.msg.op = req_upgrade) then
            for n : node_id do
              if ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) then
                node[home].home_requests[addr].invalidate_list[n] := true;
else
                node[home].home_requests[addr].invalidate_list[n] := false;
              endif;
            endfor;
            if (exists n : node_id do ((!(node[home].directory[addr][n] = cache_invalid)) & (!(n = source))) endexists) then
              node[home].home_requests[addr].status := pending;
else
              node[home].home_requests[addr].status := completed;
            endif;
else
            if (node[home].inchan_3.msg.op = read_exclusive) then
              for n : node_id do
                if (!(node[home].directory[addr][n] = cache_invalid)) then
                  node[home].home_requests[addr].invalidate_list[n] := true;
else
                  node[home].home_requests[addr].invalidate_list[n] := false;
                endif;
              endfor;
              if (exists n : node_id do (!(node[home].directory[addr][n] = cache_invalid)) endexists) then
                node[home].home_requests[addr].status := pending;
else
                for i : num_data_type do
                  node[home].home_requests[addr].data.values[i] := node[home].memory[addr].values[i];
                endfor;
                node[home].home_requests[addr].status := completed;
              endif;
            endif;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_3.msg.source := 0;
    node[home].inchan_3.msg.dest := 0;
    node[home].inchan_3.msg.op := op_invalid;
    node[home].inchan_3.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_3.msg.data.values[k] := false;
    endfor;
    node[home].inchan_3.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; dest : node_id do
  rule "n_home_prepares_invalidate_for_addr_channel21"
    (((((1 = 2) & (node[home].home_requests[addr].invalidate_list[dest] = true)) & (node[home].home_requests[addr].status = pending)) & (exists n : node_id do (node[home].home_requests[addr].invalidate_list[n] = true) endexists)) & (node[home].outchan_1.valid = false)) ==>
  begin
    node[home].outchan_1.msg.addr := addr;
    node[home].outchan_1.msg.op := invalidate;
    node[home].outchan_1.msg.source := home;
    node[home].outchan_1.msg.dest := dest;
    node[home].outchan_1.valid := true;
    node[home].home_requests[addr].invalidate_list[dest] := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; dest : node_id do
  rule "n_home_prepares_invalidate_for_addr_channel22"
    (((((2 = 2) & (node[home].home_requests[addr].invalidate_list[dest] = true)) & (node[home].home_requests[addr].status = pending)) & (exists n : node_id do (node[home].home_requests[addr].invalidate_list[n] = true) endexists)) & (node[home].outchan_2.valid = false)) ==>
  begin
    node[home].outchan_2.msg.addr := addr;
    node[home].outchan_2.msg.op := invalidate;
    node[home].outchan_2.msg.source := home;
    node[home].outchan_2.msg.dest := dest;
    node[home].outchan_2.valid := true;
    node[home].home_requests[addr].invalidate_list[dest] := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; dest : node_id do
  rule "n_home_prepares_invalidate_for_addr_channel23"
    (((((3 = 2) & (node[home].home_requests[addr].invalidate_list[dest] = true)) & (node[home].home_requests[addr].status = pending)) & (exists n : node_id do (node[home].home_requests[addr].invalidate_list[n] = true) endexists)) & (node[home].outchan_3.valid = false)) ==>
  begin
    node[home].outchan_3.msg.addr := addr;
    node[home].outchan_3.msg.op := invalidate;
    node[home].outchan_3.msg.source := home;
    node[home].outchan_3.msg.dest := dest;
    node[home].outchan_3.valid := true;
    node[home].home_requests[addr].invalidate_list[dest] := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_processes_invalidate_ack_channel31"
    ((((((1 = 3) & (addr = node[home].inchan_1.msg.addr)) & (source = node[home].inchan_1.msg.source)) & (node[home].inchan_1.valid = true)) & (node[home].home_requests[addr].status = pending)) & (node[home].inchan_1.msg.op = invalidate_ack)) ==>
  begin
    if (node[home].directory[addr][source] = cache_exclusive) then
      for i : num_data_type do
        node[home].memory[addr].values[i] := node[home].inchan_1.msg.data.values[i];
      endfor;
    endif;
    for i : num_data_type do
      node[home].home_requests[addr].data.values[i] := node[home].inchan_1.msg.data.values[i];
    endfor;
    node[home].directory[addr][source] := cache_invalid;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].home_requests[addr].status := completed;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        if (forall n : node_id do ((!(n = node[home].home_requests[addr].source)) -> (node[home].directory[addr][n] = cache_invalid)) endforall) then
          node[home].home_requests[addr].status := completed;
        endif;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          if (forall n : node_id do (node[home].directory[addr][n] = cache_invalid) endforall) then
            node[home].home_requests[addr].status := completed;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_1.msg.source := 0;
    node[home].inchan_1.msg.dest := 0;
    node[home].inchan_1.msg.op := op_invalid;
    node[home].inchan_1.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_1.msg.data.values[k] := false;
    endfor;
    node[home].inchan_1.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_processes_invalidate_ack_channel32"
    ((((((2 = 3) & (addr = node[home].inchan_2.msg.addr)) & (source = node[home].inchan_2.msg.source)) & (node[home].inchan_2.valid = true)) & (node[home].home_requests[addr].status = pending)) & (node[home].inchan_2.msg.op = invalidate_ack)) ==>
  begin
    if (node[home].directory[addr][source] = cache_exclusive) then
      for i : num_data_type do
        node[home].memory[addr].values[i] := node[home].inchan_2.msg.data.values[i];
      endfor;
    endif;
    for i : num_data_type do
      node[home].home_requests[addr].data.values[i] := node[home].inchan_2.msg.data.values[i];
    endfor;
    node[home].directory[addr][source] := cache_invalid;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].home_requests[addr].status := completed;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        if (forall n : node_id do ((!(n = node[home].home_requests[addr].source)) -> (node[home].directory[addr][n] = cache_invalid)) endforall) then
          node[home].home_requests[addr].status := completed;
        endif;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          if (forall n : node_id do (node[home].directory[addr][n] = cache_invalid) endforall) then
            node[home].home_requests[addr].status := completed;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_2.msg.source := 0;
    node[home].inchan_2.msg.dest := 0;
    node[home].inchan_2.msg.op := op_invalid;
    node[home].inchan_2.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_2.msg.data.values[k] := false;
    endfor;
    node[home].inchan_2.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_processes_invalidate_ack_channel33"
    ((((((3 = 3) & (addr = node[home].inchan_3.msg.addr)) & (source = node[home].inchan_3.msg.source)) & (node[home].inchan_3.valid = true)) & (node[home].home_requests[addr].status = pending)) & (node[home].inchan_3.msg.op = invalidate_ack)) ==>
  begin
    if (node[home].directory[addr][source] = cache_exclusive) then
      for i : num_data_type do
        node[home].memory[addr].values[i] := node[home].inchan_3.msg.data.values[i];
      endfor;
    endif;
    for i : num_data_type do
      node[home].home_requests[addr].data.values[i] := node[home].inchan_3.msg.data.values[i];
    endfor;
    node[home].directory[addr][source] := cache_invalid;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].home_requests[addr].status := completed;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        if (forall n : node_id do ((!(n = node[home].home_requests[addr].source)) -> (node[home].directory[addr][n] = cache_invalid)) endforall) then
          node[home].home_requests[addr].status := completed;
        endif;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          if (forall n : node_id do (node[home].directory[addr][n] = cache_invalid) endforall) then
            node[home].home_requests[addr].status := completed;
          endif;
        endif;
      endif;
    endif;
    node[home].inchan_3.msg.source := 0;
    node[home].inchan_3.msg.dest := 0;
    node[home].inchan_3.msg.op := op_invalid;
    node[home].inchan_3.msg.addr := 1;
    for k : num_data_type do
      node[home].inchan_3.msg.data.values[k] := false;
    endfor;
    node[home].inchan_3.valid := false;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_sends_grant_for_addr_channel21"
    ((((1 = 2) & (source = node[home].home_requests[addr].source)) & (node[home].home_requests[addr].status = completed)) & (node[home].outchan_1.valid = false)) ==>
  begin
    node[home].outchan_1.msg.source := home;
    node[home].outchan_1.msg.dest := node[home].home_requests[addr].source;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].outchan_1.msg.op := grant_shared;
      node[home].directory[addr][source] := cache_shared;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        node[home].outchan_1.msg.op := grant_upgrade;
        node[home].directory[addr][source] := cache_exclusive;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          node[home].outchan_1.msg.op := grant_exclusive;
          node[home].directory[addr][source] := cache_exclusive;
        endif;
      endif;
    endif;
    for i : num_data_type do
      node[home].outchan_1.msg.data.values[i] := node[home].home_requests[addr].data.values[i];
    endfor;
    node[home].outchan_1.msg.addr := addr;
    node[home].outchan_1.valid := true;
    node[home].home_requests[addr].source := 0;
    node[home].home_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[home].home_requests[addr].data.values[k] := false;
    endfor;
    for k : node_id do
      node[home].home_requests[addr].invalidate_list[k] := false;
    endfor;
    node[home].home_requests[addr].status := inactive;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_sends_grant_for_addr_channel22"
    ((((2 = 2) & (source = node[home].home_requests[addr].source)) & (node[home].home_requests[addr].status = completed)) & (node[home].outchan_2.valid = false)) ==>
  begin
    node[home].outchan_2.msg.source := home;
    node[home].outchan_2.msg.dest := node[home].home_requests[addr].source;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].outchan_2.msg.op := grant_shared;
      node[home].directory[addr][source] := cache_shared;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        node[home].outchan_2.msg.op := grant_upgrade;
        node[home].directory[addr][source] := cache_exclusive;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          node[home].outchan_2.msg.op := grant_exclusive;
          node[home].directory[addr][source] := cache_exclusive;
        endif;
      endif;
    endif;
    for i : num_data_type do
      node[home].outchan_2.msg.data.values[i] := node[home].home_requests[addr].data.values[i];
    endfor;
    node[home].outchan_2.msg.addr := addr;
    node[home].outchan_2.valid := true;
    node[home].home_requests[addr].source := 0;
    node[home].home_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[home].home_requests[addr].data.values[k] := false;
    endfor;
    for k : node_id do
      node[home].home_requests[addr].invalidate_list[k] := false;
    endfor;
    node[home].home_requests[addr].status := inactive;
  endrule;
endruleset;


ruleset home : node_id; addr : addr_type; source : node_id do
  rule "n_home_sends_grant_for_addr_channel23"
    ((((3 = 2) & (source = node[home].home_requests[addr].source)) & (node[home].home_requests[addr].status = completed)) & (node[home].outchan_3.valid = false)) ==>
  begin
    node[home].outchan_3.msg.source := home;
    node[home].outchan_3.msg.dest := node[home].home_requests[addr].source;
    if (node[home].home_requests[addr].op = read_shared) then
      node[home].outchan_3.msg.op := grant_shared;
      node[home].directory[addr][source] := cache_shared;
else
      if (node[home].home_requests[addr].op = req_upgrade) then
        node[home].outchan_3.msg.op := grant_upgrade;
        node[home].directory[addr][source] := cache_exclusive;
else
        if (node[home].home_requests[addr].op = read_exclusive) then
          node[home].outchan_3.msg.op := grant_exclusive;
          node[home].directory[addr][source] := cache_exclusive;
        endif;
      endif;
    endif;
    for i : num_data_type do
      node[home].outchan_3.msg.data.values[i] := node[home].home_requests[addr].data.values[i];
    endfor;
    node[home].outchan_3.msg.addr := addr;
    node[home].outchan_3.valid := true;
    node[home].home_requests[addr].source := 0;
    node[home].home_requests[addr].op := op_invalid;
    for k : num_data_type do
      node[home].home_requests[addr].data.values[k] := false;
    endfor;
    for k : node_id do
      node[home].home_requests[addr].invalidate_list[k] := false;
    endfor;
    node[home].home_requests[addr].status := inactive;
  endrule;
endruleset;

