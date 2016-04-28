const

  NODE_NUM : 5;
  DATA_NUM : 2;

type

  NODE : 1..NODE_NUM;
  DATA : 1..DATA_NUM;

  CACHE_STATE : enum {I, S, E};
  CACHE : record State : CACHE_STATE; Data : DATA; end;

  MSG_CMD : enum {Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
  MSG : record Cmd : MSG_CMD; Data : DATA; end;

var

  Cache : array [NODE] of CACHE;
  Chan1 : array [NODE] of MSG;   
  Chan2 : array [NODE] of MSG;      
  Chan3 : array [NODE] of MSG;     
  InvSet : array [NODE] of boolean;  
  ShrSet : array [NODE] of boolean; 
  ExGntd : boolean;   
  CurCmd : MSG_CMD;  
  CurPtr : NODE;   
  MemData : DATA;  
  AuxData : DATA;


ruleset d : DATA do startstate "Init"
  for i : NODE do
    Chan1[i].Cmd := Empty; Chan2[i].Cmd := Empty; Chan3[i].Cmd := Empty;
    Cache[i].State := I; InvSet[i] := false; ShrSet[i] := false;
  end;
  ExGntd := false; CurCmd := Empty; MemData := d; AuxData := d;
endstartstate; endruleset;


ruleset i : NODE; d : DATA do rule "Store"
  Cache[i].State = E
==> begin
  Cache[i].Data := d; AuxData := d;
endrule; endruleset;

ruleset i : NODE do rule "SendReqS"
  Chan1[i].Cmd = Empty & Cache[i].State = I
==> begin
  Chan1[i].Cmd := ReqS;
endrule; endruleset;

ruleset i : NODE do rule "SendReqE"
  Chan1[i].Cmd = Empty & (Cache[i].State = I | Cache[i].State = S)
==> begin
  Chan1[i].Cmd := ReqE;
endrule; endruleset;

ruleset i : NODE do rule "RecvReqS"
  CurCmd = Empty & Chan1[i].Cmd = ReqS
==> begin
  CurCmd := ReqS; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j]; end;
endrule; endruleset;

ruleset i : NODE do rule "RecvReqE"
  CurCmd = Empty & Chan1[i].Cmd = ReqE
==> begin
  CurCmd := ReqE; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j]; end;
endrule; endruleset;

ruleset i : NODE do rule "SendInv"
  Chan2[i].Cmd = Empty & InvSet[i] = true &
  ( CurCmd = ReqE | CurCmd = ReqS & ExGntd = true )
==> begin
  Chan2[i].Cmd := Inv; InvSet[i] := false;
endrule; endruleset;

ruleset i : NODE do rule "SendInvAck"
  Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty
==> begin
  Chan2[i].Cmd := Empty; Chan3[i].Cmd := InvAck;
  if (Cache[i].State = E) then Chan3[i].Data := Cache[i].Data; end;
  Cache[i].State := I;
endrule; endruleset;

ruleset i : NODE do rule "RecvInvAck"
  Chan3[i].Cmd = InvAck & CurCmd != Empty
==> begin
  Chan3[i].Cmd := Empty; ShrSet[i] := false;
  if (ExGntd = true)
  then ExGntd := false; MemData := Chan3[i].Data; end;
endrule; endruleset;

ruleset i : NODE do rule "SendGntS"
  CurCmd = ReqS & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false
==> begin
  Chan2[i].Cmd := GntS; Chan2[i].Data := MemData; ShrSet[i] := true;
  CurCmd := Empty;
endrule; endruleset;

ruleset i : NODE do rule "SendGntE"
  CurCmd = ReqE & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false &
  forall j : NODE do ShrSet[j] = false end
==> begin
  Chan2[i].Cmd := GntE; Chan2[i].Data := MemData; ShrSet[i] := true;
  ExGntd := true; CurCmd := Empty;
endrule; endruleset;

ruleset i : NODE do rule "RecvGntS"
  Chan2[i].Cmd = GntS
==> begin
  Cache[i].State := S; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
endrule; endruleset;

ruleset i : NODE do rule "RecvGntE"
  Chan2[i].Cmd = GntE
==> begin
  Cache[i].State := E; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
endrule; endruleset;
































































































































































































































































