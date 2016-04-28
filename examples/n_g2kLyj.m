const
    NODE_NUM : 5;
    DATA_NUM : 2;

type
     NODE : 1..NODE_NUM;
     DATA : 1..DATA_NUM;
     
     CACHE_STATE : enum{I, S, E};
     CACHE : record State : CACHE_STATE; Data : DATA; end;
     
     MSG_CMD : enum{Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
     MSG : record Cmd : MSG_CMD; Data : DATA; end;

var
    Cache: array [NODE] of CACHE;
    Chan1: array [NODE] of MSG;
    Chan2: array [NODE] of MSG;
    Chan3: array [NODE] of MSG;
    ShrSet: array [NODE] of boolean;
    InvSet: array [NODE] of boolean;
    ExGntd: boolean;
    CurCmd: MSG_CMD;
    CurPtr: NODE;
    MemData: DATA;
    AuxData: DATA;
    

ruleset d: DATA do startstate "Init"
 for i: NODE do
   Chan1[i].Cmd := Empty;
   Chan2[i].Cmd := Empty; 
   Chan3[i].Cmd := Empty;   
   Chan1[i].Data := d;
   Chan2[i].Data := d; 
   Chan3[i].Data := d;   
   Cache[i].State := I;
   Cache[i].Data := d;
   ShrSet[i] := false;
   InvSet[i] := false;
  end;
  CurCmd := Empty;
  ExGntd := false;
  MemData := d;
  AuxData := d;
endstartstate; endruleset;

ruleset j: NODE do
 rule "SendReqS"
      Cache[j].State = I & Chan1[j].Cmd = Empty ==> 
        begin Chan1[j].Cmd := ReqS;
endrule; endruleset;

ruleset i: NODE do
 rule "SendReqEI"
      (Cache[i].State = I) & Chan1[i].Cmd = Empty ==> 
        begin Chan1[i].Cmd := ReqE;
endrule; endruleset;

ruleset i: NODE do
 rule "SendReqES"
      (Cache[i].State = S) & Chan1[i].Cmd = Empty ==> 
        begin Chan1[i].Cmd := ReqE;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvReq"
       CurCmd = Empty & Chan1[i].Cmd != Empty ==>
        begin CurCmd := Chan1[i].Cmd; 
              Chan1[i].Cmd := Empty;
              CurPtr := i;
              for j: NODE do
               if ShrSet[j] then InvSet[j] := true; else InvSet[j] :=false; endif;
              endfor;
endrule; endruleset;
  
ruleset i: NODE do
 rule "SendInvE"
      (CurCmd = ReqE)
      & InvSet[i] & Chan2[i].Cmd = Empty ==>
       begin
        Chan2[i].Cmd := Inv;
        InvSet[i] := false;
endrule; endruleset;
  
ruleset i: NODE do
 rule "SendInvS"
      (CurCmd = ReqS & ExGntd)
      & InvSet[i] & Chan2[i].Cmd = Empty ==>
       begin
        Chan2[i].Cmd := Inv;
        InvSet[i] := false;
endrule; endruleset;
 
ruleset i: NODE do
 rule "SendInvAck"
      Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty ==>
      begin
       Chan2[i].Cmd := Empty;
       Chan3[i].Cmd := InvAck;
       if (Cache[i].State = E) then Chan3[i].Data := Cache[i].Data; end;
       Cache[i].State := I;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvInvAck"
      CurCmd != Empty & Chan3[i].Cmd = InvAck ==>
      begin 
       ShrSet[i] := false;
       if (ExGntd = true)
       then ExGntd := false; MemData := Chan3[i].Data; end;
       Chan3[i].Cmd := Empty;
endrule; endruleset;

ruleset i: NODE do
 rule "SendGntS"
      CurCmd = ReqS & CurPtr = i
      & !ExGntd & Chan2[i].Cmd = Empty ==>
      begin
       ShrSet[i] := true;
       CurCmd := Empty;
       Chan2[i].Cmd := GntS;
       Chan2[i].Data := MemData;
endrule; endruleset;

ruleset i: NODE do
 rule "SendGntE"
      CurCmd = ReqE & CurPtr = i & !ExGntd 
      & forall j: NODE do ShrSet[j] = false endforall
      & Chan2[i].Cmd = Empty ==>
      begin
       ShrSet[i] := true;
       CurCmd := Empty;
       ExGntd := true;
       Chan2[i].Cmd := GntE;
       Chan2[i].Data := MemData;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvGntS"
      Chan2[i].Cmd = GntS ==>
      begin
       Cache[i].State := S;
       Chan2[i].Cmd := Empty;
       Cache[i].Data := Chan2[i].Data;
endrule; endruleset;

ruleset i: NODE do
 rule "RecvGntE"
      Chan2[i].Cmd = GntE ==>
      begin
       Cache[i].State := E;
       Chan2[i].Cmd := Empty;
       Cache[i].Data := Chan2[i].Data;
endrule; endruleset;

ruleset i: NODE; d: DATA do
 rule "Store"
      Cache[i].State = E ==>
      begin
       Cache[i].Data := d;
       AuxData := d;
endrule; endruleset;

