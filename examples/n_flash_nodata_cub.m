
const

  NODE_NUM : 5;

type

  NODE : 1..NODE_NUM;

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : NODE;
    HomeHeadPtr : boolean;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    HomeShrSet : boolean;
    InvSet : array [NODE] of boolean;
    HomeInvSet : boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
    Proc : array [NODE] of NODE_STATE;
    HomeProc : NODE_STATE;
    Dir : DIR_STATE;
    UniMsg : array [NODE] of UNI_MSG;
    HomeUniMsg : UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    HomeInvMsg : INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    HomeRpMsg : RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  end;

var

  Sta : STATE;


ruleset h : NODE do
startstate "Init"
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.HeadPtr := h;
  Sta.Dir.HomeHeadPtr := true;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.WbMsg.Proc := h;
  Sta.WbMsg.HomeProc := true;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.Proc := h;
  Sta.ShWbMsg.HomeProc := true;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.UniMsg[p].Proc := h;
    Sta.UniMsg[p].HomeProc := true;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  end;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.Proc := h;
  Sta.HomeUniMsg.HomeProc := true;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeRpMsg.Cmd := RP_None;
endstartstate;
endruleset;



ruleset src : NODE do
rule "PI_Remote_Get"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_Get;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_Get_Get"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
begin
  Sta.HomeProc.ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_Get;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_Get_Put"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
begin
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked) then
    Sta.HomeProc.InvMarked := false;
    Sta.HomeProc.CacheState := CACHE_I;
  else
    Sta.HomeProc.CacheState := CACHE_S;
  end;
endrule;

ruleset src : NODE do
rule "PI_Remote_GetX"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_GetX;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_GetX_GetX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
begin
  Sta.HomeProc.ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_GetX;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_GetX_PutX_HeadVld"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty & Sta.Dir.HeadVld
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;

  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;

  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;

  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty & !Sta.Dir.HeadVld
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;

  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

ruleset dst : NODE do
rule "PI_Remote_PutX"
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.WbMsg.Cmd := WB_Wb;
  Sta.WbMsg.Proc := dst;
  Sta.WbMsg.HomeProc := false;
endrule;
endruleset;

rule "PI_Local_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_E
==>
begin
  if (Sta.Dir.Pending) then
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.Dir.Dirty := false;
  else
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := false;
  end;
endrule;

ruleset src : NODE do
rule "PI_Remote_Replace"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S
==>
begin
  Sta.Proc[src].CacheState := CACHE_I;
  Sta.RpMsg[src].Cmd := RP_Replace;
endrule;
endruleset;

rule "PI_Local_Replace"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_S
==>
begin
  Sta.Dir.Local := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;

ruleset dst : NODE do
rule "NI_Nak"
  Sta.UniMsg[dst].Cmd = UNI_Nak
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
endrule;
endruleset;

rule "NI_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_Nak
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
endrule;

rule "NI_Nak_Clear"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
begin
  Sta.NakcMsg.Cmd := NAKC_None;
  Sta.Dir.Pending := false;
endrule;

ruleset src : NODE do
rule "NI_Local_Get_Nak"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc &
  Sta.RpMsg[src].Cmd != RP_Replace &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr)
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Get"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local &
  (Sta.Dir.HeadPtr != src | Sta.Dir.HomeHeadPtr)
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put_Head"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[src] := true;
  for p : NODE do
    if (p = src)  then
      Sta.Dir.InvSet[p] := true;
    else
      Sta.Dir.InvSet[p] := Sta.Dir.ShrSet[p];
    end;
  end;
  Sta.Dir.HomeInvSet := Sta.Dir.HomeShrSet;
  Sta.UniMsg[src].Cmd := UNI_Put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & !Sta.Dir.HeadVld
==>
begin
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := src;
    Sta.Dir.HomeHeadPtr := false;
    Sta.UniMsg[src].Cmd := UNI_Put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put_Dirty"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState = CACHE_E
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.HomeProc.CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Nak"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst & !Sta.UniMsg[src].HomeProc &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_Get_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = dst & !Sta.HomeUniMsg.HomeProc &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Put"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst & !Sta.UniMsg[src].HomeProc &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := src;
  Sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_Get_Put_Home"
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = dst & !Sta.HomeUniMsg.HomeProc &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.HomeUniMsg.Cmd := UNI_Put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_Nak"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr)
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_GetX"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local &
  (Sta.Dir.HeadPtr != src | Sta.Dir.HomeHeadPtr)
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.UniMsg[src].HomeProc := Sta.Dir.HomeHeadPtr;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_1"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & !Sta.Dir.HeadVld & Sta.Dir.Local & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_2"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & !Sta.Dir.HeadVld & Sta.Dir.Local & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_3"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & !Sta.Dir.HeadVld & !Sta.Dir.Local
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_4"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr & !Sta.Dir.HomeShrSet &
  forall p : NODE do p != src -> !Sta.Dir.ShrSet[p] end &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_5"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr & !Sta.Dir.HomeShrSet &
  forall p : NODE do p != src -> !Sta.Dir.ShrSet[p] end &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_6"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr & !Sta.Dir.HomeShrSet &
  forall p : NODE do p != src -> !Sta.Dir.ShrSet[p] end &
  !Sta.Dir.Local
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_7"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & (Sta.Dir.HeadPtr != src | Sta.Dir.HomeHeadPtr) &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_7_NODE_Get"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & (Sta.Dir.HeadPtr != src | Sta.Dir.HomeHeadPtr) &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_8_Home"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.HomeShrSet &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_8_Home_NODE_Get"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.HomeShrSet &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_8"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.ShrSet[pp] &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_8_NODE_Get"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.ShrSet[pp] &
  Sta.Dir.Local & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_9"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & (Sta.Dir.HeadPtr != src | Sta.Dir.HomeHeadPtr) &
  !Sta.Dir.Local
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_10_Home"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.HomeShrSet &
  !Sta.Dir.Local
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_10"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  !Sta.Dir.Dirty & Sta.Dir.HeadVld & Sta.Dir.HeadPtr = src & !Sta.Dir.HomeHeadPtr &
  Sta.Dir.ShrSet[pp] &
  !Sta.Dir.Local
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
           Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p & !Sta.Dir.HomeHeadPtr) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[src].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_11"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc &
  !Sta.Dir.Pending &
  Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState = CACHE_E
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_Nak"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst & !Sta.UniMsg[src].HomeProc &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_GetX_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = dst & !Sta.HomeUniMsg.HomeProc &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_PutX"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst & !Sta.UniMsg[src].HomeProc &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := src;
  Sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_GetX_PutX_Home"
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = dst & !Sta.HomeUniMsg.HomeProc &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.HomeUniMsg.Cmd := UNI_PutX;
endrule;
endruleset;

rule "NI_Local_Put"
  Sta.HomeUniMsg.Cmd = UNI_Put
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked) then
    Sta.HomeProc.InvMarked := false;
    Sta.HomeProc.CacheState := CACHE_I;
  else
    Sta.HomeProc.CacheState := CACHE_S;
  end;
endrule;

ruleset dst : NODE do
rule "NI_Remote_Put"
  Sta.UniMsg[dst].Cmd = UNI_Put
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  if (Sta.Proc[dst].InvMarked) then
    Sta.Proc[dst].InvMarked := false;
    Sta.Proc[dst].CacheState := CACHE_I;
  else
    Sta.Proc[dst].CacheState := CACHE_S;
  end;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone"
  Sta.HomeUniMsg.Cmd = UNI_PutX
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := true;
  Sta.Dir.HeadVld := false;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

ruleset dst : NODE do
rule "NI_Remote_PutX"
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  Sta.Proc[dst].CacheState := CACHE_E;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Inv"
  Sta.InvMsg[dst].Cmd = INV_Inv
==>
begin
  Sta.InvMsg[dst].Cmd := INV_InvAck;
  Sta.Proc[dst].CacheState := CACHE_I;
  if (Sta.Proc[dst].ProcCmd = NODE_Get) then
    Sta.Proc[dst].InvMarked := true;
  end;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_exists_Home"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src] &
  Sta.Dir.HomeInvSet
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_InvAck_exists"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src] &
  (pp != src & Sta.Dir.InvSet[pp])
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_1"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src] &
  Sta.Dir.Local & !Sta.Dir.Dirty &
  !Sta.Dir.HomeInvSet & forall p : NODE do p = src | !Sta.Dir.InvSet[p] end
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_2"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src] &
  !Sta.Dir.Local &
  !Sta.Dir.HomeInvSet & forall p : NODE do p = src | !Sta.Dir.InvSet[p] end
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_3"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src] &
  Sta.Dir.Dirty &
  !Sta.Dir.HomeInvSet & forall p : NODE do p = src | !Sta.Dir.InvSet[p] end
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
endrule;
endruleset;

rule "NI_Wb"
  Sta.WbMsg.Cmd = WB_Wb
==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
endrule;

rule "NI_FAck"
  Sta.ShWbMsg.Cmd = SHWB_FAck
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  if (Sta.Dir.Dirty) then
    Sta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
    Sta.Dir.HomeHeadPtr := Sta.ShWbMsg.HomeProc;
  end;
endrule;

rule "NI_ShWb"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if (p = Sta.ShWbMsg.Proc & !Sta.ShWbMsg.HomeProc) | Sta.Dir.ShrSet[p] then
      Sta.Dir.ShrSet[p] := true;
      Sta.Dir.InvSet[p] := true;
    else
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    end;
  end;
  if (Sta.ShWbMsg.HomeProc | Sta.Dir.HomeShrSet) then
    Sta.Dir.HomeShrSet := true;
    Sta.Dir.HomeInvSet := true;
  else
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
  end;
endrule;

ruleset src : NODE do
rule "NI_Replace"
  Sta.RpMsg[src].Cmd = RP_Replace
==>
begin
  Sta.RpMsg[src].Cmd := RP_None;
  if (Sta.Dir.ShrVld) then
    Sta.Dir.ShrSet[src] := false;
    Sta.Dir.InvSet[src] := false;
  end;
endrule;
endruleset;

rule "NI_Replace_Home"
  Sta.HomeRpMsg.Cmd = RP_Replace
==>
begin
  Sta.HomeRpMsg.Cmd := RP_None;
  if (Sta.Dir.ShrVld) then
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
  end;
endrule;

