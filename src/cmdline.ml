
open Core.Std
open Utils
open Client

let confirm_with_mu =  ref false

let open_debug () = debug_switch := true

let set_smv_server_host host () =
  Smv.host := UnixLabels.inet_addr_of_string host

let set_smv_server_port port () =
  Smv.port := port

let set_smv_bmc_server_host host () =
  SmvBMC.host := UnixLabels.inet_addr_of_string host

let set_smv_bmc_server_port port () =
  SmvBMC.port := port

let set_smt_server_host host () =
  Smt2.host := UnixLabels.inet_addr_of_string host

let set_smt_server_port port () =
  Smt2.port := port

let set_mu_server_host host () =
  Murphi.host := UnixLabels.inet_addr_of_string host

let set_mu_server_port port () =
  Murphi.port := port

let command program =
  Command.basic
    ~summary:"Find invariants of parameterized systems."
    Command.Spec.(
      empty
      +> flag "-g" no_arg ~doc:"open debuG mode"
      +> flag "-C" no_arg ~doc:"Confirm inv checked by NuSMV through Murphi"
      +> flag "-vh" (optional string) ~doc:"set ip address as Host of smV server"
      +> flag "-vp" (optional int) ~doc:"set Port of smV server"
      +> flag "-vbh" (optional string) ~doc:"set ip address as Host of smV Bmc server"
      +> flag "-vbp" (optional int) ~doc:"set Port of smV Bmc server"
      +> flag "-th" (optional string) ~doc:"set ip address as Host of smT server"
      +> flag "-tp" (optional int) ~doc:"set Port of smT server"
      +> flag "-mh" (optional string) ~doc:"set ip address as Host of Murphi server"
      +> flag "-mp" (optional int) ~doc:"set Port of Murphi server"
    )
    (fun g c vh vp vbh vbp th tp mh mp () ->
      begin
        match g with
        | true -> open_debug ()
        | false  -> ()
      end;
      begin
        match c with
        | true -> confirm_with_mu := true
        | false  -> ()
      end;
      begin
        match vh with
        | Some host -> set_smv_server_host host ()
        | None -> ()
      end;
      begin
        match vp with
        | Some port -> set_smv_server_port port ()
        | None -> ()
      end;
      begin
        match vbh with
        | Some host -> set_smv_bmc_server_host host ()
        | None -> ()
      end;
      begin
        match vbp with
        | Some port -> set_smv_bmc_server_port port ()
        | None -> ()
      end;
      begin
        match th with
        | Some host -> set_smt_server_host host ()
        | None -> ()
      end;
      begin
        match tp with
        | Some port -> set_smt_server_port port ()
        | None -> ()
      end;
      begin
        match mh with
        | Some host -> set_mu_server_host host ()
        | None -> ()
      end;
      begin
        match mp with
        | Some port -> set_mu_server_port port ()
        | None -> ()
      end;
      program ()
    )

let run_with_cmdline program = Command.run (command program)
