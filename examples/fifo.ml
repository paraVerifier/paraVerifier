


open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline

let _True = boolc true
let _False = boolc false


let types = [
  enum "value_type" (int_consts (up_to 16));
  enum "depth_type" (int_consts (up_to 16));
  enum "addr_type" (int_consts (up_to 4));
  enum "boolean" [_True; _False];
]

let vardefs = List.concat [
  [arrdef [("mem", [paramdef "i0" "depth_type"])] "value_type"];
  [arrdef [("tmp", [paramdef "i1" "depth_type"])] "value_type"];
  [arrdef [("tail", [])] "depth_type"];
  [arrdef [("empty", [])] "boolean"];
]

let init = parallel [
  forStatement (
    assign (arr [("mem", [paramref "i"])]) (const (intc 0))
  ) [paramdef "i" "depth_type"];
  assign (global "tail") (const (intc 0));
  assign (global "empty") (const (boolc true));
]


let always =
  let name = "always" in
  let params = [
    paramdef "dataIn" "value_type";
    paramdef "rst" "boolean";
    paramdef "push" "boolean";
    paramdef "pop" "boolean";
  ] in
  let formula = chaos in
  let statement = ifelseStatement (
    eqn (param (paramref "rst")) (const (boolc true))
  ) (parallel [
    assign (global "tail") (const (intc 0));
    assign (global "empty") (const (boolc true));
  ]) (
    ifelseStatement (
      andList [
        eqn (param (paramref "push")) (const (boolc true));
        neg (eqn (var (global "tail")) (const (intc 15)))
      ]
    ) (
      parallel [
        forStatement (parallel [
          assign (
            arr [("mem", [paramref "i"])]
          ) (
            ite (
              eqn (param (paramref "i")) (const (intc 0))
            ) (
              param (paramref "dataIn")
            ) (
              read (
                arrdef [("mem", [paramdef "i1" "depth_type"])] "depth_type"
              ) (
                uif "-" [param (paramref "i"); const (intc 1)]
              ) types
            )
          );
          ifStatement (
            uip ">" [param (paramref "i"); const (intc 0)]
          ) (
            write (
              arrdef [("tmp", [paramdef "i0" "depth_type"])] "depth_type"
            ) (
              uif "-" [param (paramref "i"); const (intc 1)]
            ) (
              var (arr [("mem", [paramref "i"])])
            ) types
          );
        ]) [paramdef "i" "depth_type"];
        ifStatement (
          eqn (var (global "empty")) (const (boolc true))
        ) (
          assign (global "tail") (uif "+" [var (global "tail"); const (intc 1)])
        );
        assign (global "empty") (const (boolc false))
      ]
    ) (
      ifStatement (
        andList [
          eqn (param (paramref "pop")) (const (boolc true));
          eqn (var (global "empty")) (const (boolc false))
        ]
      ) (
        ifelseStatement (
          eqn (var (global "tail")) (const (intc 0))
        ) (
          assign (global "empty") (const (boolc true))
        ) (
          assign (global "tail") (uif "-" [var (global "tail"); (const (intc 1))])
        )
      )
    )
  ) in
  rule name params formula statement


let rules = [always]

let coherent =
  let name = "coherent" in
  let params = [] in
  let formula = imply (
    eqn (var (global "tail")) (const (intc 15))
  ) (
    eqn (var (global "empty")) (const (boolc false))
  ) in
  prop name params formula

let properties = [coherent]

let protocol = {
  name = "fifo";
  types;
  vardefs;
  init;
  rules;
  properties;
}



let () = run_with_cmdline (fun () ->
  let insym_types = ["value_type"; "depth_type"; "addr_type"; "boolean"] in
  let protocol = PartParam.apply_protocol insym_types protocol in
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "fifo.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)


