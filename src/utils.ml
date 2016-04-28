(** This library provides some useful functions
*)

open Core.Std

(*----------------------------- Switches ----------------------------------*)

let debug_switch = ref false;

(*----------------------------- Exceptions ----------------------------------*)

(* This exception is for stop warnings. It will never be raised. *)
exception Empty_exception

(** Exception raised when could not find something *)
exception Cannot_find of string

(*----------------------------- Functions ----------------------------------*)

let up_to n =
  let rec wrapper n res =
    match n with
    | 0 -> res
    | _ -> wrapper (n - 1) ((n - 1)::res)
  in
  wrapper n []

(** Generate the permutation of a list *)
let rec permutation list =
  match list with
  | [] -> []
  | _ ->
    let remove_at list len i = 
      let head = List.sub list ~pos:0 ~len:i in 
      let tail = List.sub list ~pos:(i + 1) ~len:(len - i - 1) in
      if head@tail = [] then
        [List.sub list ~pos:i ~len:1]
      else begin
        List.map (permutation (head@tail)) ~f:(fun x -> (List.sub list ~pos:i ~len:1)@x)
      end
    in
    let len = List.length list in
    List.map (up_to len) ~f:(remove_at list len)
    |> List.concat

(** Generate the combination of a list *)
let rec combination list n =
  match list with
  | [] -> []
  | ele::list' ->
    let len = List.length list in
    if len < n then
      []
    else begin
      match n with
      | 0 -> []
      | 1 -> List.map list ~f:(fun x -> [x])
      | _ ->
        let first_set = List.map (combination list' (n - 1)) ~f:(fun x -> ele::x) in
        first_set@(combination list' n)
    end

(** Generate all combinations of a list *)
let combination_all list =
  let nums = List.map (up_to (List.length list)) ~f:(fun x -> x + 1) in
  List.concat (List.map nums ~f:(fun n -> combination list n))


(** Combination firstly and permutation for each element of the combination *)
let combination_permutation list n =
  combination list n
  |> List.map ~f:permutation
  |> List.concat

(** Generate Cartesian Production of a set of lists
    For example, given [[1;2]; [1;3]] produces [[1;1]; [1;3]; [2;1]; [2;3]]

    @param list the given set of lists, whose elements will be omitted if it is []
    @return the generated Cartesian Production
*)
let cartesian_product list =
  let append_all alist ele = List.map ~f:(fun x -> x@[ele]) alist in
  let com_next res b =
    match (res, b) with
    | (res, []) -> res
    | ([], b) -> List.map ~f:(fun x -> [x]) b
    | _ -> List.concat (List.map ~f:(append_all res) b)
  in
  List.fold ~init:[] ~f:com_next list

(** Judge if all elements in list satisfy function f

    @param the list
    @param f a function maps elements in list to bool
    @return true if satisfy else false
*)
let all list ~f =
  list
  |> List.map ~f
  |> List.fold ~f:(fun res x -> res && x) ~init:true

(** Judge if any elements in list satisfies function f

    @param the list
    @param f a function maps elements in list to bool
    @return true if satisfies else false
*)
let any list ~f =
  list
  |> List.map ~f
  |> List.fold ~f:(fun res x -> res || x) ~init:false

(** Reduce a list, if the list is empty, a default value is returned *)
let reduce list ~default ~f =
  match List.reduce list ~f with
  | Some(x) -> x
  | None -> default

let rm_from_list ls ~f =
  let rec wrapper ls res =
    match ls with
    | [] -> res
    | i::ls' ->
      if f i then wrapper ls' res else wrapper ls' (res@[i])
  in
  wrapper ls []

(** Partition a list to a set of labeled lists, with function f
    e.g., for list [1;2;3;4;5;6] and function (fun x -> x mod 3),
    generate list [(1, [1;4]); (2, [2;5]); (0, [3;6])]
*)
let partition_with_label list ~f =
  let rec wrapper list assoc =
    match list with
    | [] -> assoc
    | ele::list' ->
      let value = f ele in (
        match List.Assoc.find assoc value with
        | None -> wrapper list' (List.Assoc.add assoc value [ele])
        | Some(v) ->
          let assoc' = List.Assoc.remove assoc value in
          wrapper list' (List.Assoc.add assoc' value (ele::v))
      )
  in
  wrapper (List.rev list) []

(** Partition a list to a set of lists, with function f
    e.g., for list [1;2;3;4;5;6] and function (fun x -> x mod 3),
    generate list [[1;4]; [2;5]; [3;6]]
*)
let partition list ~f =
  let assoc = partition_with_label list ~f in
  List.map assoc ~f:(fun (_, v) -> v)


let rec stupid_dedup_list ls ~f =
  match ls with
  | [] -> []
  | ele::ls' ->
    let tail = stupid_dedup_list ls' ~f in
    if List.exists ls' ~f:(fun x -> f x ele) then tail else ele::tail


let string_replace s d =
  Re2.Regex.rewrite_exn (Re2.Regex.of_string s) ~template:d












(** Denotes there are errors while execute a program *)
exception Exec_error

(* Generate a new string buffer with size *)
let new_str_buf size =
  let buf = String.create size in
  String.fill buf ~pos:0 ~len:size '\000';
  buf

(* Read all contents in a filedsr *)
let read_to_end filedsr =
  let rec read filedsr results =
    let buf = new_str_buf 1024 in
    let size = Unix.read filedsr ~buf in
    if size = 0 then
      results
    else
      read filedsr ((String.sub buf ~pos:0 ~len:size)::results)
  in
  let res = String.concat (List.rev (read filedsr [])) in
  Unix.close filedsr; res

(** Execute a program with some arguments then fetch the output.
    This function will block the main process.

    @param prog the program to be executed
    @param args arguments
    @return stdout string
*)
let exec ~prog ~args =
  let open Unix.Process_info in
  let sub = Unix.create_process ~prog ~args in
  Unix.close sub.stdin;
  (read_to_end sub.stdout, read_to_end sub.stderr)

(** Execute a program with some arguments and some input strings then fetch the output.
    This function will block the main process.

    @param prog the program to be executed
    @param args arguments
    @param input input string
    @return stdout string
*)
let exec_with_input ~prog ~args input =
  let open Unix.Process_info in
  let sub = Unix.create_process ~prog ~args in
  let size = 
    let s = Unix.write sub.stdin ~buf:input in
    Unix.close sub.stdin; s
  in
  if size = 0 then
    raise Empty_exception
  else
    (read_to_end sub.stdout, read_to_end sub.stderr)










(** Some usefule colorful print functions *)
module Prt = struct

  (** Wrong color value *)
  exception Wrong_color

  (** Basic color *)
  type basic_color =
    | Black
    | Red
    | Green
    | Yellow
    | Blue
    | Magenta
    | Cyan
    | White

  (** More color
      + Basic basic color
      + Bold bold color
      + RGB 6x6x6 color cube
      + Gray 24 grayscale levels
  *)
  type color =
    | Basic of basic_color
    | Bold of basic_color
    | RGB of int * int * int
    | Gray of int

  let basic c = Basic c
  let bold c = Bold c
  let rgb r g b =
    let in_range i = i >= 0 && i < 6 in
    if in_range r && in_range g && in_range b then
      RGB (r, g, b)
    else
      raise Wrong_color
  let gray i = if i >=0 && i < 24 then Gray i else raise Wrong_color

  (* Cast basic color to integer representation in terminal color *)
  let basic_color_to_int = function
    | Black -> 0
    | Red -> 1
    | Green -> 2
    | Yellow -> 3
    | Blue -> 4
    | Magenta -> 5
    | Cyan -> 6
    | White -> 7

  (* Cast all color to integer *)
  let color_to_int = function
    | Basic basic_color -> basic_color_to_int basic_color
    | Bold basic_color -> 8 + basic_color_to_int basic_color
    | RGB (r, g, b) -> 16 + b + 6*g + 36*r
    | Gray i -> 232 + i

  (** Print colorful text on terminal

      @param text string to be printed
      @param color color of string
  *)
  let colorful ~text ~color =
    print_endline (sprintf "\027[38;5;%dm%s\027[0m" (color_to_int color) text)

  (** Print info string *)
  let info text =
    colorful ~text ~color:(basic Cyan)

  (** Print warning string *)
  let warning text =
    colorful ~text ~color:(basic Yellow)

  (** Print error string *)
  let error text =
    colorful ~text ~color:(basic Red)

end