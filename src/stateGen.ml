
open Core.Std
open Utils
open Paramecium
open InvFinder


let equal_form f g =
  Formula.is_tautology (andList [imply f g; imply g f])

let can_imply f g =
  Formula.is_tautology (imply f g)


let rec statement_2_assigns statement =
  match statement with
  | Parallel(sl) -> List.concat (List.map sl ~f:statement_2_assigns)
  | Assign(v, e) -> [(v, e)]


let bfs inits rules bound =
  let rec wrapper cur res =
    if List.length res >= bound || List.is_empty cur then
      res
    else begin
      let c::cur' = cur in
      let found = List.concat (List.map rules ~f:(fun (Rule(n, p, f, s)) ->
        let assigns = statement_2_assigns s in
        let c' = pre_cond c assigns in
        List.map c' ~f:(fun (b, g) -> Formula.simplify (andList [f; b; g]))
      )) |> List.filter ~f:(fun g -> Formula.is_satisfiable g) in
      let new_found = List.fold found ~init:[] ~f:(fun remained x ->
        match can_imply x (orList (res@remained)) with
        | true -> remained
        | false -> remained@[x]
      ) in
      wrapper (cur'@new_found) (res@new_found)
    end
  in
  wrapper inits inits






