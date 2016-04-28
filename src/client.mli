(** Client for connect to smv/smt2 server
*)

exception Server_exception

module Smv : sig
  exception Cannot_check
  val host : UnixLabels.inet_addr ref
  val port : int ref
  val compute_reachable : string -> string -> bool
  val query_reachable : string -> int
  val check_inv : string -> string -> bool
  val quit : string -> bool
end

module SmvBMC : sig
  exception Cannot_check
  val host : UnixLabels.inet_addr ref
  val port : int ref
  val go_bmc : string -> string -> bool
  val check_inv : string -> string -> bool
  val quit : string -> bool
end

module Murphi : sig
  val host : UnixLabels.inet_addr ref
  val port : int ref
  val set_context : string -> string -> bool
  val check_inv : string -> string -> bool
end

module Smt2 : sig
  val host : UnixLabels.inet_addr ref
  val port : int ref
  val set_context : string -> string -> bool
  val check : string -> string -> bool
  val check_stand : string -> string -> bool
end



