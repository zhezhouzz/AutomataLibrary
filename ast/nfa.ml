open Zzdatatype.Datatype

type state = int64

module StateSet = Set.Make (Int64)
module StateMap = Map.Make (Int64)

module type CHARAC = sig
  include Map.OrderedType

  val layout : t -> string
  val delimit_cotexnt_char : t list option * t -> t list
end

module type CHARACTER = sig
  include CHARAC

  type char_idx

  val layout : t -> string
  val init_char_map : unit -> char_idx
  val add_char_to_map : char_idx -> t -> unit
  val id2c : char_idx -> Int64.t -> t
  val c2id : char_idx -> t -> Int64.t
end

module type AUTOMATA = sig
  module C : CHARACTER
  module CharMap : Map.S with type key = C.t

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : state -> transitions;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : state -> d_transition;
  }
end
