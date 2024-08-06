open Common
open Zzdatatype.Datatype

module type FINITE_AUTOMATA = sig
  module C : CHARACTER
  module CharMap : Map.S with type key = C.t
  module EpsCharMap : Map.S with type key = C.t option

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t
  type eps_transitions = StateSet.t EpsCharMap.t

  type 'c raw_regex =
    | Empty : 'c raw_regex (* L = { } *)
    | Eps : 'c raw_regex (* L = {ε} *)
    | MultiChar : 'c list -> 'c raw_regex
    | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Inters : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Comple : 'c list * 'c raw_regex -> 'c raw_regex
    | Seq : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Star : 'c raw_regex -> 'c raw_regex

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : transitions StateMap.t;
  }

  type eps_nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : eps_transitions StateMap.t;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : d_transition StateMap.t;
  }
end
