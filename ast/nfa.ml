open Zzdatatype.Datatype

type state = int64

module StateSet = Set.Make (Int64)
module StateMap = Map.Make (Int64)

module type CHARACTER = sig
  include Map.OrderedType

  val layout : t -> string
end

module type Automata = functor
  (C : CHARACTER)
  (CharMap : Map.S with type key = C.t)
  -> sig
  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : state;
    finals : StateSet.t;
    next : transitions StateMap.t;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : d_transition StateMap.t;
  }

  val nfa_accept : nfa -> C.t list -> bool

  val minimize : dfa -> dfa
  (** [minimize dfa] is a minimized dfa equivalent to the dfa [dfa],
      obtained via Brzozowski's algorithm *)

  val dfa_accept : dfa -> C.t list -> bool
  (** [accept dfa l] is [true] iff the dfa [dfa] accepts the
      character sequence [l] *)

  val determinize : nfa -> dfa
  (** [determinize nfa] is a deterministic finite automaton that
      accepts the same language as [nfa].
  *)

  val inject : dfa -> nfa
  (** [inject dfa] is the deterministic NFA corresponding to [dfa] *)

  val compile : C.t Regex.regex -> nfa
end
