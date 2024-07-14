open Common
open Sexplib.Std

type 'a regex =
  | EmptyA
  | EpsilonA
  | Atomic of 'a
  | LorA of 'a regex * 'a regex
  | LandA of 'a regex * 'a regex
  | SeqA of 'a regex * 'a regex
  | StarA of 'a regex
  | DComplementA of { atoms : 'a list; body : 'a regex }
  | MultiAtomic of 'a list
  (* the rest are extend fields *)
  | AnyA
  | ComplementA of 'a regex
  | Ctx of { atoms : 'a list; body : 'a regex }
  | CtxOp of { op_names : string list; body : 'a regex }
  (* a syntax sugar *)
  | SetMinusA of 'a regex * 'a regex
[@@deriving sexp]

type 'c raw_regex =
  | Empty : 'c raw_regex
  | Eps : 'c raw_regex
  | Char : 'c -> 'c raw_regex
  | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex
  | Seq : 'c raw_regex * 'c raw_regex -> 'c raw_regex
  | Star : 'c raw_regex -> 'c raw_regex
[@@deriving sexp]

let map_label_in_regex (type a b) (f : a -> b) (regex : a regex) : b regex =
  let rec aux regex =
    match regex with
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | AnyA -> AnyA
    | Atomic c -> Atomic (f c)
    | MultiAtomic cs -> MultiAtomic (List.map f cs)
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA (r1, r2) -> SeqA (aux r1, aux r2)
    | StarA r -> StarA (aux r)
    | ComplementA r -> ComplementA (aux r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms = List.map f atoms; body = aux body }
    | SetMinusA (r1, r2) -> SetMinusA (aux r1, aux r2)
    | CtxOp { op_names; body } -> CtxOp { op_names; body = aux body }
    | Ctx { atoms; body } -> Ctx { atoms = List.map f atoms; body = aux body }
  in
  aux regex

let iter_label_in_regex (type a) (f : a -> unit) (regex : a regex) : unit =
  let _ = map_label_in_regex f regex in
  ()
