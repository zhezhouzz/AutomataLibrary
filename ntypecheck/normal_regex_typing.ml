open Language

type t = Nt.t

let bi_regex_check (type a b) (label_check : t ctx -> a -> b) (ctx : t ctx)
    (regex : a regex) : b regex =
  let rec aux ctx regex =
    match regex with
    | EpsilonA -> EpsilonA
    | AnyA -> AnyA
    | EmptyA -> EmptyA
    | Atomic se -> Atomic (label_check ctx se)
    | LorA (t1, t2) -> LorA (aux ctx t1, aux ctx t2)
    | SetMinusA (t1, t2) -> SetMinusA (aux ctx t1, aux ctx t2)
    | LandA (t1, t2) -> LandA (aux ctx t1, aux ctx t2)
    | SeqA (t1, t2) -> SeqA (aux ctx t1, aux ctx t2)
    | StarA t -> StarA (aux ctx t)
    | ComplementA t -> ComplementA (aux ctx t)
  in
  aux ctx regex

let bi_symbolic_regex_check =
  bi_regex_check Normal_sevent_typing.bi_sevent_check

let bi_str_regex_check ctx regex = bi_regex_check (fun _ x -> x) ctx regex
