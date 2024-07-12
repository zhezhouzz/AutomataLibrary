open Common

type 'a regex =
  | EmptyA
  | EpsilonA
  | AnyA
  | Atomic of 'a
  | LorA of 'a regex * 'a regex
  | LandA of 'a regex * 'a regex
  | SeqA of 'a regex * 'a regex
  | StarA of 'a regex
  | ComplementA of 'a regex
  | SetMinusA of 'a regex * 'a regex
[@@deriving sexp]
