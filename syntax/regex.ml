open Ast

let rec desugar regex =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ -> regex
  | LorA (r1, r2) -> LorA (desugar r1, desugar r2)
  | LandA (r1, r2) -> LandA (desugar r1, desugar r2)
  | SeqA (r1, r2) -> SeqA (desugar r1, desugar r2)
  | StarA r -> StarA (desugar r)
  | ComplementA r -> ComplementA (desugar r)
  | SetMinusA (r1, r2) -> LandA (desugar r1, ComplementA (desugar r2))

(* let rec to_dnf  *)

let rec to_nnf (regex : 'a regex) : 'a regex =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ -> regex
  | LorA (r1, r2) -> LorA (to_nnf r1, to_nnf r2)
  | LandA (r1, r2) -> LandA (to_nnf r1, to_nnf r2)
  | SeqA (r1, r2) -> SeqA (to_nnf r1, to_nnf r2)
  | StarA r -> StarA (to_nnf r)
  | ComplementA r -> negate r
  | SetMinusA _ -> failwith "die"

and negate regex =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ -> ComplementA regex
  | LorA (r1, r2) -> LandA (negate r1, negate r2)
  | LandA (r1, r2) -> LorA (negate r1, negate r2)
  | SeqA (r1, r2) -> ComplementA (SeqA (to_nnf r1, to_nnf r2))
  | StarA r -> SeqA (SeqA (StarA AnyA, negate r), StarA AnyA)
  | ComplementA r -> to_nnf r
  | SetMinusA _ -> failwith "die"

let rec to_cnf (regex : 'a regex) : 'a regex list =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ -> [ regex ]
  | LorA (r1, r2) ->
      let rs1 = to_cnf r1 in
      let rs2 = to_cnf r2 in
      let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in
      List.map (fun (r1, r2) -> LorA (r1, r2)) rs
  | LandA (r1, r2) -> to_cnf r1 @ to_cnf r2
  | SeqA (r1, r2) ->
      let rs1 = to_cnf r1 in
      let rs2 = to_cnf r2 in
      let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in
      List.map (fun (r1, r2) -> SeqA (r1, r2)) rs
  | StarA r ->
      let rs = to_cnf r in
      List.map (fun r -> StarA r) rs
  | ComplementA r -> List.map negate (to_dnf r)
  | SetMinusA _ -> failwith "die"

and to_dnf (regex : 'a regex) : 'a regex list =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ -> [ regex ]
  | LorA (r1, r2) -> to_dnf r1 @ to_dnf r2
  | LandA (r1, r2) ->
      let rs1 = to_dnf r1 in
      let rs2 = to_dnf r2 in
      let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in
      List.map (fun (r1, r2) -> LandA (r1, r2)) rs
  | SeqA (r1, r2) ->
      let rs1 = to_dnf r1 in
      let rs2 = to_dnf r2 in
      let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in
      List.map (fun (r1, r2) -> SeqA (r1, r2)) rs
  | StarA _ -> failwith "die"
  | ComplementA r -> List.map negate (to_cnf r)
  | SetMinusA _ -> failwith "die"

let mk_any (ctx : 'a list) =
  match ctx with
  | [] -> failwith "die"
  | a :: ctx -> List.fold_left (fun r b -> LorA (r, Atomic b)) (Atomic a) ctx

let limit_context (ctx : 'a list) (regex : 'a regex) : 'a regex =
  let rec aux regex =
    match regex with
    | AnyA -> mk_any ctx
    | EmptyA | EpsilonA | Atomic _ -> regex
    | ComplementA EmptyA -> StarA (mk_any ctx)
    | ComplementA EpsilonA -> SeqA (mk_any ctx, StarA (mk_any ctx))
    | ComplementA (Atomic a) ->
        let others =
          mk_any (List.filter (fun b -> 0 != Stdlib.compare a b) ctx)
        in
        LorA (StarA others, SeqA (Atomic a, StarA (mk_any ctx)))
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA (r1, r2) -> SeqA (aux r1, aux r2)
    | StarA r -> StarA (aux r)
    | ComplementA r -> ComplementA r
    | SetMinusA (a, b) -> SetMinusA (aux a, aux b)
  in
  aux regex
