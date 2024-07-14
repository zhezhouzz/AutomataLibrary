open Ast
open Zzdatatype.Datatype

let labels_to_multiatomic ls =
  let ls = List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) ls in
  match ls with [] -> EmptyA | [ e ] -> Atomic e | _ -> MultiAtomic ls

let rec desugar regex =
  match regex with
  | EmptyA | EpsilonA | AnyA | Atomic _ | MultiAtomic _ -> regex
  | LorA (r1, r2) -> (
      match (desugar r1, desugar r2) with
      | StarA AnyA, _ | _, StarA AnyA -> StarA AnyA
      | EmptyA, r2 -> r2
      | r1, EmptyA -> r1
      | r1, r2 -> LorA (r1, r2))
  | LandA (r1, r2) -> (
      match (desugar r1, desugar r2) with
      | EmptyA, _ | _, EmptyA -> StarA AnyA
      | StarA AnyA, r2 -> r2
      | r1, StarA AnyA -> r1
      | r1, r2 -> LandA (r1, r2))
  | SeqA (r1, r2) -> SeqA (desugar r1, desugar r2)
  | StarA r -> StarA (desugar r)
  | ComplementA r -> ComplementA (desugar r)
  | DComplementA { atoms; body } -> DComplementA { atoms; body = desugar body }
  | SetMinusA (r1, r2) -> desugar (LandA (desugar r1, ComplementA (desugar r2)))
  | CtxOp { op_names; body } -> CtxOp { op_names; body = desugar body }
  | Ctx { atoms; body } -> Ctx { atoms; body = desugar body }

(* let rec to_dnf  *)

(* let rec to_nnf (regex : 'a regex) : 'a regex = *)
(*   match regex with *)
(*   | EmptyA | EpsilonA | AnyA | Atomic _ -> regex *)
(*   | LorA (r1, r2) -> LorA (to_nnf r1, to_nnf r2) *)
(*   | LandA (r1, r2) -> LandA (to_nnf r1, to_nnf r2) *)
(*   | SeqA (r1, r2) -> SeqA (to_nnf r1, to_nnf r2) *)
(*   | StarA r -> StarA (to_nnf r) *)
(*   | ComplementA r -> negate r *)
(*   | SetMinusA _ -> failwith "die" *)

(* and negate regex = *)
(*   match regex with *)
(*   | EmptyA | EpsilonA | AnyA | Atomic _ -> ComplementA regex *)
(*   | LorA (r1, r2) -> LandA (negate r1, negate r2) *)
(*   | LandA (r1, r2) -> LorA (negate r1, negate r2) *)
(*   | SeqA (r1, r2) -> ComplementA (SeqA (to_nnf r1, to_nnf r2)) *)
(*   | StarA r -> SeqA (SeqA (StarA AnyA, negate r), StarA AnyA) *)
(*   | ComplementA r -> to_nnf r *)
(*   | SetMinusA _ -> failwith "die" *)

(* let rec to_cnf (regex : 'a regex) : 'a regex list = *)
(*   match regex with *)
(*   | EmptyA | EpsilonA | AnyA | Atomic _ -> [ regex ] *)
(*   | LorA (r1, r2) -> *)
(*       let rs1 = to_cnf r1 in *)
(*       let rs2 = to_cnf r2 in *)
(*       let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in *)
(*       List.map (fun (r1, r2) -> LorA (r1, r2)) rs *)
(*   | LandA (r1, r2) -> to_cnf r1 @ to_cnf r2 *)
(*   | SeqA (r1, r2) -> *)
(*       let rs1 = to_cnf r1 in *)
(*       let rs2 = to_cnf r2 in *)
(*       let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in *)
(*       List.map (fun (r1, r2) -> SeqA (r1, r2)) rs *)
(*   | StarA r -> *)
(*       let rs = to_cnf r in *)
(*       List.map (fun r -> StarA r) rs *)
(*   | ComplementA r -> List.map negate (to_dnf r) *)
(*   | SetMinusA _ -> failwith "die" *)

(* and to_dnf (regex : 'a regex) : 'a regex list = *)
(*   match regex with *)
(*   | EmptyA | EpsilonA | AnyA | Atomic _ -> [ regex ] *)
(*   | LorA (r1, r2) -> to_dnf r1 @ to_dnf r2 *)
(*   | LandA (r1, r2) -> *)
(*       let rs1 = to_dnf r1 in *)
(*       let rs2 = to_dnf r2 in *)
(*       let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in *)
(*       List.map (fun (r1, r2) -> LandA (r1, r2)) rs *)
(*   | SeqA (r1, r2) -> *)
(*       let rs1 = to_dnf r1 in *)
(*       let rs2 = to_dnf r2 in *)
(*       let rs = Zzdatatype.Datatype.List.cross rs1 rs2 in *)
(*       List.map (fun (r1, r2) -> SeqA (r1, r2)) rs *)
(*   | StarA _ -> failwith "die" *)
(*   | ComplementA r -> List.map negate (to_cnf r) *)
(*   | SetMinusA _ -> failwith "die" *)

let delimit_context (regex : 'a regex) : 'a regex =
  let ctx, regex =
    match regex with
    | Ctx { atoms; body } -> (Some atoms, body)
    | _ -> (None, regex)
  in
  let force_ctx = function
    | None ->
        _failatwith __FILE__ __LINE__
          "the regex need to be quantified with a context of chars."
    | Some ctx -> ctx
  in
  let rec aux ctx regex =
    match regex with
    | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
    | ComplementA EmptyA -> StarA (MultiAtomic (force_ctx ctx))
    | ComplementA EpsilonA ->
        SeqA (MultiAtomic (force_ctx ctx), StarA (MultiAtomic (force_ctx ctx)))
    | ComplementA (Atomic a) ->
        let others =
          MultiAtomic
            (List.filter (fun b -> 0 != Stdlib.compare a b) (force_ctx ctx))
        in
        LorA (StarA others, SeqA (Atomic a, StarA (MultiAtomic (force_ctx ctx))))
    | DComplementA { atoms; body } ->
        DComplementA { atoms; body = aux (Some atoms) body }
    | LorA (r1, r2) -> LorA (aux ctx r1, aux ctx r2)
    | LandA (r1, r2) -> LandA (aux ctx r1, aux ctx r2)
    | SeqA (r1, r2) -> SeqA (aux ctx r1, aux ctx r2)
    | StarA r -> StarA (aux ctx r)
    (* the rest are extend fields *)
    | AnyA -> MultiAtomic (force_ctx ctx)
    | ComplementA r -> DComplementA { atoms = force_ctx ctx; body = aux ctx r }
    | Ctx { atoms; body } -> aux (Some atoms) body
    | SetMinusA _ | CtxOp _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux ctx regex

let gather_regex regex =
  let rec aux regex m =
    match regex with
    | EmptyA -> m
    | AnyA -> m
    | EpsilonA -> m
    | Atomic se -> Sevent.gather_se m se
    | LorA (t1, t2) -> aux t1 @@ aux t2 m
    | SetMinusA (t1, t2) -> aux t1 @@ aux t2 m
    | LandA (t1, t2) -> aux t1 @@ aux t2 m
    | SeqA (t1, t2) -> aux t1 @@ aux t2 m
    | StarA t -> aux t m
    | ComplementA t -> aux t m
    | MultiAtomic se -> List.fold_left Sevent.gather_se m se
    | Ctx { atoms; body } ->
        let m = List.fold_left Sevent.gather_se m atoms in
        aux body m
    | DComplementA _ | CtxOp _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux regex (Sevent.gathered_lits_init ())
