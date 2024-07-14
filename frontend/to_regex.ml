open Ast
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Sugar
open To_id

let of_expr_aux label_of_expr expr =
  let parse_labels a =
    match a.pexp_desc with
    | Pexp_array es -> List.map label_of_expr es
    | _ -> _failatwith __FILE__ __LINE__ "expected an array of lables "
  in
  let parse_ids a =
    match a.pexp_desc with
    | Pexp_array es -> List.map id_of_expr es
    | _ -> _failatwith __FILE__ __LINE__ "expected an array of names "
  in
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_apply (func, args) -> (
        match (id_of_expr func, List.map snd args) with
        | "starA", [ e1 ] -> StarA (aux e1)
        | "not", [ e1 ] -> ComplementA (aux e1)
        | "mu", _ ->
            _failatwith __FILE__ __LINE__
              "the recursive automata are disallowed"
        | "||", [ a; b ] -> LorA (aux a, aux b)
        | "-", [ a; b ] -> SetMinusA (aux a, aux b)
        | "&&", [ a; b ] -> LandA (aux a, aux b)
        | "ctx", [ a; b ] ->
            let atoms = parse_labels a in
            Ctx { atoms; body = aux b }
        | "ctxOp", [ a; b ] ->
            let op_names = parse_ids a in
            CtxOp { op_names; body = aux b }
        | "range", [ a ] ->
            let atoms = parse_labels a in
            MultiAtomic atoms
        | f, _ -> _failatwith __FILE__ __LINE__ @@ spf "unknown regular op %s" f
        )
    | Pexp_sequence (a, b) -> SeqA (aux a, aux b)
    | Pexp_ident id ->
        let id = To_id.longid_to_id id in
        if String.equal "epsilonA" id then EpsilonA
        else if String.equal "emptyA" id then EmptyA
        else if String.equal "anyA" id then AnyA
        else Atomic (label_of_expr expr)
    | _ -> Atomic (label_of_expr expr)
  in
  aux expr

let of_expr label_of_expr expr =
  let rty = of_expr_aux label_of_expr expr in
  (* let rty = Syntax.RtyRaw.SRL.normalize_name rty in *)
  rty

let rec pprint_aux layout_label = function
  | EmptyA -> ("∅", true)
  | EpsilonA -> ("ϵ", true)
  | Atomic se -> (layout_label se, true)
  | MultiAtomic atoms ->
      (spf "[%s]" (List.split_by " " layout_label atoms), true)
  | LorA (a1, a2) ->
      ( spf "%s%s%s" (p_pprint layout_label a1) "∪" (p_pprint layout_label a2),
        false )
  | SetMinusA (a1, a2) ->
      (spf "%s\\%s" (p_pprint layout_label a1) (p_pprint layout_label a2), false)
  | LandA (a1, a2) ->
      ( spf "%s%s%s" (p_pprint layout_label a1) "∩" (p_pprint layout_label a2),
        false )
  | SeqA (a1, a2) ->
      (spf "%s;%s" (p_pprint layout_label a1) (p_pprint layout_label a2), false)
  | StarA AnyA -> ("•*", true)
  | StarA a -> (spf "%s*" (p_pprint layout_label a), true)
  | AnyA -> ("•", true)
  | DComplementA { atoms; body } ->
      ( spf "[%s]{%sᶜ}"
          (List.split_by " " layout_label atoms)
          (p_pprint layout_label body),
        true )
  | Ctx { atoms; body } ->
      ( spf "[%s]{%s}"
          (List.split_by " " layout_label atoms)
          (p_pprint layout_label body),
        true )
  | CtxOp { op_names; body } ->
      ( spf "[%s]{%s}"
          (List.split_by " " (fun x -> x) op_names)
          (p_pprint layout_label body),
        true )
  | ComplementA a -> (spf "%sᶜ" (p_pprint layout_label a), true)

and p_pprint layout_label a =
  let str, is_p = pprint_aux layout_label a in
  if is_p then str else spf "(%s)" str

and pprint layout_label a = fst (pprint_aux layout_label a)

let layout_regex = pprint
let layout = pprint
