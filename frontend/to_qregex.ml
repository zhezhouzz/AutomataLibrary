open Ast
open Ocaml5_parser
open Parsetree

let of_expr regex_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_fun (_, _, arg, expr) -> (
        let q, qv = To_notation.quantifier_of_expr arg in
        let body = aux expr in
        match q with
        | Normalty.Connective.Fa -> RForall { qv; body }
        | Normalty.Connective.Ex -> RExists { qv; body })
    | _ -> Regex (regex_of_expr expr)
  in
  aux expr

let layout layout_ty layout_regex e =
  let rec aux = function
    | Regex regex -> layout_regex regex
    | RForall { qv; body } ->
        spf "∀(%s:%s).%s" qv.x (layout_ty qv.ty) (aux body)
    | RExists { qv; body } ->
        spf "∃(%s:%s).%s" qv.x (layout_ty qv.ty) (aux body)
  in
  aux e
