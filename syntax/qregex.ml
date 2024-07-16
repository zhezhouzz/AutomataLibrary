open Ast

let rec get_regex_from_qregex = function
  | Regex regex -> regex
  | RPi { body; _ } -> get_regex_from_qregex body
  | RForall { body; _ } -> get_regex_from_qregex body
  | RExists { body; _ } -> get_regex_from_qregex body

let get_type q =
  let rec aux = function
    | RPi { sort; body } -> Nt.mk_arr (ty_set sort.ty) (aux body)
    | RForall { qv; body } -> Nt.mk_arr qv.ty (aux body)
    | _ -> Nt.unit_ty
  in
  aux q

let subst_qregex_const regex name c =
  let rec aux = function
    | RPi { sort; body } -> RPi { sort; body = aux body }
    | RForall { qv; body } ->
        if String.equal qv.x name then _failatwith __FILE__ __LINE__ "die"
        else RForall { qv; body = aux body }
    | RExists { qv; body } ->
        if String.equal qv.x name then _failatwith __FILE__ __LINE__ "die"
        else RExists { qv; body = aux body }
    | Regex r -> Regex (Regex.subst_regex_const r name c)
  in
  aux regex

let map_qregex_body (f : 'a -> 'b) q =
  let rec aux = function
    | RPi { sort; body } -> RPi { sort; body = aux body }
    | RForall { qv; body } -> RForall { qv; body = aux body }
    | RExists { qv; body } -> RExists { qv; body = aux body }
    | Regex r -> Regex (f r)
  in
  aux q
