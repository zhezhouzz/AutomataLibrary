open Language
open Normal_regex_typing

type t = Nt.t

let bi_qregex_check (regex_check : t ctx -> 'a regex -> 'b regex) (ctx : t ctx)
    (qregex : (Nt.t option, 'a) qregex) : (Nt.t, 'b) qregex =
  let rec aux ctx qregex =
    match qregex with
    | Regex regex -> Regex (regex_check ctx regex)
    | RForall { qv; body } ->
        let qv = __force_typed __FILE__ __LINE__ qv in
        RForall { qv; body = aux (add_to_right ctx qv) body }
    | RExists { qv; body } ->
        let qv = __force_typed __FILE__ __LINE__ qv in
        RExists { qv; body = aux (add_to_right ctx qv) body }
  in
  aux ctx qregex

let bi_str_qregex_check ctx automata =
  bi_qregex_check bi_str_regex_check ctx automata

let bi_symbolic_qregex_check ctx automata =
  bi_qregex_check bi_symbolic_regex_check ctx automata
