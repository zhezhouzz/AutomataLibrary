include Syntax
include Common
include To_id
include To_lit
include To_sevent
include To_prop
include To_item

(* module Nt = struct *)
(*   include Nt.T *)
(*   include Nt *)
(* end *)

let layout_str_regex = To_regex.layout (fun x -> x)
let layout_str_qregex = To_qregex.layout Nt.layout layout_str_regex
let layout_symbolic_regex regex = To_regex.layout To_sevent.layout regex

let layout_symbolic_qregex regex =
  To_qregex.layout Nt.layout layout_symbolic_regex regex

let layout_desym_regex regex = To_regex.layout DesymLabel.layout regex
let layout_desym_qregex = To_qregex.layout Nt.layout layout_desym_regex

let layout_ntopt_symbolic_qregex =
  To_qregex.layout Ntopt.layout layout_str_regex

let str_regex_of_expr = To_regex.of_expr id_of_expr
let str_qregex_of_expr = To_qregex.of_expr str_regex_of_expr
let symbolic_regex_of_expr = To_regex.of_expr To_sevent.of_expr
let symbolic_qregex_of_expr = To_qregex.of_expr symbolic_regex_of_expr
