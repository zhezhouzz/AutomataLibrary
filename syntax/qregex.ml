open Ast

let rec get_regex_from_qregex = function
  | Regex regex -> regex
  | RPi { body; _ } -> get_regex_from_qregex body
  | RForall { body; _ } -> get_regex_from_qregex body
  | RExists { body; _ } -> get_regex_from_qregex body
