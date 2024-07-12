open Ast

let qregex2regex = function
  | Regex regex -> regex
  | _ -> _failatwith __FILE__ __LINE__ "is quantified"
