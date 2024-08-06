module type AST = sig
  type 'a ast [@@deriving sexp]

  val fv : 'a ast -> string
  val subst : 'a ast -> string -> 'a ast -> 'a ast
  val subst_id : 'a ast -> string -> string -> 'a ast
end

open Ast

let layout_states f s =
  let open Zzdatatype.Datatype in
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s
