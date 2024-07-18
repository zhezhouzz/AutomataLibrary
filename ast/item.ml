open Sexplib.Std
open Mtyped
open Prop
open Sevent
open Regex
open Inst
open Constructor_declaration

type 't item =
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decls : constructor_declaration list;
    }
  | MTyDeclSub of { type_name : string; super_ty : Nt.t }
  | MValDecl of ('t, string) typed
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; prop : 't prop }
  | MRegex of { name : ('t, string) typed; automata : ('t, 't sevent) regex }
(* | MFAImp of { name : string; automata : ('t, string) re } *)
(* | MSFAImp of { name : string; automata : ('t, 't sevent) qregex } *)
[@@deriving sexp]
