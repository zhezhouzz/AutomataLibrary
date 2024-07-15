open Sexplib.Std
open Mtyped
open Prop
open Sevent
open Regex
open Qregex
open Inst
open Constructor_declaration

type 't item =
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decls : constructor_declaration list;
    }
  | MValDecl of ('t, string) typed
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; prop : 't prop }
  | MFAImp of { name : string; automata : ('t, string) qregex }
  | MSFAImp of { name : string; automata : ('t, 't sevent) qregex }
  | MConstant of { name : ('t, string) typed; const : Constant.constant }
  | MInst of { name : string; inst : 't inst }
[@@deriving sexp]
