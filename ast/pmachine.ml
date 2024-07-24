open Sexplib.Std
open Mtyped
open Constant

type 't p_const =
  | PBool of bool
  | PInt of int
  | PNull
  | PSeqLit of 't p_const list
  | PStr of string
  | PHalt
  | PThis
  | PRandomBool
[@@deriving sexp]

let p_infix_operator =
  [ "-"; "+"; "=="; "!="; ">"; "<"; ">="; "<="; "*"; "\\"; "in" ]

(** Also p statement *)
type 't p_expr =
  | Pid of (('t, string) typed[@free])
  | PConst of ('t, 't p_const) typed
  | PApp of {
      pfunc : (('t, string) typed[@free]);
      args : ('t, 't p_expr) typed list;
    }
  | PRecord of (string * ('t, 't p_expr) typed) list
  | PField of { record : ('t, 't p_expr) typed; field : string }
  | PAssign of {
      lvalue : ('t, 't p_expr) typed;
      rvalue : ('t, 't p_expr) typed;
    }
  | PLet of {
      lhs : (('t, string) typed[@free]);
      rhs : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PSeq of { rhs : ('t, 't p_expr) typed; body : ('t, 't p_expr) typed }
  | PGoto of string
  | PReturn of ('t, 't p_expr) typed
[@@deriving sexp]

let mk_return x = (PReturn x) #: x.ty

type 't p_func = {
  params : ('t, string) typed list;
  local_vars : ('t, string) typed list;
  body : ('t, 't p_expr) typed;
}
[@@deriving sexp]

type state_label = Hot | Cold | Start [@@deriving sexp]
type func_label = Plain | Entry | Exit | Listen of string [@@deriving sexp]

type 't p_state = {
  name : string;
  state_label : state_label list;
  state_body : (func_label * 't p_func) list;
}
[@@deriving sexp]

type 't p_machine_decl = {
  name : string;
  local_vars : ('t, string) typed list;
  local_funcs : (('t, string) typed * 't p_func) list;
  states : 't p_state list;
}
[@@deriving sexp]

type 't p_item =
  | PMachine of 't p_machine_decl
  (* | PTypeDecl of (Nt.t, string) typed *)
  | PGlobalFunc of ('t, string) typed * 't p_func
[@@deriving sexp]
