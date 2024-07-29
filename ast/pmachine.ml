open Sexplib.Std
open Mtyped
open Constant

(** constant has types independent from type context *)
type p_const =
  | PUnit
  | PBool of bool
  | PInt of int
  (* | PSeqLit of p_const list *)
  (* | PRecordLit of (string * p_const) list *)
  | PStr of string
  | PHalt
  | PRandomBool
[@@deriving sexp]

let p_infix_operator =
  [ "-"; "+"; "=="; "!="; ">"; "<"; ">="; "<="; "*"; "\\"; "in" ]

let mk_p_abstract_ty name = Nt.Ty_constructor (name, [])
let mk_p_seq_ty ty = Nt.Ty_constructor ("seq", [ ty ])
let mk_p_map_ty ty1 ty2 = Nt.Ty_constructor ("map", [ ty1; ty2 ])
let mk_p_ref_ty ty = Nt.Ty_constructor ("ref", [ ty ])

let mk_p_machine_ty name =
  Nt.Ty_constructor ("machine", [ Nt.Ty_constructor (name, []) ])

(** Also p statement *)
type 't p_expr =
  | PThis
  | PNull
  | Pid of (('t, string) typed[@free])
  | PConst of p_const
  | PApp of {
      pfunc : (('t, string) typed[@free]);
      args : ('t, 't p_expr) typed list;
    }
  | PAccess of {
      container : ('t, 't p_expr) typed;
      index : ('t, 't p_expr) typed;
    }
  | PRecord of (string * ('t, 't p_expr) typed) list
  | PField of { record : ('t, 't p_expr) typed; field : string }
  | PAssign of {
      lvalue : ('t, 't p_expr) typed;
      rvalue : ('t, 't p_expr) typed;
    }
  | PDeref of ('t, 't p_expr) typed
  | PLet of {
      lhs : (('t, string) typed[@free]);
      rhs : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PSeq of { rhs : ('t, 't p_expr) typed; body : ('t, 't p_expr) typed }
  | ForeachSeq of {
      elem : ('t, string) typed;
      seq : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | ForeachMap of {
      key : ('t, string) typed;
      value : ('t, string) typed;
      map : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PGoto of string
  | PReturn of ('t, 't p_expr) typed
[@@deriving sexp]

let mk_pid id = (Pid id) #: id.ty

open Sugar

let mk_depair (record : (Nt.t, Nt.t p_expr) typed) =
  match record.ty with
  | Nt.Ty_tuple [ t1; t2 ] ->
      let fst = (PField { record; field = "0" }) #: t1 in
      let snd = (PField { record; field = "1" }) #: t2 in
      (fst, snd)
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_foreach_map key value map body =
  (ForeachMap { key; value; map; body }) #: Nt.Ty_unit

let mk_foreach_seq elem seq body =
  (ForeachSeq { elem; seq; body }) #: Nt.Ty_unit

let mk_p_app pfunc args =
  let _, retty = Nt.destruct_arr_tp pfunc.ty in
  (PApp { pfunc; args }) #: retty

let mk_p_choose pexpr =
  match pexpr.ty with
  | Nt.Ty_constructor ("seq", [ nt ]) ->
      let pfunc = "choose" #: (Nt.mk_arr pexpr.ty nt) in
      mk_p_app pfunc [ pexpr ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_seq rhs body = (PSeq { rhs; body }) #: body.ty
let mk_p_seqs es e = List.fold_right mk_p_seq es e
let mk_p_assign (lvalue, rvalue) = (PAssign { lvalue; rvalue }) #: Nt.Ty_unit
let mk_return_void = (PReturn (PConst PUnit) #: Nt.Ty_unit) #: Nt.Ty_unit
let mk_p_int i = (PConst (PInt i)) #: Nt.Ty_int
let mk_p_bool b = (PConst (PBool b)) #: Nt.Ty_bool

let mk_p_access (container, index) =
  let e = PAccess { container; index } in
  let t2 =
    match container.ty with
    | Nt.Ty_constructor ("map", [ t1; t2 ]) when Nt.eq t1 index.ty -> t2
    | Nt.Ty_constructor ("seq", [ t2 ]) when Nt.eq Nt.Ty_int index.ty -> t2
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  e #: t2

let mk_return x =
  let rec aux x =
    match x.x with
    | PGoto _ -> x
    | PSeq { rhs; body } -> (PSeq { rhs; body = aux body }) #: x.ty
    | PLet { lhs; rhs; body } -> (PLet { lhs; rhs; body = aux body }) #: x.ty
    | _ -> (PReturn x) #: x.ty
  in
  aux x

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
  state_body : (('t, func_label) typed * 't p_func) list;
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
  | PPrimFuncDecl of ('t, string) typed
[@@deriving sexp]

let p_expr_to_str expr =
  Sexplib.Sexp.to_string @@ sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) expr

let map_on_p_machine f items =
  List.map (function PMachine m -> PMachine (f m) | _ as item -> item) items
