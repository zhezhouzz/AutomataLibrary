open Sexplib.Std
open Mtyped
open Constant

(** constant has types independent from type context *)
type p_const =
  | PUnit
  | PBool of bool
  | PInt of int
  | PDefault of Nt.t
  (* | PSeqLit of p_const list *)
  (* | PRecordLit of (string * p_const) list *)
  | PStr of string
  | PHalt
  | PRandomBool
[@@deriving sexp]

let p_infix_operator =
  [ "&&"; "||"; "-"; "+"; "=="; "!="; ">"; "<"; ">="; "<="; "*"; "\\"; "in" ]

let mk_p_abstract_ty name = Nt.Ty_constructor (name, [])
let mk_p_set_ty ty = Nt.Ty_constructor ("set", [ ty ])
let mk_p_seq_ty ty = Nt.Ty_constructor ("seq", [ ty ])
let mk_p_map_ty ty1 ty2 = Nt.Ty_constructor ("map", [ ty1; ty2 ])
let mk_p_ref_ty ty = Nt.Ty_constructor ("ref", [ ty ])
let mk_p_record_ty vs = Nt.Ty_record (List.map (fun x -> (x.x, x.ty)) vs)
let mk_p_string_ty = mk_p_abstract_ty "string"

let mk_p_tuple_ty vs =
  Nt.Ty_record (List.mapi (fun i ty -> (string_of_int i, ty)) vs)

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
  | ForeachSet of {
      elem : ('t, string) typed;
      set : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | ForeachMap of {
      key : ('t, string) typed;
      map : ('t, 't p_expr) typed;
      body : ('t, 't p_expr) typed;
    }
  | PIf of {
      condition : ('t, 't p_expr) typed;
      tbranch : ('t, 't p_expr) typed;
      fbranch : ('t, 't p_expr) typed option;
    }
  | PSend of {
      dest : ('t, 't p_expr) typed;
      event_name : string;
      payload : ('t, 't p_expr) typed;
    }
  | PGoto of string
  | PBreak
  | PReturn of ('t, 't p_expr) typed
[@@deriving sexp]

open Sugar

let mk_break = PBreak #: Nt.Ty_unit
let mk_p_default nt = (PConst (PDefault nt)) #: nt
let mk_pid id = (Pid id) #: id.ty

let mk_p_ite condition tbranch fbranch =
  (PIf { condition; tbranch; fbranch }) #: Nt.Ty_unit

let mk_p_it condition tbranch =
  (PIf { condition; tbranch; fbranch = None }) #: Nt.Ty_unit

let mk_field record field =
  let ty =
    match record.ty with
    | Nt.Ty_record l -> (
        match List.find_opt (fun (name, _) -> String.equal name field) l with
        | None -> _failatwith __FILE__ __LINE__ "die"
        | Some (_, ty) -> ty)
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  (PField { record; field }) #: ty

let mk_p_send dest event_name payload =
  (PSend { dest; event_name; payload }) #: Nt.unit_ty

(** TODO: record type and tuple type...*)
let mk_depair (record : (Nt.t, Nt.t p_expr) typed) =
  match record.ty with
  | Nt.Ty_tuple [ t1; t2 ] ->
      let fst = (PField { record; field = "0" }) #: t1 in
      let snd = (PField { record; field = "1" }) #: t2 in
      (fst, snd)
  | Nt.Ty_record [ (_, t1); (_, t2) ] ->
      let fst = (PField { record; field = "0" }) #: t1 in
      let snd = (PField { record; field = "1" }) #: t2 in
      (fst, snd)
  | _ -> _failatwith __FILE__ __LINE__ (spf "die: %s" (Nt.layout record.ty))

let mk_p_app pfunc args =
  let _, retty = Nt.destruct_arr_tp pfunc.ty in
  (PApp { pfunc; args }) #: retty

let mk_p_add_set e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ t1 ]) ->
      if Nt.eq t1 e2.ty then
        let f =
          "add_set" #: (Nt.construct_arr_tp ([ e1.ty; e2.ty ], Nt.Ty_unit))
        in
        mk_p_app f [ e1; e2 ]
      else _failatwith __FILE__ __LINE__ "die"
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_map_keys e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ t1; _ ]) ->
      let f = "keys" #: (Nt.mk_arr e1.ty (mk_p_set_ty t1)) in
      mk_p_app f [ e1 ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_map_values e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ _; t2 ]) ->
      let f = "values" #: (Nt.mk_arr e1.ty (mk_p_set_ty t2)) in
      mk_p_app f [ e1 ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_set_intersection e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ t2 ]) when Nt.eq e1.ty e2.ty ->
      let f =
        "intersection" #: (Nt.construct_arr_tp ([ e1.ty; e1.ty ], e1.ty))
      in
      mk_p_app f [ e1; e2 ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_choose pexpr =
  match pexpr.ty with
  | Nt.Ty_constructor ("set", [ nt ]) ->
      let pfunc = "choose" #: (Nt.mk_arr pexpr.ty nt) in
      mk_p_app pfunc [ pexpr ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

open Zzdatatype.Datatype

let mk_p_seq rhs body = (PSeq { rhs; body }) #: body.ty
let mk_p_seqs es e = List.fold_right mk_p_seq es e

let mk_p_seqs_ es =
  match List.last_destruct_opt es with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some (es, e) -> mk_p_seqs es e

let mk_p_assign (lvalue, rvalue) = (PAssign { lvalue; rvalue }) #: Nt.Ty_unit

let mk_p_vassign (lvalue, rvalue) =
  (PAssign { lvalue = mk_pid lvalue; rvalue }) #: Nt.Ty_unit

let mk_p_let lhs rhs body = (PLet { lhs; rhs; body }) #: body.ty
let mk_return_void = (PReturn (PConst PUnit) #: Nt.Ty_unit) #: Nt.Ty_unit
let mk_p_int i = (PConst (PInt i)) #: Nt.Ty_int
let mk_p_bool b = (PConst (PBool b)) #: Nt.Ty_bool
let mk_p_string str = (PConst (PStr str)) #: (mk_p_abstract_ty "string")
let mk_random_bool = (PConst PRandomBool) #: Nt.Ty_bool

let mk_random_int =
  mk_p_app "choose" #: (Nt.mk_arr Nt.Ty_int Nt.Ty_int) [ mk_p_int 10000 ]

let mk_random_from_seq seq =
  match seq.ty with
  | Nt.Ty_constructor ("set", [ t2 ]) ->
      mk_p_app "choose" #: (Nt.mk_arr seq.ty t2) [ seq ]
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_access (container, index) =
  let e = PAccess { container; index } in
  let t2 =
    match container.ty with
    | Nt.Ty_constructor ("map", [ t1; t2 ]) ->
        if Nt.eq t1 index.ty then t2
        else
          _failatwith __FILE__ __LINE__
            (spf "%s != %s" (Nt.layout t1) (Nt.layout index.ty))
    | Nt.Ty_constructor ("set", [ t2 ]) ->
        if Nt.eq Nt.Ty_int index.ty then t2
        else
          _failatwith __FILE__ __LINE__
            (spf "%s != %s" (Nt.layout Nt.Ty_int) (Nt.layout index.ty))
    | Nt.Ty_constructor ("seq", [ t2 ]) ->
        (* HACK: server type = int *)
        if
          Nt.eq Nt.Ty_int index.ty || Nt.eq (mk_p_abstract_ty "server") index.ty
        then t2
        else
          _failatwith __FILE__ __LINE__
            (spf "%s != %s" (Nt.layout Nt.Ty_int) (Nt.layout index.ty))
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "%s[%s]?" (Nt.layout container.ty) (Nt.layout index.ty))
  in
  e #: t2

let mk_foreach_map_with_key key map body =
  let value = mk_p_access (map, mk_pid key) in
  (ForeachMap { key; map; body = body value }) #: Nt.Ty_unit

let mk_foreach_map map body =
  match map.ty with
  | Nt.Ty_constructor ("map", [ t1; t2 ]) ->
      let key = (Rename.unique "key") #: t1 in
      mk_foreach_map_with_key key map (body key)
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_foreach_set set body =
  match set.ty with
  | Nt.Ty_constructor ("set", [ t ]) ->
      let elem = (Rename.unique "elem") #: t in
      (ForeachSet { elem; set; body = body (mk_pid elem) }) #: Nt.Ty_unit
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_record l =
  let tys = List.map (fun (name, e) -> name #: e.ty) l in
  let ty = mk_p_record_ty tys in
  (PRecord l) #: ty

let mk_p_tuple l = mk_p_record @@ List.mapi (fun i e -> (string_of_int i, e)) l

let mk_return x =
  let rec aux x =
    match x.x with
    | PGoto _ -> x
    | PSeq { rhs; body } -> (PSeq { rhs; body = aux body }) #: x.ty
    | PLet { lhs; rhs; body } -> (PLet { lhs; rhs; body = aux body }) #: x.ty
    | _ -> (PReturn x) #: x.ty
  in
  aux x

let mk_p_eq e1 e2 =
  if Nt.eq e1.ty e2.ty then
    mk_p_app
      "==" #: (Nt.construct_arr_tp ([ e1.ty; e1.ty ], Nt.Ty_bool))
      [ e1; e2 ]
  else _failatwith __FILE__ __LINE__ "die"

let mk_p_in e1 e2 =
  mk_p_app "in" #: (Nt.construct_arr_tp ([ e1.ty; e2.ty ], Ty_bool)) [ e1; e2 ]

let mk_p_halt = mk_return @@ ((PConst PHalt) #: Nt.Ty_unit)
let mk_p_goto name = (PGoto name) #: Nt.Ty_unit

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
  | PTypeDecl of (Nt.t, string) typed
  | PEventDecl of (Nt.t, string) typed
  | PGlobalFunc of ('t, string) typed * 't p_func
  | PPrimFuncDecl of ('t, string) typed
[@@deriving sexp]

let p_expr_to_str expr =
  Sexplib.Sexp.to_string @@ sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) expr

let map_on_p_machine f items =
  List.map (function PMachine m -> PMachine (f m) | _ as item -> item) items
