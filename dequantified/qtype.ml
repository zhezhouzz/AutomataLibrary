open Language
(* open Zzdatatype.Datatype *)

let qDomain = "_Domain"

type pexpr = (Nt.t, Nt.t p_expr) typed

let domain_name nt =
  match nt with
  | Nt.Ty_constructor (name, []) -> name ^ qDomain
  | _ -> _failatwith __FILE__ __LINE__ "die"

let qtype_domain_declear (nt, superty) =
  (domain_name nt) #: (mk_p_seq_ty superty)

let qtype_domain_expr qty = mk_pid @@ qtype_domain_declear qty

let fresh_qname (nt, _) =
  let name = Rename.unique (Nt.layout nt) in
  name #: nt

let qtype_iter (f : pexpr -> pexpr) qty : pexpr =
  let seq = qtype_domain_expr qty in
  let elem = fresh_qname qty in
  mk_foreach_seq elem seq (f (mk_pid elem))

let qtype_init_function = "qtype_init_function"

let qtype_init_function qtypes =
  let f qty =
    let qid = qtype_domain_declear qty in
    let argname = ("_" ^ qid.x) #: qid.ty in
    (qid, argname)
  in
  let l = List.map f qtypes in
  let es = List.map (fun (a, b) -> mk_p_assign (mk_pid a, mk_pid b)) l in
  let _, args = List.split l in
  ( qtype_init_function #: Nt.Ty_unit,
    { params = args; local_vars = []; body = mk_p_seqs es mk_return_void } )

let qtype_choose_function_name (nt, _) = "qtype_choose_" ^ Nt.layout nt

let qtype_choose_expr (nt, superty) =
  mk_p_app
    "choose" #: (Nt.mk_arr (mk_p_seq_ty superty) superty)
    [ qtype_domain_expr (nt, superty) ]

(* let qtype_default_expr (nt, superty) = *)
(*   mk_p_app ("choose") *)

let machine_register_qtypes { name; local_vars; local_funcs; states } qtypes =
  let declears = List.map qtype_domain_declear qtypes in
  {
    name;
    local_vars = declears @ local_vars;
    local_funcs = qtype_init_function qtypes :: local_funcs;
    states;
  }

let machine_register_qtypes_test m =
  let open Nt in
  machine_register_qtypes m
    [
      (Ty_constructor ("server", []), Ty_int);
      (Ty_constructor ("account", []), Ty_int);
    ]
