open Language
(* open Zzdatatype.Datatype *)

let qDomain = "_Domain"

type pexpr = (Nt.t, Nt.t p_expr) typed

let domain_name nt =
  match nt with
  | Nt.Ty_constructor (name, []) -> name ^ qDomain
  | _ -> _failatwith __FILE__ __LINE__ "die"

let qtype_domain_declear (nt, superty) =
  (domain_name nt) #: (mk_p_set_ty superty)

let qtype_domain_expr qty = mk_pid @@ qtype_domain_declear qty

let fresh_qname (nt, _) =
  let name = Rename.unique (Nt.layout nt) in
  name #: nt

let qtype_iter (f : pexpr -> pexpr) qty : pexpr =
  let set = qtype_domain_expr qty in
  mk_foreach_set set f

let qtype_init_function_name = "qtype_init"
let qtype_init_function_decl = qtype_init_function_name #: Nt.Ty_unit

let mk_qtype_init_function_decl qtypes =
  let vs = List.map (fun qty -> qtype_domain_declear qty) qtypes in
  let input = "input" #: (mk_p_record_ty vs) in
  let es =
    List.map (fun x -> mk_p_vassign (x, mk_field (mk_pid input) x.x)) vs
  in
  ( qtype_init_function_decl,
    mk_p_function_decl [ input ] [] (mk_p_seqs es mk_return_void) )

let qtype_choose_function_name (nt, _) = "qtype_choose_" ^ Nt.layout nt

let qtype_choose_expr (nt, superty) =
  mk_p_app
    "choose" #: (Nt.mk_arr (mk_p_set_ty superty) superty)
    [ qtype_domain_expr (nt, superty) ]

(* let qtype_default_expr (nt, superty) = *)
(*   mk_p_app ("choose") *)

let machine_register_qtypes { name; local_vars; local_funcs; states } ctx =
  let qtypes = List.map (fun x -> (mk_p_abstract_ty x.x, x.ty)) ctx in
  let declears = List.map qtype_domain_declear qtypes in
  {
    name;
    local_vars = declears @ local_vars;
    local_funcs = mk_qtype_init_function_decl qtypes :: local_funcs;
    states;
  }

let machine_register_qtypes_test m =
  machine_register_qtypes m [ "server" #: Nt.Ty_int; "account" #: Nt.Ty_int ]
