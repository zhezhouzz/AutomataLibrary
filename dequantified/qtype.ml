open Language
(* open Zzdatatype.Datatype *)

let qDomain = "_domain"

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

let qtype_init_function_decl = "qtype_init" #: Nt.Ty_unit

let server_machines_decl =
  "server_machines" #: (mk_p_seq_ty (mk_p_abstract_ty "machine"))

let server_domain_decl = "server_domain" #: (mk_p_set_ty Nt.Ty_int)

let mk_index_set_function_decl =
  "mk_index_set"
  #: (Nt.mk_arr
        (mk_p_seq_ty (mk_p_abstract_ty "machine"))
        (mk_p_set_ty Nt.int_ty))

let mk_qtype_init_input qtypes =
  let vs =
    List.map
      (fun qty ->
        if Nt.eq (mk_p_abstract_ty "server") (fst qty) then server_machines_decl
        else qtype_domain_declear qty)
      qtypes
  in
  let input = "input" #: (mk_p_record_ty vs) in
  (vs, input)

let mk_qtype_init_function_decl qtypes =
  let vs, input = mk_qtype_init_input qtypes in
  let es =
    List.map
      (fun x ->
        if Nt.eq server_machines_decl.ty x.ty then
          (* NOTE: handle server specially *)
          let e = mk_field (mk_pid input) x.x in
          mk_p_seq
            (mk_p_vassign (server_machines_decl, e))
            (mk_p_vassign
               (server_domain_decl, mk_p_app mk_index_set_function_decl [ e ]))
        else mk_p_vassign (x, mk_field (mk_pid input) x.x))
      vs
  in
  ( qtype_init_function_decl,
    mk_p_function_decl [ input ] [] (mk_p_seqs es mk_return_void) )

let qtype_choose_function_name (nt, _) = "qtype_choose_" ^ Nt.layout nt

let qtype_choose_expr (nt, superty) =
  mk_p_app
    "choose" #: (Nt.mk_arr (mk_p_set_ty superty) superty)
    [ qtype_domain_expr (nt, superty) ]

let machine_register_qtypes { name; local_vars; local_funcs; states } ctx =
  let qtypes = List.map (fun x -> (mk_p_abstract_ty x.x, x.ty)) ctx in
  let declears = List.map qtype_domain_declear qtypes in
  {
    name;
    local_vars = (server_machines_decl :: declears) @ local_vars;
    local_funcs = mk_qtype_init_function_decl qtypes :: local_funcs;
    states;
  }

let machine_register_qtypes_test m =
  machine_register_qtypes m [ "server" #: Nt.Ty_int; "account" #: Nt.Ty_int ]
