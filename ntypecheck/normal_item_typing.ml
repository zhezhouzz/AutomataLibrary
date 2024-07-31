open Language
open Normal_prop_typing
open Normal_regex_typing
(* open Normal_inst_typing *)

type t = Nt.t

let constructor_declaration_mk_ (retty, { constr_name; argsty }) =
  constr_name #: (Nt.construct_arr_tp (argsty, retty))

let item_mk_ctx (e : t option item) =
  match e with
  | MTyDecl { type_name; type_params; type_decls } ->
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs =
        List.map (fun c -> constructor_declaration_mk_ (retty, c)) type_decls
      in
      xs
  | MEventDecl { ev; _ } ->
      let ev = __force_typed __FILE__ __LINE__ ev in
      let ev = ev.x #: (add_server_field_record_type ev.ty) in
      [ ev ]
  | MValDecl x -> [ __force_typed __FILE__ __LINE__ x ]
  | MMethodPred mp -> [ __force_typed __FILE__ __LINE__ mp ]
  | MAxiom _ | MRegex _ | MTyDeclSub _ -> []
(* | _ -> _failatwith __FILE__ __LINE__ "not predefine" *)

let item_check ctx (e : t option item) : t ctx * t item =
  match e with
  | MTyDeclSub { type_name; super_ty } ->
      (ctx, MTyDeclSub { type_name; super_ty })
  | MTyDecl { type_name; type_params; type_decls } ->
      let res = MTyDecl { type_name; type_params; type_decls } in
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs =
        List.map (fun c -> constructor_declaration_mk_ (retty, c)) type_decls
      in
      (add_to_rights ctx xs, res)
  | MEventDecl { ev; event_kind } ->
      let ev = __force_typed __FILE__ __LINE__ ev in
      let ev = ev.x #: (add_server_field_record_type ev.ty) in
      let res = MEventDecl { ev; event_kind } in
      (add_to_right ctx ev, res)
  | MValDecl x ->
      let x = __force_typed __FILE__ __LINE__ x in
      let res = MValDecl x in
      (add_to_right ctx x, res)
  | MMethodPred x ->
      let x = __force_typed __FILE__ __LINE__ x in
      let res = MMethodPred x in
      (add_to_right ctx x, res)
  | MAxiom { name; prop } ->
      (ctx, MAxiom { name; prop = bi_typed_prop_check ctx prop })
  | MRegex { name; automata } ->
      let automata = bi_symbolic_regex_check ctx automata in
      let name = name.x #: automata.ty in
      ( add_to_right ctx name.x #: automata.ty,
        MRegex { name; automata = automata.x } )
(* | _ -> _failatwith __FILE__ __LINE__ "die" *)

let struct_mk_ctx ctx l =
  add_to_rights ctx @@ List.concat @@ List.map item_mk_ctx l

let struct_check ctx l =
  List.fold_left
    (fun (ctx, res) e ->
      let ctx, e = item_check ctx e in
      (ctx, res @ [ e ]))
    (ctx, []) l
