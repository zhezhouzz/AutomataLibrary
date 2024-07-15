open Language
open Normal_prop_typing
open Normal_qregex_typing
open Normal_constant_typing
open Normal_inst_typing

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
  | MValDecl x -> [ __force_typed __FILE__ __LINE__ x ]
  | MMethodPred mp -> [ __force_typed __FILE__ __LINE__ mp ]
  | MAxiom _ | MFAImp _ | MSFAImp _ | MConstant _ | MInst _ -> []
(* | _ -> _failatwith __FILE__ __LINE__ "not predefine" *)

let item_check ctx (e : t option item) : t ctx * t item =
  match e with
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
  | MFAImp { name; automata } ->
      (ctx, MFAImp { name; automata = bi_str_qregex_check ctx automata })
  | MSFAImp { name; automata } ->
      let automata = bi_symbolic_qregex_check ctx automata in
      (add_to_right ctx name #: (get_type automata), MSFAImp { name; automata })
  | MConstant { name; const } ->
      let t = infer_constant const in
      let name = name.x #: t in
      (add_to_right ctx name, MConstant { name; const })
  | MInst { name; inst } ->
      (ctx, MInst { name; inst = (bi_typed_inst_infer ctx inst).x })
(* | _ -> _failatwith __FILE__ __LINE__ "die" *)

let struct_mk_ctx ctx l =
  add_to_rights ctx @@ List.concat @@ List.map item_mk_ctx l

let struct_check ctx l =
  List.fold_left
    (fun (ctx, res) e ->
      let ctx, e = item_check ctx e in
      (ctx, res @ [ e ]))
    (ctx, []) l
