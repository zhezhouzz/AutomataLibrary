open Language
open Normal_id_typing
open Normal_constant_typing
open Sugar

type t = Nt.t

let rec bi_typed_inst_check (ctx : t ctx)
    (lit : (t option, t option inst) typed) (ty : t) : (t, t inst) typed =
  match (lit.x, ty) with
  | IVar _, _ | IConst _, _ ->
      let lit = bi_typed_inst_infer ctx lit.x in
      let _ = Nt._type_unify __FILE__ __LINE__ lit.ty ty in
      lit.x #: ty
  | IQregex _, _ -> _failatwith __FILE__ __LINE__ "die"
  | IApp _, _ ->
      let lit' = bi_typed_inst_infer ctx lit.x in
      let ty = Nt._type_unify __FILE__ __LINE__ lit'.ty ty in
      lit'.x #: ty

and bi_typed_inst_infer (ctx : t ctx) (lit : t option inst) : (t, t inst) typed
    =
  match lit with
  | IVar id ->
      let id =
        match id.ty with
        | None -> bi_typed_id_infer ctx id
        | Some ty -> id.x #: ty
      in
      (* let () = Printf.printf "%s --> %s\n" id.x (Nt.layout id.ty) in *)
      (IVar id) #: id.ty
  | IConst c -> (IConst c) #: (infer_constant c)
  | IQregex _ -> _failatwith __FILE__ __LINE__ "die"
  | IApp (mp, arg) ->
      let mp = bi_typed_inst_infer ctx mp in
      let arg = bi_typed_inst_infer ctx arg in
      (* let () = *)
      (*   Printf.printf "%s -- %s\n" *)
      (*     (layout_inst Nt.layout mp.x) *)
      (*     (layout_inst Nt.layout arg.x) *)
      (* in *)
      let mp_ty =
        Nt._type_unify __FILE__ __LINE__ mp.ty (Nt.mk_arr arg.ty Ty_unknown)
      in
      let mp = mp.x #: mp_ty in
      let retty =
        match mp_ty with
        | Nt.Ty_arrow (_, t) -> t
        | _ -> _failatwith __FILE__ __LINE__ "die"
      in
      (IApp (mp.x, arg.x)) #: retty
