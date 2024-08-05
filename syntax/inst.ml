open Ast

(* let inst_with_var_or_c (inst : 't inst) (name : string) (c : var_or_c) = *)
(*   let rec aux = function *)
(*     | IVar x when String.equal name x.x -> ( *)
(*         match c with *)
(*         | VCC c -> IConst c *)
(*         | VCTVar y -> IVar y *)
(*         | _ -> _failatwith __FILE__ __LINE__ "die") *)
(*     | IApp (a, b) -> IApp (aux a, aux b) *)
(*     | ILet { lhs; rhs; body } -> *)
(*         let rhs = aux rhs in *)
(*         if String.equal lhs.x name then ILet { lhs; rhs; body } *)
(*         else ILet { lhs; rhs; body = aux body } *)
(*     | IAtomicF { args; regex } -> *)
(*         if List.exists (fun arg -> String.equal name arg.x) args then *)
(*           IAtomicF { args; regex } *)
(*         else IAtomicF { args; regex = Regex.subst_regex_var_or_c regex name c } *)
(*     | (IVar _ | IConst _ | IQregex _) as inst -> inst *)
(*   in *)
(*   aux inst *)

(* let inst_with_qregex (inst : 't inst) (name : string) *)
(*     (q : ('t, 't sevent) qregex) = *)
(*   let rec aux = function *)
(*     | IVar x when String.equal name x.x -> IQregex q *)
(*     | IApp (a, b) -> IApp (aux a, aux b) *)
(*     | ILet { lhs; rhs; body } -> *)
(*         let rhs = aux rhs in *)
(*         if String.equal lhs.x name then ILet { lhs; rhs; body } *)
(*         else ILet { lhs; rhs; body = aux body } *)
(*     | (IVar _ | IConst _ | IQregex _ | IAtomicF _) as inst -> inst *)
(*   in *)
(*   aux inst *)

(* let get_interpreted_sort binding qv = *)
(*   match Typectx.get_opt binding (Nt.layout qv.ty) with *)
(*   | Some (IConst c) -> c *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

(* let to_machine tab q = *)
(*   let rec aux (binding, q) = *)
(*     match q with *)
(*     | RPi _ -> _failatwith __FILE__ __LINE__ "die" *)
(*     | RForall { qv; body } -> *)
(*         let binding = *)
(*           binding *)
(*           @ [ (qv.x, Normalty.Connective.Fa, get_interpreted_sort tab qv) ] *)
(*         in *)
(*         aux (binding, body) *)
(*     | RExists { qv; body } -> *)
(*         let binding = *)
(*           binding *)
(*           @ [ (qv.x, Normalty.Connective.Ex, get_interpreted_sort tab qv) ] *)
(*         in *)
(*         aux (binding, body) *)
(*     | Regex reg -> { binding; reg } *)
(*   in *)
(*   aux ([], q) *)

let rec world_to_nt = function
  | WState -> Nt.Ty_int
  | WSingle { qv; world; _ } -> Nt.Ty_tuple [ qv.ty; world_to_nt world ]
  | WMap { qv; world; _ } -> mk_p_map_ty qv.ty (world_to_nt world)

let rec get_qvs_from_world = function
  | WState -> []
  | WSingle { qv; world; _ } -> qv :: get_qvs_from_world world
  | WMap { qv; world; _ } -> qv :: get_qvs_from_world world

let rec get_abstract_qvs_from_world = function
  | WState -> []
  | WSingle { qv; world; abstract_type } ->
      (qv.x #: abstract_type) :: get_abstract_qvs_from_world world
  | WMap { qv; world; abstract_type } ->
      (qv.x #: abstract_type) :: get_abstract_qvs_from_world world
