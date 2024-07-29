open Language
open Zzdatatype.Datatype
open Qtype
open World

let action_name_mapping = "action_name"

let action_name_mapping_decl =
  action_name_mapping #: (mk_p_map_ty Ty_int (mk_p_abstract_ty "string"))

let action_name_mapping_expr = mk_pid @@ action_name_mapping_decl
let prop_func_name (op, i) = spf "prop_%s_%i" op i

type pprop = string * int * (Nt.t, string) typed list * Nt.t prop

let prop_func_declear (op, i, vs, _) =
  ( (prop_func_name (op, i)) #: Nt.Ty_bool,
    { params = vs; local_vars = []; body = mk_return_void } )

let prop_func_expr (op, i, vs, _) =
  let vsty = List.map _get_ty vs in
  mk_pid (prop_func_name (op, i)) #: (Nt.construct_arr_tp (vsty, Nt.Ty_bool))

let machine_register_sevents { name; local_vars; local_funcs; states }
    (ses : Nt.t sevent list) =
  let m =
    List.fold_left
      (fun m se ->
        match se with
        | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
        | EffEvent { op; vs; phi } ->
            StrMap.update op
              (function
                | None -> Some (vs, [ phi ])
                | Some (vs, phis) -> Some (vs, phi :: phis))
              m)
      StrMap.empty ses
  in
  let m =
    StrMap.map
      (fun (vs, l) ->
        (vs, List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) l))
      m
  in
  let pprops =
    StrMap.fold
      (fun op (vs, phis) l ->
        List.mapi (fun i phi -> (op, i, vs, phi)) phis @ l)
      m []
  in
  let pprop_decls = List.map prop_func_declear pprops in
  { name; local_vars; local_funcs = pprop_decls @ local_funcs; states }

(* let machine_register_prop { name; local_vars; local_funcs; states } *)
(*     (props : (Nt.t, prop) IntMap.t) = *)
(*   { *)
(*     name; *)
(*     local_vars = world_decl world :: local_vars; *)
(*     local_funcs = world_init_expr world :: local_funcs; *)
(*     states; *)
(*   } *)
