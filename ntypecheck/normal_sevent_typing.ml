open Normal_prop_typing
open Language

(* type t = Nt.t *)

let bi_sevent_check (ctx : Nt.t ctx) (sevent : Nt.t option sevent) : Nt.t sevent
    =
  match sevent with
  | GuardEvent prop -> GuardEvent (bi_typed_prop_check ctx prop)
  | EffEvent { op; vs; phi } -> (
      match get_opt ctx op with
      | None -> _failatwith __FILE__ __LINE__ (spf "undefined event: %s" op)
      | Some ty ->
          let argsty, _ = Nt.destruct_arr_tp ty in
          let vs =
            List.map
              (fun ({ x; ty }, ty') ->
                (* let () = *)
                (*   Printf.printf "%s: %s ?= %s\n" op (layout ty) (Nt.layout ty') *)
                (* in *)
                let ty =
                  Ntopt.__type_unify Ntopt.layout __FILE__ __LINE__ ty
                    (Some ty')
                in
                { x; ty })
              (_safe_combine __FILE__ __LINE__ vs argsty)
          in
          let bindings = List.map (__force_typed __FILE__ __LINE__) vs in
          let ctx' = add_to_rights ctx bindings in
          let phi = bi_typed_prop_check ctx' phi in
          EffEvent { op; vs = bindings; phi })

let bi_label_check = bi_sevent_check
