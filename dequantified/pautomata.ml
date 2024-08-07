open Language
open Zzdatatype.Datatype
open Qtype
open World
open Pprop

let action_name_mapping = "action_name"

let action_name_mapping_decl =
  action_name_mapping #: (mk_p_map_ty Ty_int mk_p_string_ty)

let action_name_mapping_expr = mk_pid @@ action_name_mapping_decl

let __force_effect_event = function
  | EffEvent { op; vs; phi } -> (op, vs, phi)
  | _ -> _failatwith __FILE__ __LINE__ "die"

module S2D = SFA.CharMap
module D2S = DesymFA.CharMap

let concretlize_atuoamta reg =
  let open SFA in
  let globals, regs =
    List.split @@ List.mapi (fun i (global, reg) -> ((i, global), (i, reg))) reg
  in
  (* let () = *)
  (*   Printf.printf "globals\n%s\n" *)
  (*     (List.split_by "\n" *)
  (*        (fun (i, prop) -> spf "%i:%s;" i (layout_prop prop)) *)
  (*        globals) *)
  (* in *)
  let finals =
    IntMap.of_seq @@ List.to_seq
    @@ List.map (fun (i, dfa) -> (i, dfa.finals)) regs
  in
  let mapping = List.map (fun (i, reg) -> (i, reg.next)) regs in
  let get_actions mapping =
    let ses =
      List.of_seq @@ Seq.concat
      @@ Seq.map (fun m -> Seq.map fst @@ CharMap.to_seq m)
      @@ Seq.map snd @@ StateMap.to_seq mapping
    in
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
    m
  in
  let ms =
    List.fold_left
      (fun m (_, mapping) ->
        let m' = get_actions mapping in
        StrMap.union (fun _ (_, l1) (vs, l2) -> Some (vs, l1 @ l2)) m m')
      StrMap.empty mapping
  in
  let m =
    StrMap.map
      (fun (vs, l) ->
        (vs, List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) l))
      ms
  in
  let actions = m in
  (* NOTE: also had global ones *)
  let m = StrMap.add global_event_name ([], List.map snd globals) m in
  (* let event_typing_ctx = StrMap.map (fun (vs, _) -> mk_p_record_ty vs) m in *)
  let s2d, d2s =
    StrMap.fold
      (fun op (vs, props) (s2d, d2s) ->
        let s2d =
          List.fold_lefti
            (fun s2d i phi -> S2D.add (EffEvent { op; vs; phi }) (op, i) s2d)
            s2d props
        in
        let d2s =
          List.fold_lefti
            (fun d2s i phi -> D2S.add (op, i) (EffEvent { op; vs; phi }) d2s)
            d2s props
        in
        (s2d, d2s))
      m (S2D.empty, D2S.empty)
  in
  (* let () = *)
  (*   Printf.printf "s2d\n%s\n" *)
  (*     (List.split_by_comma layout_se *)
  (*        (List.of_seq @@ Seq.map fst @@ S2D.to_seq s2d)) *)
  (* in *)
  let mk_mapping mapping =
    let mapping =
      StateMap.map
        (fun m ->
          D2S.of_seq
          @@ Seq.map (fun (c, s) ->
                 (* let () = Printf.printf "%s\n" (layout_se c) in *)
                 (CharMap.find c s2d, s))
          @@ CharMap.to_seq m)
        mapping
    in
    let mk_precise (m : state D2S.t) =
      let l = List.of_seq @@ D2S.to_seq m in
      let m =
        List.fold_right
          (fun ((op, i), state) ->
            StrMap.update op (function
              | None -> Some (IntMap.singleton i state)
              | Some m' -> Some (IntMap.add i state m')))
          l StrMap.empty
      in
      m
    in
    StateMap.map mk_precise mapping
  in
  let mapping =
    IntMap.of_seq @@ List.to_seq
    @@ List.map
         (fun (i, mapping) ->
           let _, global_prop =
             List.find "die" (fun (i', _) -> i == i') globals
           in
           let global_event =
             EffEvent { op = global_event_name; vs = []; phi = global_prop }
           in
           let _, id = S2D.find global_event s2d in
           (id, mk_mapping mapping))
         mapping
  in
  (actions, mapping, finals, d2s)

let transition_init_function_name = "transition_init_function"
let transition_init_function_decl = transition_init_function_name #: Nt.Ty_unit
let transition_name = "transitions"

let transtion_type =
  mk_p_map_ty Nt.Ty_int (* the global prop index *)
    (mk_p_map_ty Nt.Ty_int (* the state *)
       (mk_p_map_ty mk_p_string_ty (* the event name *)
          (mk_p_map_ty Nt.Ty_int (* the prop index *)
             Nt.Ty_int (* the next state *))))

let transition_decl = transition_name #: transtion_type
let transition_expr = mk_pid transition_decl

let init_p_int_map (m : (pexpr -> pexpr) IntMap.t) (expr : pexpr) =
  let () =
    Printf.printf "%s: %s\n" (layout_p_expr 0 expr.x) (layout_pnt expr.ty)
  in
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    IntMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_int64_map (m : (pexpr -> pexpr) StateMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StateMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_str_map (m : (pexpr -> pexpr) StrMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StrMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_string i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let mk_transition_init_function mapping =
  let mapping =
    IntMap.map
      (StateMap.map
         (StrMap.map (IntMap.map (fun i e -> mk_p_assign (e, mk_p_int i)))))
      mapping
  in
  let mapping = IntMap.map (StateMap.map (StrMap.map init_p_int_map)) mapping in
  let mapping = IntMap.map (StateMap.map init_p_str_map) mapping in
  let mapping = IntMap.map init_p_int64_map mapping in
  let body = init_p_int_map mapping transition_expr in
  (transition_init_function_decl, mk_p_function_decl [] [] body)

let machine_register_transitions { name; local_vars; local_funcs; states }
    mapping =
  {
    name;
    local_vars = transition_decl :: local_vars;
    local_funcs = mk_transition_init_function mapping :: local_funcs;
    states;
  }

let machine_register_d2s { name; local_vars; local_funcs; states } world d2s =
  let pprops =
    D2S.fold
      (fun (op, i) se l ->
        let _, vs, phi = __force_effect_event se in
        (op, i, vs, phi) :: l)
      d2s []
  in
  let gpprops, pprops =
    List.partition
      (fun (op, _, _, _) -> String.equal op global_event_name)
      pprops
  in
  let pprop_decls = List.map (prop_func_declear world) pprops in
  let gpprop_decls = List.map (gprop_func_declear world) gpprops in
  {
    name;
    local_vars;
    local_funcs = gpprop_decls @ pprop_decls @ local_funcs;
    states;
  }

(** predict an event under world *)
(* let predict_under_world_function_name op = spf "predict_under_world_%s" op *)

(* let mk_predict_under_world_function world ctx op m = *)
(*   let event_type = *)
(*     match get_opt ctx op with *)
(*     | None -> _failatwith __FILE__ __LINE__ "die" *)
(*     | Some ty -> ty *)
(*   in *)
(*   let input = input_name #: event_type in *)
(*   let qvs = get_qvs_from_world world in *)
(*   let mk_inner_expr m = *)
(*     let state_expr = StrMap.find "die" m state_decl.x in *)
(*     let qvs = List.map (fun x -> StrMap.find "die" m x.x) qvs in *)
(*     let transitions = mk_p_access (transition_expr, state_expr) in *)
(*     let transitions = mk_p_access (transitions, mk_p_string op) in *)
(*     let prop_id = ("prop_id" #: Nt.Ty_int) in *)
(*     let value = ("next_state" #: Nt.Ty_int) in *)
(*     mk_foreach_map key vlaue *)
(*   let prepare = *)
(*     List.map (fun v -> mk_p_assign (mk_pid v, mk_field (mk_pid input) v.x)) vs *)
(*   in *)
(*   { *)
(*     params = qvs @ [ input ]; *)
(*     local_vars = qvs; *)
(*     body = mk_p_seqs prepare (mk_return @@ prop_to_p_prop prop); *)
(*   } *)

(** validate an event *)
let validate_function_name op = spf "validate_%s" op

let mk_validate_function world op size =
  let qvs = get_qvs_from_world world in
  let next_state = "next_state" #: Nt.Ty_int in
  let if_valid = "if_valid" #: Nt.Ty_bool in
  let mapping = "m" #: (mk_p_map_ty Nt.Ty_int Nt.Ty_int) in
  let input = input_name #: op.ty in
  let prepare = mk_p_assign (mk_pid if_valid, mk_p_bool false) in
  (* let e = mk_foreach_map (mk_pid mapping) (fun action_id) *)
  let mk_one i s prop_id =
    let prop_func = (prop_func_name (op.x, prop_id)) #: Nt.Ty_unit in
    let condition = mk_p_app prop_func (List.map mk_pid (qvs @ [ input ])) in
    let tbranch = mk_return @@ mk_p_tuple [ mk_p_bool true; s ] in
    mk_p_it (mk_p_eq (mk_pid i) (mk_p_int prop_id)) @@ mk_p_it condition tbranch
  in
  let e =
    mk_foreach_map (mk_pid mapping) (fun i s ->
        mk_p_seqs_ @@ List.init size (mk_one i s))
  in
  let body =
    mk_return (mk_p_tuple (List.map mk_pid [ if_valid; next_state ]))
  in
  let body = mk_p_seqs [ prepare; e ] body in
  ( (validate_function_name op.x) #: Nt.Ty_unit,
    mk_p_function_decl (qvs @ [ mapping; input ]) [ next_state; if_valid ] body
  )

(** next world *)

let source_field_decl = "source" #: (mk_p_abstract_ty "machine")
let next_world_function op = spf "next_world_%s" op
let next_world_function_decl op = (next_world_function op.x) #: Nt.Ty_unit

let mk_send op event =
  let server_id = (mk_field event default_serv_field.x).x #: Nt.Ty_int in
  let dest = mk_p_access (mk_pid server_machines_decl, server_id) in
  (* let l = *)
  (*   match remove_server_field_record_type op.ty with *)
  (*   | Nt.Ty_record l -> l *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
  (* in *)
  let l =
    match op.ty with
    | Nt.Ty_record l -> l
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let payload =
    mk_p_record
    @@ (source_field_decl.x, mk_p_this)
       :: List.map (fun (name, _) -> (name, mk_field event name)) l
  in
  mk_p_send dest op.x payload

let world_iter_with_transitions (f : pexpr StrMap.t -> pexpr -> pexpr)
    (world : world) : pexpr =
  world_iter
    (fun m ->
      let qvs = get_qvs_from_world world in
      let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
      let state = StrMap.find "die" m state_decl.x in
      let mapping =
        mk_p_access
          (transition_expr, mk_p_app world_to_gprop_id_function_decl qvs)
      in
      let mapping = mk_p_access (mapping, state) in
      f m mapping)
    world

let mk_next_world_function world (kind, op) =
  let just_check_sat = "just_check_sat" #: Nt.Ty_bool in
  let qvs = get_qvs_from_world world in
  (* let op = "op" #: (mk_p_string_ty) in *)
  let res = "res" #: (Nt.mk_tuple [ Nt.Ty_bool; Nt.Ty_int ]) in
  let input = input_name #: op.ty in
  let func = (validate_function_name op.x) #: Nt.Ty_unit in
  let if_valid = "if_valid" #: Nt.Ty_bool in
  let prepares =
    [
      mk_p_assign (mk_pid if_valid, mk_p_bool true);
      mk_p_assign (tmp_world_expr world, world_expr world);
    ]
  in
  let mk_one m mapping =
    let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
    let state = StrMap.find "die" m state_decl.x in
    let mapping = mk_p_access (mapping, mk_p_string op.x) in
    let e11, e12 = mk_depair (mk_pid res) in
    let e2 =
      mk_p_ite e11
        (mk_p_assign (state, e12))
        (Some (mk_p_assign (mk_pid if_valid, mk_p_bool false)))
    in
    let body =
      mk_p_let res (mk_p_app func (qvs @ [ mapping; mk_pid input ])) e2
    in
    body
  in
  let loop = world_iter_with_transitions mk_one world in
  let e_just_check_sat =
    mk_p_it (mk_pid just_check_sat)
      (mk_p_seq
         (mk_p_assign (world_expr world, tmp_world_expr world))
         (mk_return (mk_pid if_valid)))
  in
  let body =
    mk_p_ite
      (mk_p_not (mk_pid if_valid))
      (mk_p_assign (world_expr world, tmp_world_expr world))
      (match kind with
      | Resp -> None
      | Hidden ->
          _failatwith __FILE__ __LINE__ "the hidden event should be eliminated"
      | Req -> Some (mk_send op (mk_pid input)))
  in
  let last = mk_return (mk_pid if_valid) in
  let body = mk_p_seqs (prepares @ [ loop; e_just_check_sat; body ]) last in
  ( (next_world_function op.x) #: Nt.Ty_unit,
    mk_p_function_decl [ just_check_sat; input ]
      [ tmp_world_decl world; if_valid ]
      body )

let action_domain_name = "action_domain"
let action_domain_declar = action_domain_name #: (mk_p_set_ty mk_p_string_ty)
let action_domain_expr = mk_pid action_domain_declar
let action_domain_init_function_name = "action_domain_init"

let action_domain_init_function_decl =
  action_domain_init_function_name #: Nt.Ty_unit

let action_domain_init actions =
  let l = StrMap.to_key_list actions in
  let es =
    List.map (fun op -> mk_p_add_set action_domain_expr (mk_p_string op)) l
  in
  let body = mk_p_seqs es mk_return_void in
  (action_domain_init_function_decl, mk_p_function_decl [] [] body)

(** get available actions *)
let get_available_actions_function_name = "get_available_actions"

let get_available_actions_function_decl =
  get_available_actions_function_name #: (mk_p_set_ty mk_p_string_ty)

let get_available_actions_function world =
  let res = "res" #: (mk_p_set_ty mk_p_string_ty) in
  let prepares = [ mk_p_assign (mk_pid res, action_domain_expr) ] in
  let mk_one _ mapping =
    let body =
      mk_p_assign
        (mk_pid res, mk_set_intersection (mk_pid res) @@ mk_p_map_keys mapping)
    in
    body
  in
  let loop = world_iter_with_transitions mk_one world in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs (prepares @ [ loop ]) last in
  (get_available_actions_function_decl, mk_p_function_decl [] [ res ] body)

(** mk_random_event *)
let random_event_function_name op = spf "random_event_%s" op

let random_event_function_decl op =
  (random_event_function_name op.x) #: (Nt.mk_arr Nt.Ty_unit op.ty)

let random_instance_from_type abstract_ctx e =
  let aux = function
    | Nt.Ty_bool -> mk_random_bool
    | Nt.Ty_int -> mk_random_int
    | Nt.Ty_constructor (_, []) as t -> (
        match get_opt abstract_ctx (Nt.layout t) with
        | None -> _failatwith __FILE__ __LINE__ (spf "die: %s" (Nt.layout t))
        | Some (ATSuper _) ->
            mk_random_from_seq (qtype_domain_expr (t, Nt.Ty_int))
        | Some (ATEnum names) -> mk_p_choose (mk_p_int (List.length names))
        | Some (ATAssigned _) -> _failatwith __FILE__ __LINE__ "die")
    | _ as ty -> _failatwith __FILE__ __LINE__ (spf "die: %s" (Nt.layout ty))
  in
  aux e

let mk_random_event_function_decl abstract_ctx op =
  let vs =
    match op.ty with
    | Nt.Ty_record l -> l
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let es =
    List.map (fun (x, ty) -> (x, random_instance_from_type abstract_ctx ty)) vs
  in
  let body = mk_return @@ mk_p_record es in
  (random_event_function_decl op, mk_p_function_decl [] [] body)

(** mk_action *)

let machine_register_actions { name; local_vars; local_funcs; states } kind_ctx
    abstract_ctx world actions =
  let actions_decls =
    StrMap.fold
      (fun op (vs, phis) l ->
        let op = op #: (mk_p_record_ty vs) in
        mk_validate_function world op (List.length phis) :: l)
      actions []
  in
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list actions
  in
  let ops =
    List.filter_map
      (fun x ->
        if String.equal x.x global_event_name then None
        else
          match get_opt kind_ctx x.x with
          | None -> _failatwith __FILE__ __LINE__ "die"
          | Some kind -> Some (kind, x))
      ops
  in
  let next_world_decls =
    List.fold_right (fun op l -> mk_next_world_function world op :: l) ops []
  in
  let random_event_function_decls =
    List.fold_right
      (fun op l -> mk_random_event_function_decl abstract_ctx (snd op) :: l)
      ops []
  in
  (* let do_action_function_decl = mk_do_action_function_decl ops in *)
  {
    name;
    local_vars = action_domain_declar :: local_vars;
    local_funcs =
      [ action_domain_init actions; get_available_actions_function world ]
      @ random_event_function_decls @ actions_decls @ next_world_decls
      @ local_funcs;
    states;
  }

let final_states_decl =
  "final_states" #: (mk_p_map_ty Nt.Ty_int (mk_p_set_ty Nt.Ty_int))

let final_states_expr = mk_pid final_states_decl
let final_states_init_function_decl = "final_states_init" #: Nt.Ty_unit

let mk_final_states_init_function_decl ss =
  let m =
    IntMap.map
      (fun ss final_states_expr ->
        let ss = List.of_seq @@ StateSet.to_seq ss in
        let e =
          mk_p_assign (final_states_expr, mk_p_default final_states_expr.ty)
        in
        let es =
          List.map (fun s -> mk_p_add_set final_states_expr (mk_p_int s)) ss
        in
        mk_p_seqs_ (e :: es))
      ss
  in
  let body = init_p_int_map m final_states_expr in
  (final_states_init_function_decl, mk_p_function_decl [] [] body)

let check_final_function_name = "check_final"
let check_final_function_decl = check_final_function_name #: Nt.Ty_bool

let mk_check_final_function_decl world =
  let res = "res" #: Nt.Ty_bool in
  let e =
    world_iter
      (fun m ->
        let qvs = get_qvs_from_world world in
        let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
        let state = StrMap.find "die" m state_decl.x in
        let final_states =
          mk_p_access
            (final_states_expr, mk_p_app world_to_gprop_id_function_decl qvs)
        in
        mk_p_it
          (mk_p_not (mk_p_in state final_states))
          (mk_p_vassign (res, mk_p_bool false)))
      world
  in
  let prepare = mk_p_vassign (res, mk_p_bool true) in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs [ prepare; e ] last in
  (check_final_function_decl, mk_p_function_decl [] [ res ] body)

(** Loop state *)
let loop_state_name = "Loop"

(** handle response *)

let mk_handle_function op =
  let event = "input" #: op.ty in
  let next_world_f = next_world_function_decl op in
  let body =
    mk_p_it
      (mk_p_app next_world_f [ mk_p_bool false; mk_pid event ])
      (mk_p_goto loop_state_name)
  in
  let body = mk_p_seq body mk_p_error in
  ((Listen op.x) #: Nt.Ty_unit, mk_p_function_decl [ event ] [] body)

let loop_state_function_decl request_ops response_ops =
  let e1 = mk_p_it (mk_p_app check_final_function_decl []) mk_p_halt in
  let action = "action" #: (mk_p_abstract_ty "string") in
  let mk_request_f op =
    let event = (spf "event_%s" op.x) #: op.ty in
    let print_event = mk_p_printf (spf "event %s: {0}" op.x) [ mk_pid event ] in
    let random_f = random_event_function_decl op in
    let next_world_f = next_world_function_decl op in
    mk_p_it
      (mk_p_eq (mk_p_string op.x) (mk_pid action))
      (mk_p_let event (mk_p_app random_f [])
         (mk_p_seq print_event
            (mk_p_it
               (mk_p_app next_world_f [ mk_p_bool false; mk_pid event ])
               (mk_p_goto loop_state_name))))
  in
  let request_es = List.map mk_request_f request_ops in
  let mk_response_f op =
    let event = (spf "event_%s" op.x) #: op.ty in
    let print_event = mk_p_printf (spf "event %s: {0}" op.x) [ mk_pid event ] in
    let random_f = random_event_function_decl op in
    let next_world_f = next_world_function_decl op in
    mk_p_it
      (mk_p_eq (mk_p_string op.x) (mk_pid action))
      (mk_p_let event (mk_p_app random_f [])
         (mk_p_seq print_event
            (mk_p_it
               (mk_p_not
               @@ mk_p_app next_world_f [ mk_p_bool true; mk_pid event ])
               (mk_p_goto loop_state_name))))
  in
  let response_es = List.map mk_response_f response_ops in
  let print_action = mk_p_printf "choose action: {0}" [ mk_pid action ] in
  let body =
    mk_p_let action
      (mk_random_from_seq (mk_p_app get_available_actions_function_decl []))
      (mk_p_seqs_ ((print_action :: request_es) @ response_es))
  in
  let body = mk_p_seq e1 body in
  (Entry #: Nt.Ty_unit, mk_p_function_decl [] [] body)

let loop_state kind_ctx ops =
  let request_ops, response_ops =
    List.partition
      (fun x ->
        match get_opt kind_ctx x.x with
        | Some Req -> true
        | Some Resp -> false
        | Some Hidden -> _failatwith __FILE__ __LINE__ "die"
        | None -> _failatwith __FILE__ __LINE__ "die")
      ops
  in
  let es = List.map mk_handle_function response_ops in
  {
    name = loop_state_name;
    state_label = [];
    state_body = loop_state_function_decl request_ops response_ops :: es;
  }

(** Init state *)
let init_state_name = "Init"

let init_state_function_decl ctx =
  let qtypes = get_qtypes_from_abstract_ctx ctx in
  let _, input = mk_qtype_init_input qtypes in
  let e = mk_p_app qtype_init_function_decl [ mk_pid input ] in
  let mk f = mk_p_app f [] in
  let functions =
    [
      world_init_function_decl;
      action_domain_init_function_decl;
      final_states_init_function_decl;
      transition_init_function_decl;
    ]
  in
  let body =
    mk_p_seqs (e :: List.map mk functions) (mk_p_goto loop_state_name)
  in
  mk_p_function_decl [ input ] [] body

let init_state ctx =
  {
    name = init_state_name;
    state_label = [ Start ];
    state_body = [ (Entry #: Nt.Ty_unit, init_state_function_decl ctx) ];
  }

let machine_register_states { name; local_vars; local_funcs; states } kind_ctx
    ctx ops =
  {
    name;
    local_vars;
    local_funcs;
    states = init_state ctx :: loop_state kind_ctx ops :: states;
  }

let machine_register_finals { name; local_vars; local_funcs; states } world ss =
  {
    name;
    local_vars = final_states_decl :: local_vars;
    local_funcs =
      mk_check_final_function_decl world
      :: mk_final_states_init_function_decl ss
      :: local_funcs;
    states;
  }

let machine_register_automata m kind_ctx abstract_ctx { world; reg } =
  (* let open SFA in *)
  let actions, mapping, finals, d2s = concretlize_atuoamta reg in
  let m = machine_register_world m (IntMap.to_key_list mapping) world in
  let m = machine_register_d2s m world d2s in
  let m = machine_register_transitions m mapping in
  let m = machine_register_finals m world finals in
  let m = machine_register_actions m kind_ctx abstract_ctx world actions in
  let ops =
    List.map (fun (op, (vs, _)) -> op #: (mk_p_record_ty vs))
    @@ StrMap.to_kv_list actions
  in
  let m = machine_register_states m kind_ctx abstract_ctx ops in
  m

let file_register_abstract_types items ctx =
  let l =
    List.map
      (fun x ->
        match x.ty with
        | ATSuper ty -> PTypeDecl x.x #: ty
        | ATEnum names -> PEnumDecl (x.x, names)
        | _ -> _failatwith __FILE__ __LINE__ "unimp")
      (("action" #: (ATSuper mk_p_string_ty)) :: ctx_to_list ctx)
  in
  l @ items

let file_register_events items (kind_ctx, event_ctx) =
  let l = ctx_to_list event_ctx in
  let l =
    List.map
      (fun x ->
        match get_opt kind_ctx x.x with
        | Some Req ->
            let tys =
              match x.ty with
              | Nt.Ty_record l -> l
              | _ -> _failatwith __FILE__ __LINE__ "die"
            in
            let tys = (source_field_decl.x, source_field_decl.ty) :: tys in
            x.x #: (Nt.Ty_record tys)
        | Some Resp -> x
        | Some Hidden -> _failatwith __FILE__ __LINE__ "die"
        | None -> _failatwith __FILE__ __LINE__ "die")
      l
  in
  let l = List.map (fun x -> PEventDecl x) l in
  l @ items
