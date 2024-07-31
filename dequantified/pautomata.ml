open Language
open Zzdatatype.Datatype
open Qtype
open World
open Pprop

let action_name_mapping = "action_name"

let action_name_mapping_decl =
  action_name_mapping #: (mk_p_map_ty Ty_int mk_p_string_ty)

let action_name_mapping_expr = mk_pid @@ action_name_mapping_decl
let prop_func_name (op, i) = spf "prop_%s_%i" op i

type pprop = string * int * (Nt.t, string) typed list * Nt.t prop

let prop_func_declear world (op, i, vs, prop) =
  let qvs = get_qvs_from_world world in
  ( (prop_func_name (op, i)) #: Nt.Ty_bool,
    mk_p_prop_function_decl qvs (vs, prop) )

let prop_func_expr (op, i) =
  let vs =
    match op.ty with
    | Nt.Ty_record l -> l
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let vsty = List.map snd vs in
  mk_pid (prop_func_name (op.x, i)) #: (Nt.construct_arr_tp (vsty, Nt.Ty_bool))

let __force_effect_event = function
  | EffEvent { op; vs; phi } -> (op, vs, phi)
  | _ -> _failatwith __FILE__ __LINE__ "die"

module S2D = SFA.CharMap
module D2S = DesymFA.CharMap

let concretlize_atuoamta reg =
  let open SFA in
  let mapping = concretelize_dfa_aux (fun x -> x) reg in
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
  let m =
    StrMap.map
      (fun (vs, l) ->
        (vs, List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) l))
      m
  in
  let actions = m in
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
  let mapping =
    StateMap.map
      (fun m ->
        D2S.of_seq
        @@ Seq.map (fun (c, s) -> (CharMap.find c s2d, s))
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
  let mapping = StateMap.map mk_precise mapping in
  (actions, mapping, d2s)

let transition_init_function_name = "transition_init_function"
let transition_init_function_decl = transition_init_function_name #: Nt.Ty_unit
let transition_name = "transitions"

let transtion_type =
  mk_p_map_ty Nt.Ty_int
    (mk_p_map_ty mk_p_string_ty (mk_p_map_ty Nt.Ty_int Nt.Ty_int))

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
        let lvalue = mk_p_access (expr, mk_p_int (Int64.to_int i)) in
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
    StateMap.map
      (StrMap.map
         (IntMap.map (fun i e -> mk_p_assign (e, mk_p_int (Int64.to_int i)))))
      mapping
  in
  let mapping = StateMap.map (StrMap.map init_p_int_map) mapping in
  let mapping = StateMap.map init_p_str_map mapping in
  let body = init_p_int64_map mapping transition_expr in
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
  let pprop_decls = List.map (prop_func_declear world) pprops in
  { name; local_vars; local_funcs = pprop_decls @ local_funcs; states }

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
(*     let state_expr = StrMap.find "die" m state_name in *)
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
  let mk_one prop_id =
    let prop_func = (prop_func_name (op.x, prop_id)) #: Nt.Ty_unit in
    let condition = mk_p_app prop_func (List.map mk_pid (qvs @ [ input ])) in
    let s = mk_p_access (mk_pid mapping, mk_p_int prop_id) in
    let tbranch1 = mk_p_assign (mk_pid next_state, s) in
    let tbranch2 = mk_p_assign (mk_pid if_valid, mk_p_bool true) in
    mk_p_it condition (mk_p_seq tbranch1 tbranch2)
  in
  let es = List.init size mk_one in
  let body =
    mk_return (mk_p_tuple (List.map mk_pid [ if_valid; next_state ]))
  in
  let body = mk_p_seqs (prepare :: es) body in
  ( (validate_function_name op.x) #: Nt.Ty_unit,
    mk_p_function_decl (qvs @ [ mapping; input ]) [ next_state; if_valid ] body
  )

(** next world *)

let next_world_function op = spf "next_world_%s" op
let next_world_function_decl op = (next_world_function op.x) #: Nt.Ty_unit

let mk_next_world_function world op =
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
  let mk_one m =
    let qvs = List.map (fun qv -> StrMap.find "die" m qv.x) qvs in
    let state = StrMap.find "die" m state_name in
    let mapping = mk_p_access (transition_expr, state) in
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
  let loop = world_iter mk_one world in
  let body =
    mk_p_it
      (mk_p_not (mk_pid if_valid))
      (mk_p_assign (world_expr world, tmp_world_expr world))
  in
  let last = mk_return (mk_pid if_valid) in
  let body = mk_p_seqs (prepares @ [ loop; body ]) last in
  ( (next_world_function op.x) #: Nt.Ty_unit,
    mk_p_function_decl [ input ] [ tmp_world_decl world; if_valid ] body )

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
  let mk_one m =
    let state = StrMap.find "die" m state_name in
    let mapping = mk_p_access (transition_expr, state) in
    let body =
      mk_p_assign
        (mk_pid res, mk_set_intersection (mk_pid res) @@ mk_p_map_keys mapping)
    in
    body
  in
  let loop = world_iter mk_one world in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs (prepares @ [ loop ]) last in
  (get_available_actions_function_decl, mk_p_function_decl [] [ res ] body)

(** mk_random_event *)
let random_event_function_name op = spf "random_event_%s" op

let random_event_function_decl op =
  (random_event_function_name op.x) #: (Nt.mk_arr Nt.Ty_unit op.ty)

let random_instance_from_type e =
  let aux = function
    | Nt.Ty_bool -> mk_random_bool
    | Nt.Ty_int -> mk_random_int
    | Nt.Ty_constructor (_, []) as t ->
        mk_random_from_seq (qtype_domain_expr (t, Nt.Ty_int))
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux e

let mk_random_event_function_decl op =
  let vs =
    match op.ty with
    | Nt.Ty_record l -> l
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let es = List.map (fun (x, ty) -> (x, random_instance_from_type ty)) vs in
  let body = mk_return @@ mk_p_record es in
  (random_event_function_decl op, mk_p_function_decl [] [] body)

(** mk_action *)

let do_action_function = "do_action"
let do_action_function_decl = do_action_function #: Nt.Ty_unit

let mk_do_action_function_decl ops =
  let action = "action" #: (mk_p_abstract_ty "string") in
  let mk_f op =
    let event = (spf "event_%s" op.x) #: op.ty in
    let random_f = random_event_function_decl op in
    let next_world_f = next_world_function_decl op in
    mk_p_it
      (mk_p_eq (mk_p_string op.x) (mk_pid action))
      (mk_p_let event (mk_p_app random_f [])
         (mk_p_it
            (mk_p_app next_world_f [ mk_pid event ])
            (mk_return (mk_p_bool true))))
  in
  let es = List.map mk_f ops in
  let body =
    mk_p_let action
      (mk_random_from_seq (mk_p_app get_available_actions_function_decl []))
      (mk_p_seqs es (mk_return (mk_p_bool false)))
  in
  (do_action_function_decl, mk_p_function_decl [] [] body)

let machine_register_actions { name; local_vars; local_funcs; states } world
    actions =
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
  let next_world_decls =
    List.fold_right (fun op l -> mk_next_world_function world op :: l) ops []
  in
  let random_event_function_decls =
    List.fold_right (fun op l -> mk_random_event_function_decl op :: l) ops []
  in
  let do_action_function_decl = mk_do_action_function_decl ops in
  {
    name;
    local_vars = action_domain_declar :: local_vars;
    local_funcs =
      [ action_domain_init actions; get_available_actions_function world ]
      @ random_event_function_decls @ actions_decls @ next_world_decls
      @ [ do_action_function_decl ]
      @ local_funcs;
    states;
  }

let final_states_name = "final_states"
let final_states_decl = final_states_name #: (mk_p_set_ty Nt.Ty_int)
let final_states_expr = mk_pid final_states_decl
let final_states_init_function_name = "final_states_init"

let final_states_init_function_decl =
  final_states_init_function_name #: Nt.Ty_unit

let mk_final_states_init_function_decl ss =
  let ss = List.of_seq @@ StateSet.to_seq ss in
  let es =
    List.map
      (fun s -> mk_p_add_set final_states_expr (mk_p_int (Int64.to_int s)))
      ss
  in
  let body = mk_p_seqs es mk_return_void in
  (final_states_init_function_decl, mk_p_function_decl [] [] body)

let check_final_function_name = "check_final"
let check_final_function_decl = check_final_function_name #: Nt.Ty_bool

let mk_check_final_function_decl world =
  let res = "res" #: Nt.Ty_bool in
  let e =
    world_iter
      (fun m ->
        let state = StrMap.find "die" m state_name in
        mk_p_it
          (mk_p_not (mk_p_in state final_states_expr))
          (mk_p_vassign (res, mk_p_bool false)))
      world
  in
  let prepare = mk_p_vassign (res, mk_p_bool true) in
  let last = mk_return (mk_pid res) in
  let body = mk_p_seqs [ prepare; e ] last in
  (check_final_function_decl, mk_p_function_decl [] [ res ] body)

(** Loop state *)
let loop_state_name = "Loop"

let loop_state_function_decl =
  let e1 = mk_p_it (mk_p_app check_final_function_decl []) mk_p_halt in
  let e2 = mk_p_app do_action_function_decl [] in
  let body = mk_p_seqs [ e1; e2 ] (mk_p_goto loop_state_name) in
  mk_p_function_decl [] [] body

let loop_state =
  {
    name = loop_state_name;
    state_label = [];
    state_body = [ (Entry #: Nt.Ty_unit, loop_state_function_decl) ];
  }

(** Init state *)
let init_state_name = "Init"

let init_state_function_decl ctx =
  let qtypes = List.map (fun x -> (mk_p_abstract_ty x.x, x.ty)) ctx in
  let vs = List.map (fun qty -> qtype_domain_declear qty) qtypes in
  let input = "input" #: (mk_p_record_ty vs) in
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

let machine_register_states { name; local_vars; local_funcs; states } ctx =
  {
    name;
    local_vars;
    local_funcs;
    states = init_state ctx :: loop_state :: states;
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

let machine_register_automata m ctx { world; reg } =
  (* let open SFA in *)
  let actions, mapping, d2s = concretlize_atuoamta reg in
  let m = machine_register_world m world in
  let m = machine_register_d2s m world d2s in
  let m = machine_register_transitions m mapping in
  let m = machine_register_finals m world reg.finals in
  let m = machine_register_actions m world actions in
  let m = machine_register_states m (ctx_to_list ctx) in
  m

let file_register_abstract_types items ctx =
  let l =
    List.map
      (fun x -> PTypeDecl x)
      (("st" #: Nt.Ty_int) :: ("action" #: mk_p_string_ty) :: ctx_to_list ctx)
  in
  l @ items

let file_register_events items ({ reg; _ } : SFA.dfa regspec) =
  let actions, _, _ = concretlize_atuoamta reg in
  let l =
    List.map (fun (op, (vs, _)) ->
        let ty = mk_p_record_ty vs in
        op #: ty)
    @@ StrMap.to_kv_list actions
  in
  let l = List.map (fun x -> PEventDecl x) l in
  l @ items
