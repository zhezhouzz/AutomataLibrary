open Ast
open Common

module MakeBasicAutomata (C : CHARAC) = struct
  module C = C
  module CharMap = Map.Make (C)

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : transitions StateMap.t;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : d_transition StateMap.t;
  }

  let _get_next next m = StateMap.find m next
  let ( #-> ) = _get_next

  let nfa_find_states sym (nfa : nfa) m =
    try CharMap.find sym nfa.next #-> m with Not_found -> StateSet.empty

  let _iter_to_fold (type a b c) (iter : (c -> unit) -> a -> unit) :
      (c -> b -> b) -> a -> b -> b =
   fun f container init ->
    let v = ref init in
    iter (fun s -> v := f s !v) container;
    !v

  let nfa_iter_states (f : state -> unit) (nfa : nfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> visit) nfa.next #-> state)
    and visit states = StateSet.iter apply states in
    visit nfa.start

  let dfa_iter_states (f : state -> unit) (dfa : dfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> apply) dfa.next #-> state)
    in
    apply dfa.start

  let nfa_iter_transitions (f : state * C.t * state -> unit) (nfa : nfa) : unit
      =
    nfa_iter_states
      (fun s ->
        CharMap.iter
          (fun (c : C.t) -> StateSet.iter (fun (dst : state) -> f (s, c, dst)))
          nfa.next #-> s)
      nfa

  let dfa_iter_transitions (f : state * C.t * state -> unit) (dfa : dfa) : unit
      =
    dfa_iter_states
      (fun s ->
        CharMap.iter (fun (c : C.t) dst -> f (s, c, dst)) dfa.next #-> s)
      dfa

  let nfa_fold_states (type a) : (state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_states (fun s -> v := f s !v) container;
    !v

  let dfa_fold_states (type a) : (state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_states (fun s -> v := f s !v) container;
    !v

  let nfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let dfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let layout_nfa (nfa : nfa) =
    (* let open Zzdatatype.Datatype in *)
    let () =
      Printf.printf "starts: %s\n" (layout_states Int.to_string nfa.start)
    in
    let () =
      Printf.printf "finals: %s\n" (layout_states Int.to_string nfa.finals)
    in
    let () =
      nfa_iter_transitions
        (fun (s, c, d) ->
          Printf.printf "\t%s--[%s]-->%s\n" (Int.to_string s) (C.layout c)
            (Int.to_string d))
        nfa
    in
    let () = print_newline () in
    ()

  let layout_dfa (dfa : dfa) =
    (* let open Zzdatatype.Datatype in *)
    let () = Printf.printf "starts: %s\n" (Int.to_string dfa.start) in
    let () =
      Printf.printf "finals: %s\n" (layout_states Int.to_string dfa.finals)
    in
    let () =
      dfa_iter_transitions
        (fun (s, c, d) ->
          Printf.printf "\t%s--[%s]-->%s\n" (Int.to_string s) (C.layout c)
            (Int.to_string d))
        dfa
    in
    let () = print_newline () in
    ()

  let nfa_charmap_insert (c : C.t) (d : state) (charmap : StateSet.t CharMap.t)
      =
    CharMap.update c
      (function
        | None -> Some (StateSet.singleton d)
        | Some ss -> Some (StateSet.add d ss))
      charmap

  let dfa_charmap_insert (c : C.t) (d : state) (charmap : state CharMap.t) =
    CharMap.update c
      (function
        | None -> Some d
        | Some d' when not (Int.equal d d') ->
            _failatwith __FILE__ __LINE__ "die"
        | Some d' -> Some d')
      charmap

  let nfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c (StateSet.singleton d))
        | Some charmap -> Some (nfa_charmap_insert c d charmap))
      next

  let dfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c d)
        | Some charmap -> Some (dfa_charmap_insert c d charmap))
      next

  let nfa_next_map_state renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        nfa_next_insert s c d)
      nfa StateMap.empty

  let dfa_next_map_state renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        dfa_next_insert s c d)
      dfa StateMap.empty

  let nfa_next_map_c renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) -> nfa_next_insert s (renaming c) d)
      nfa StateMap.empty

  let dfa_next_map_c renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) -> dfa_next_insert s (renaming c) d)
      dfa StateMap.empty

  let nfa_map_state map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_state map_state nfa in
    {
      start = StateSet.map map_state nfa.start;
      finals = StateSet.map map_state nfa.finals;
      next;
    }

  let dfa_map_state map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_state map_state dfa in
    {
      start = map_state dfa.start;
      finals = StateSet.map map_state dfa.finals;
      next;
    }

  let nfa_map_c map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_c map_state nfa in
    { start = nfa.start; finals = nfa.finals; next }

  let dfa_map_c map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_c map_state dfa in
    { start = dfa.start; finals = dfa.finals; next }

  let force_nfa ({ start; finals; next } : dfa) : nfa =
    {
      start = StateSet.singleton start;
      finals;
      next = StateMap.map (CharMap.map StateSet.singleton) next;
    }

  let normalize_nfa (nfa : nfa) : nfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = nfa_iter_states (fun s -> do_state_renaming s) nfa in
    nfa_map_state (fun s -> StateMap.find s !state_naming) nfa

  let normalize_dfa (dfa : dfa) : dfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = dfa_iter_states (fun s -> do_state_renaming s) dfa in
    dfa_map_state (fun s -> StateMap.find s !state_naming) dfa

  let num_states_nfa (nfa : nfa) = nfa_fold_states (fun _ x -> x + 1) nfa 0
  let num_states_dfa (dfa : dfa) = dfa_fold_states (fun _ x -> x + 1) dfa 0

  let mk_disjoint_multi_nfa (nfa : nfa list) =
    let nfa = List.map normalize_nfa nfa in
    let _, nfa =
      List.fold_left
        (fun (sum, res) (nfa : nfa) ->
          (sum + num_states_nfa nfa, res @ [ nfa_map_state (( + ) sum) nfa ]))
        (0, []) nfa
    in
    nfa

  let mk_disjoint_multi_dfa (dfa : dfa list) =
    let dfa = List.map normalize_dfa dfa in
    let _, dfa =
      List.fold_left
        (fun (sum, res) (dfa : dfa) ->
          (sum + num_states_dfa dfa, res @ [ dfa_map_state (( + ) sum) dfa ]))
        (0, []) dfa
    in
    dfa

  let mk_disjoint_nfa (nfa1, nfa2) =
    match mk_disjoint_multi_nfa [ nfa1; nfa2 ] with
    | [ nfa1; nfa2 ] -> (nfa1, nfa2)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let mk_disjoint_dfa (dfa1, dfa2) =
    match mk_disjoint_multi_dfa [ dfa1; dfa2 ] with
    | [ dfa1; dfa2 ] -> (dfa1, dfa2)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let nfa_union_charmap c1 c2 =
    CharMap.union (fun _ s1 s2 -> Some (StateSet.union s1 s2)) c1 c2

  let dfa_union_charmap c1 c2 =
    CharMap.union (fun _ _ _ -> _failatwith __FILE__ __LINE__ "die") c1 c2

  let nfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (nfa_union_charmap m1 m2)) next1 next2

  let dfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (dfa_union_charmap m1 m2)) next1 next2

  (** Complete *)

  let complete_nfa (ctx : C.t list) (nfa : nfa) =
    (* Add a dummy node to complete the nfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      nfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = nfa.next #-> state in
          List.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
        nfa
    in
    (* reverse the nfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      nfa
    else
      match !max_state with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some s' ->
          let char_map =
            List.fold_right (fun c -> nfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> nfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = nfa.start;
            finals = nfa.finals;
            next = nfa_union_next nfa.next next';
          }

  let complete_dfa (ctx : C.t list) (dfa : dfa) =
    (* Add a dummy node to complete the dfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      dfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = dfa.next #-> state in
          List.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
        dfa
    in
    (* reverse the dfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      dfa
    else
      match !max_state with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some s' ->
          let char_map =
            List.fold_right (fun c -> dfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> dfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = dfa.start;
            finals = dfa.finals;
            next = dfa_union_next dfa.next next';
          }
end

module MakeAutomata (C : CHARACTER) = struct
  include MakeBasicAutomata (C)
  module CharSet = Set.Make (C)
  module CharMap = Map.Make (C)

  module EpsC = struct
    type t = C.t option

    let layout = function None -> "none" | Some c -> C.layout c

    (* HACK: dummy imp *)
    let delimit_cotexnt_char (_, c) = [ c ]

    let compare c1 c2 =
      match (c1, c2) with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some c1, Some c2 -> C.compare c1 c2
  end

  module EpsFA = MakeBasicAutomata (EpsC)

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type 'c raw_regex =
    | Empty : 'c raw_regex (* L = { } *)
    | Eps : 'c raw_regex (* L = {ε} *)
    | MultiChar : 'c list -> 'c raw_regex
    | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Inters : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Comple : 'c list * 'c raw_regex -> 'c raw_regex
    | Seq : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Star : 'c raw_regex -> 'c raw_regex

  let force_eps_nfa (nfa : nfa) : EpsFA.nfa =
    {
      start = nfa.start;
      finals = nfa.finals;
      next =
        nfa_fold_transitions
          (fun (s, c, d) m -> EpsFA.nfa_next_insert s (Some c) d m)
          nfa StateMap.empty;
    }

  let _get_next next m = StateMap.find m next
  let ( #-> ) = _get_next

  let nfa_find_states sym (nfa : nfa) m =
    try CharMap.find sym nfa.next #-> m with Not_found -> StateSet.empty

  let _iter_to_fold (type a b c) (iter : (c -> unit) -> a -> unit) :
      (c -> b -> b) -> a -> b -> b =
   fun f container init ->
    let v = ref init in
    iter (fun s -> v := f s !v) container;
    !v

  let nfa_iter_states (f : state -> unit) (nfa : nfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> visit) nfa.next #-> state)
    and visit states = StateSet.iter apply states in
    visit nfa.start

  let dfa_iter_states (f : state -> unit) (dfa : dfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> apply) dfa.next #-> state)
    in
    apply dfa.start

  let nfa_iter_transitions (f : state * C.t * state -> unit) (nfa : nfa) : unit
      =
    nfa_iter_states
      (fun s ->
        CharMap.iter
          (fun (c : C.t) -> StateSet.iter (fun (dst : state) -> f (s, c, dst)))
          nfa.next #-> s)
      nfa

  let dfa_iter_transitions (f : state * C.t * state -> unit) (dfa : dfa) : unit
      =
    dfa_iter_states
      (fun s ->
        CharMap.iter (fun (c : C.t) dst -> f (s, c, dst)) dfa.next #-> s)
      dfa

  let nfa_fold_states (type a) : (state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_states (fun s -> v := f s !v) container;
    !v

  let dfa_fold_states (type a) : (state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_states (fun s -> v := f s !v) container;
    !v

  let nfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let dfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let layout_nfa (nfa : nfa) =
    (* let open Zzdatatype.Datatype in *)
    let () =
      Printf.printf "starts: %s\n" (layout_states Int.to_string nfa.start)
    in
    let () =
      Printf.printf "finals: %s\n" (layout_states Int.to_string nfa.finals)
    in
    let () =
      nfa_iter_transitions
        (fun (s, c, d) ->
          Printf.printf "\t%s--[%s]-->%s\n" (Int.to_string s) (C.layout c)
            (Int.to_string d))
        nfa
    in
    let () = print_newline () in
    ()

  let layout_dfa (dfa : dfa) =
    (* let open Zzdatatype.Datatype in *)
    let () = Printf.printf "starts: %s\n" (Int.to_string dfa.start) in
    let () =
      Printf.printf "finals: %s\n" (layout_states Int.to_string dfa.finals)
    in
    let () =
      dfa_iter_transitions
        (fun (s, c, d) ->
          Printf.printf "\t%s--[%s]-->%s\n" (Int.to_string s) (C.layout c)
            (Int.to_string d))
        dfa
    in
    let () = print_newline () in
    ()

  let nfa_charmap_insert (c : C.t) (d : state) (charmap : StateSet.t CharMap.t)
      =
    CharMap.update c
      (function
        | None -> Some (StateSet.singleton d)
        | Some ss -> Some (StateSet.add d ss))
      charmap

  let dfa_charmap_insert (c : C.t) (d : state) (charmap : state CharMap.t) =
    CharMap.update c
      (function
        | None -> Some d
        | Some d' when not (Int.equal d d') ->
            _failatwith __FILE__ __LINE__ "die"
        | Some d' -> Some d')
      charmap

  let nfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c (StateSet.singleton d))
        | Some charmap -> Some (nfa_charmap_insert c d charmap))
      next

  let dfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c d)
        | Some charmap -> Some (dfa_charmap_insert c d charmap))
      next

  let nfa_next_map_state renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        nfa_next_insert s c d)
      nfa StateMap.empty

  let dfa_next_map_state renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        dfa_next_insert s c d)
      dfa StateMap.empty

  let nfa_next_map_c renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) -> nfa_next_insert s (renaming c) d)
      nfa StateMap.empty

  let dfa_next_map_c renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) -> dfa_next_insert s (renaming c) d)
      dfa StateMap.empty

  let nfa_map_state map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_state map_state nfa in
    {
      start = StateSet.map map_state nfa.start;
      finals = StateSet.map map_state nfa.finals;
      next;
    }

  let dfa_map_state map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_state map_state dfa in
    {
      start = map_state dfa.start;
      finals = StateSet.map map_state dfa.finals;
      next;
    }

  let nfa_map_c map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_c map_state nfa in
    { start = nfa.start; finals = nfa.finals; next }

  let dfa_map_c map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_c map_state dfa in
    { start = dfa.start; finals = dfa.finals; next }

  let force_nfa ({ start; finals; next } : dfa) : nfa =
    {
      start = StateSet.singleton start;
      finals;
      next = StateMap.map (CharMap.map StateSet.singleton) next;
    }

  let normalize_nfa (nfa : nfa) : nfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = nfa_iter_states (fun s -> do_state_renaming s) nfa in
    nfa_map_state (fun s -> StateMap.find s !state_naming) nfa

  let normalize_dfa (dfa : dfa) : dfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = dfa_iter_states (fun s -> do_state_renaming s) dfa in
    dfa_map_state (fun s -> StateMap.find s !state_naming) dfa

  let num_states_nfa (nfa : nfa) = nfa_fold_states (fun _ x -> x + 1) nfa 0
  let num_states_dfa (dfa : dfa) = dfa_fold_states (fun _ x -> x + 1) dfa 0

  let mk_disjoint_multi_nfa (nfa : nfa list) =
    let nfa = List.map normalize_nfa nfa in
    let _, nfa =
      List.fold_left
        (fun (sum, res) (nfa : nfa) ->
          (sum + num_states_nfa nfa, res @ [ nfa_map_state (( + ) sum) nfa ]))
        (0, []) nfa
    in
    nfa

  let mk_disjoint_multi_dfa (dfa : dfa list) =
    let dfa = List.map normalize_dfa dfa in
    let _, dfa =
      List.fold_left
        (fun (sum, res) (dfa : dfa) ->
          (sum + num_states_dfa dfa, res @ [ dfa_map_state (( + ) sum) dfa ]))
        (0, []) dfa
    in
    dfa

  let mk_disjoint_nfa (nfa1, nfa2) =
    match mk_disjoint_multi_nfa [ nfa1; nfa2 ] with
    | [ nfa1; nfa2 ] -> (nfa1, nfa2)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let mk_disjoint_dfa (dfa1, dfa2) =
    match mk_disjoint_multi_dfa [ dfa1; dfa2 ] with
    | [ dfa1; dfa2 ] -> (dfa1, dfa2)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let nfa_union_charmap c1 c2 =
    CharMap.union (fun _ s1 s2 -> Some (StateSet.union s1 s2)) c1 c2

  let dfa_union_charmap c1 c2 =
    CharMap.union (fun _ _ _ -> _failatwith __FILE__ __LINE__ "die") c1 c2

  let nfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (nfa_union_charmap m1 m2)) next1 next2

  let dfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (dfa_union_charmap m1 m2)) next1 next2

  (** Complete *)

  let complete_nfa (ctx : C.t list) (nfa : nfa) =
    (* Add a dummy node to complete the nfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      nfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = nfa.next #-> state in
          List.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
        nfa
    in
    (* reverse the nfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      nfa
    else
      match !max_state with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some s' ->
          let char_map =
            List.fold_right (fun c -> nfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> nfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = nfa.start;
            finals = nfa.finals;
            next = nfa_union_next nfa.next next';
          }

  let complete_dfa (ctx : C.t list) (dfa : dfa) =
    (* Add a dummy node to complete the dfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      dfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = dfa.next #-> state in
          List.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
        dfa
    in
    (* reverse the dfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      dfa
    else
      match !max_state with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some s' ->
          let char_map =
            List.fold_right (fun c -> dfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> dfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = dfa.start;
            finals = dfa.finals;
            next = dfa_union_next dfa.next next';
          }

  (** Build an NFA by reversing a DFA, inverting transition arrows,
    turning finals states into start states, and the start state into
    the final state *)
  let reverse (dfa : dfa) : nfa =
    let next =
      dfa_fold_transitions
        (fun (s, c, t) -> nfa_next_insert s c t)
        dfa StateMap.empty
    in
    { start = dfa.finals; finals = StateSet.singleton dfa.start; next }

  (** Available transitions from a set of states *)
  let nfa_transitions states (nfa : nfa) =
    StateSet.fold
      (fun s m ->
        let m' = nfa.next #-> s in
        nfa_union_charmap m m')
      states CharMap.empty

  (** Available transitions from a set of states *)
  let eps_nfa_transitions states (nfa : EpsFA.nfa) =
    let tab = Hashtbl.create 10 in
    let rec visit rest trans =
      match rest with
      | [] -> trans
      | s :: rest -> (
          match Hashtbl.find_opt tab s with
          | Some _ -> visit rest trans
          | None ->
              let () = Hashtbl.add tab s () in
              let m = nfa.next #-> s in
              let rest', m =
                EpsFA.CharMap.fold
                  (fun c s' (rest', m) ->
                    match c with
                    | None -> (StateSet.elements s' @ rest', m)
                    | Some c -> (rest', CharMap.add c s' m))
                  m ([], CharMap.empty)
              in
              visit (rest' @ rest) (nfa_union_charmap trans m))
    in
    visit (StateSet.elements states) CharMap.empty

  (** Remove eps via the powerset construction *)
  let eps_determinize : EpsFA.nfa -> dfa =
    let module M = Map.Make (StateSet) in
    fun nfa ->
      let fresh =
        let r = ref (_default_init_state : int) in
        fun () ->
          r := Int.succ !r;
          !r
      in
      let rec build states (map, ts, finals) =
        match M.find states map with
        | state -> (state, map, ts, finals)
        | exception Not_found ->
            let state = fresh () in
            let finals =
              if not (StateSet.is_empty (StateSet.inter states nfa.finals)) then
                StateSet.add state finals
              else finals
            in
            let map = M.add states state map in
            let tsn = eps_nfa_transitions states nfa in
            let map, ts, finals =
              CharMap.fold
                (fun c ss (map, ts, finals) ->
                  let dst, map, ts, finals = build ss (map, ts, finals) in
                  let ts = dfa_next_insert state c dst ts in
                  (map, ts, finals))
                tsn (map, ts, finals)
            in
            (state, map, ts, finals)
      in
      let start, _, trans, finals =
        build nfa.start (M.empty, StateMap.empty, StateSet.empty)
      in
      { start; finals; next = trans }

  (** Conversion to DFA via the powerset construction *)
  let determinize : nfa -> dfa =
    let module M = Map.Make (StateSet) in
    fun nfa ->
      let fresh =
        let r = ref (_default_init_state : int) in
        fun () ->
          r := Int.succ !r;
          !r
      in
      let rec build states (map, ts, finals) =
        match M.find states map with
        | state -> (state, map, ts, finals)
        | exception Not_found ->
            let state = fresh () in
            let finals =
              if not (StateSet.is_empty (StateSet.inter states nfa.finals)) then
                StateSet.add state finals
              else finals
            in
            let map = M.add states state map in
            let tsn = nfa_transitions states nfa in
            let map, ts, finals =
              CharMap.fold
                (fun c ss (map, ts, finals) ->
                  let dst, map, ts, finals = build ss (map, ts, finals) in
                  let ts = dfa_next_insert state c dst ts in
                  (map, ts, finals))
                tsn (map, ts, finals)
            in
            (state, map, ts, finals)
      in

      let start, _, trans, finals =
        build nfa.start (M.empty, StateMap.empty, StateSet.empty)
      in
      { start; finals; next = trans }

  (** Brzozowski's DFA minimization algorithm:
    reverse DFA to build an NFA and determinize, then do the same again *)
  let minimize g = determinize (reverse (determinize (reverse g)))

  (** Complement *)

  (* let complete_dfa (ctx : C.t list) (dfa : dfa) = *)
  (*   determinize @@ complete_nfa ctx @@ force_nfa dfa *)

  let swap_dfa (dfa : dfa) : dfa =
    let finals =
      dfa_fold_states
        (fun s res ->
          if StateSet.mem s dfa.finals then res else StateSet.add s res)
        dfa StateSet.empty
    in
    { start = dfa.start; finals; next = dfa.next }

  let swap_nfa (nfa : nfa) : nfa =
    let finals =
      nfa_fold_states
        (fun s res ->
          if StateSet.mem s nfa.finals then res else StateSet.add s res)
        nfa StateSet.empty
    in
    { start = nfa.start; finals; next = nfa.next }

  let complement_dfa (ctx : C.t list) (dfa : dfa) =
    swap_dfa @@ complete_dfa ctx dfa

  let complement_nfa (ctx : C.t list) (nfa : nfa) =
    swap_nfa @@ complete_nfa ctx nfa

  let complement_eps_nfa (ctx : C.t list) (eps_nfa : EpsFA.nfa) =
    force_eps_nfa @@ force_nfa @@ complement_dfa ctx (eps_determinize eps_nfa)

  (** binary operations *)
  let union_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    let nfa1, nfa2 = mk_disjoint_nfa (nfa1, nfa2) in
    {
      start = StateSet.union nfa1.start nfa2.start;
      finals = StateSet.union nfa1.finals nfa2.finals;
      next = nfa_union_next nfa1.next nfa2.next;
    }

  let union_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    let nfa1, nfa2 = EpsFA.mk_disjoint_nfa (nfa1, nfa2) in
    {
      start = StateSet.union nfa1.start nfa2.start;
      finals = StateSet.union nfa1.finals nfa2.finals;
      next = EpsFA.nfa_union_next nfa1.next nfa2.next;
    }

  let union_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    minimize @@ determinize @@ union_nfa (force_nfa dfa1) (force_nfa dfa2)

  let intersect_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    let dfa1 = normalize_dfa dfa1 in
    let dfa2 = normalize_dfa dfa2 in
    let num2 = num_states_dfa dfa2 in
    let mk_p (n1 : state) (n2 : state) = Int.add n2 @@ Int.mul num2 n1 in
    let fst_p p = Int.div p num2 in
    let snd_p p = Int.rem p num2 in
    let seen = Hashtbl.create 1000 in
    let tbl = ref StateMap.empty in
    let update_tbl (s, c, d) =
      tbl :=
        StateMap.update s
          (function
            | None -> Some (CharMap.singleton c d)
            | Some charmap -> Some (CharMap.add c d charmap))
          !tbl
    in
    let rec visit state =
      if not (Hashtbl.mem seen state) then
        let () = Hashtbl.add seen state () in
        let charmap1 = dfa1.next #-> (fst_p state) in
        let charmap2 = dfa2.next #-> (snd_p state) in
        CharMap.iter
          (fun c d1 ->
            match CharMap.find_opt c charmap2 with
            | None -> ()
            | Some d2 ->
                let d = mk_p d1 d2 in
                update_tbl (state, c, d);
                visit d)
          charmap1
    in
    let start = mk_p dfa1.start dfa2.start in
    let () = visit start in
    let finals =
      StateSet.fold
        (fun s1 ->
          StateSet.fold (fun s2 -> StateSet.add (mk_p s1 s2)) dfa2.finals)
        dfa1.finals StateSet.empty
    in
    let res = { start; finals; next = !tbl } in
    minimize res

  let intersect_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    force_nfa @@ intersect_dfa (determinize nfa1) (determinize nfa2)

  let intersect_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    force_eps_nfa @@ force_nfa
    @@ intersect_dfa (eps_determinize nfa1) (eps_determinize nfa2)

  let concat_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    let eps_nfa1, eps_nfa2 = EpsFA.mk_disjoint_nfa (nfa1, nfa2) in
    let next = EpsFA.nfa_union_next eps_nfa1.next eps_nfa2.next in
    let next =
      StateSet.fold
        (fun final ->
          StateSet.fold (EpsFA.nfa_next_insert final None) eps_nfa2.start)
        eps_nfa1.finals next
    in
    let eps_nfa : EpsFA.nfa =
      { start = eps_nfa1.start; finals = eps_nfa2.finals; next }
    in
    eps_nfa

  let _concat_nfa (nfa1 : nfa) (nfa2 : nfa) : dfa =
    let eps_nfa = concat_eps_nfa (force_eps_nfa nfa1) (force_eps_nfa nfa2) in
    minimize (eps_determinize eps_nfa)

  let concat_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    force_nfa (_concat_nfa nfa1 nfa2)

  let concat_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    _concat_nfa (force_nfa dfa1) (force_nfa dfa2)

  let kleene_eps_nfa (nfa : EpsFA.nfa) : EpsFA.nfa =
    let nfa = EpsFA.normalize_nfa nfa in
    let num = EpsFA.num_states_nfa nfa in
    let new_start = num in
    let new_final = num + 1 in
    let next =
      StateSet.fold (EpsFA.nfa_next_insert new_start None) nfa.start nfa.next
    in
    let next = EpsFA.nfa_next_insert new_start None new_final next in
    let next =
      StateSet.fold
        (fun final -> EpsFA.nfa_next_insert final None new_start)
        nfa.finals next
    in
    let next =
      StateSet.fold
        (fun final -> EpsFA.nfa_next_insert final None new_final)
        nfa.finals next
    in
    let eps_nfa : EpsFA.nfa =
      {
        start = StateSet.singleton new_start;
        finals = StateSet.singleton new_final;
        next;
      }
    in
    eps_nfa

  let _kleene_nfa (nfa : nfa) : dfa =
    let eps_nfa : EpsFA.nfa = kleene_eps_nfa (force_eps_nfa nfa) in
    minimize (eps_determinize eps_nfa)

  let kleene_nfa (nfa : nfa) : nfa = force_nfa (_kleene_nfa nfa)
  let kleene_dfa (dfa : dfa) : dfa = _kleene_nfa (force_nfa dfa)

  let multi_char_dfa (cs : C.t list) : dfa =
    let start = _default_init_state in
    let final = start + 1 in
    let next =
      List.fold_right (fun c -> dfa_next_insert start c final) cs StateMap.empty
    in
    { start; finals = StateSet.singleton final; next }

  let multi_char_nfa (cs : C.t list) : nfa = force_nfa (multi_char_dfa cs)

  let multi_char_eps_nfa (cs : C.t list) : EpsFA.nfa =
    force_eps_nfa (multi_char_nfa cs)

  let eps_lit_dfa =
    {
      start = _default_init_state;
      finals = StateSet.singleton _default_init_state;
      next = StateMap.empty;
    }

  let eps_lit_nfa : nfa = force_nfa eps_lit_dfa
  let eps_lit_eps_nfa : EpsFA.nfa = force_eps_nfa eps_lit_nfa

  let emp_lit_dfa : dfa =
    {
      start = _default_init_state;
      finals = StateSet.empty;
      next = StateMap.empty;
    }

  let rec compile_regex_to_eps_nfa (r : C.t raw_regex) : EpsFA.nfa option =
    match r with
    | Empty -> None
    | Eps -> Some eps_lit_eps_nfa
    | MultiChar [] -> None
    | MultiChar cs -> Some (multi_char_eps_nfa cs)
    | Alt (r1, r2) -> (
        match (compile_regex_to_eps_nfa r1, compile_regex_to_eps_nfa r2) with
        | None, r2 -> r2
        | r1, None -> r1
        | Some r1, Some r2 -> Some (union_eps_nfa r1 r2))
    | Inters (r1, r2) -> (
        match (compile_regex_to_eps_nfa r1, compile_regex_to_eps_nfa r2) with
        | None, _ | _, None -> None
        | Some r1, Some r2 -> Some (intersect_eps_nfa r1 r2))
    | Comple (cs, r) -> (
        match compile_regex_to_eps_nfa r with
        | None -> compile_regex_to_eps_nfa (Star (MultiChar cs))
        | Some r -> Some (complement_eps_nfa cs r))
    | Seq (r1, r2) -> (
        match (compile_regex_to_eps_nfa r1, compile_regex_to_eps_nfa r2) with
        | None, _ | _, None -> None
        | Some r1, Some r2 -> Some (concat_eps_nfa r1 r2))
    | Star r -> (
        match compile_regex_to_eps_nfa r with
        | None -> None
        | Some r -> Some (kleene_eps_nfa r))

  let compile_regex_to_dfa (r : C.t raw_regex) : dfa =
    match compile_regex_to_eps_nfa r with
    | None -> emp_lit_dfa
    | Some r -> eps_determinize r
end
