open Common
open Zzdatatype.Datatype
open Language
open SFA
open Explore

module MPath = struct
  type multi_ch = {
    op : string;
    vs : (Nt.t, string) typed list;
    phis : Nt.t prop list;
  }

  type path =
    | PathEmpty of state list
    | PathCons of { prefix : path; ch : multi_ch; dest : state list }

  let append prefix (ch, dest) = PathCons { prefix; ch; dest }

  let to_event_list =
    let rec aux rev = function
      | PathEmpty _ -> List.rev rev
      | PathCons { prefix; ch; _ } -> aux (ch :: rev) prefix
    in
    aux []

  let to_event_name_list l = to_event_list l |> List.map (fun x -> x.op)
  let length l = List.length @@ to_event_list l
  let end_point = function PathEmpty s -> s | PathCons { dest; _ } -> dest

  let rec start_point = function
    | PathEmpty s -> s
    | PathCons { prefix; _ } -> start_point prefix

  let layout_ layout_ch layout_state =
    let rec aux = function
      | PathEmpty s -> layout_state s
      | PathCons { prefix; ch; dest } ->
          spf "%s =>> %s =>> %s" (aux prefix) (layout_ch ch) (layout_state dest)
    in
    aux

  let layout_op =
    (List.split_by " =>> " (fun x -> x))#.List.rev#.to_event_name_list

  (* let layout_op = layout_ (_get_sevent_name __FILE__ __LINE__) string_of_int *)
  let layout_paths_op = List.split_by "\n" layout_op

  let rec front_destruct_opt = function
    | PathEmpty _ -> None
    | PathCons { prefix = PathEmpty start; ch; dest } ->
        Some ((start, ch, dest), PathEmpty dest)
    | PathCons { prefix; ch; dest } -> (
        match front_destruct_opt prefix with
        | None -> _failatwith __FILE__ __LINE__ "die"
        | Some (tran, prefix) -> Some (tran, PathCons { prefix; ch; dest }))

  let ch_to_chs { op; vs; phis } =
    List.map (fun phi -> EffEvent { op; vs; phi }) phis

  let to_paths =
    let rec aux = function
      | PathEmpty s -> List.map (fun s -> Path.PathEmpty s) s
      | PathCons { prefix; ch; dest } ->
          let prefix = aux prefix in
          let ch = ch_to_chs ch in
          List.map (fun (prefix, (ch, dest)) ->
              Path.PathCons { prefix; ch; dest })
          @@ List.combine prefix (List.combine ch dest)
    in
    aux

  let check (sat_solver : Nt.t prop -> bool) world
      (world_props : Nt.t prop list) (ch : multi_ch) =
    let body =
      smart_and
      @@ List.map (fun (p1, p2) -> Implies (p1, p2))
      @@ List.combine world_props ch.phis
    in
    let rec aux world =
      match world with
      | WState -> body
      | WMap { qv; world; _ } -> Forall { qv; body = aux world }
      | WSingle { qv; world; _ } -> Exists { qv; body = aux world }
    in
    let query = aux world in
    sat_solver query
end

type path = MPath.path

let terminate_filter (dfa : dfa list) (p : path) =
  let end_points = MPath.end_point p in
  List.combine dfa end_points
  |> List.for_all (fun (dfa, en) -> StateSet.mem en dfa.finals)

let last_non_request_filter (ctx : sym_explore_ctx) (p : path) =
  match p with
  | PathEmpty _ -> true
  | PathCons { ch; _ } -> (
      match StrMap.find "die" ctx.event_kindctx ch.op with
      | Req -> false
      | Resp | Hidden -> true)

let request_length_filter (ctx : sym_explore_ctx) =
  MPath.to_event_name_list
  #> (List.filter
        (StrMap.find "die" ctx.event_kindctx) #> ( function
        | Req -> true
        | _ -> false ))
  #> List.length
  #> (fun n -> n <= ctx.request_bound)

let path_length_filter n p = MPath.length p <= n

(* NOTE:
   dfa should be complete;
   although we have filter function; we still set a maximal bound to avoid finite loop
*)

let _default_path_lengt_bound = 200

let dfs_with_filter ctx (dfa : (Nt.t prop * dfa) list) (filter : path -> bool)
    (res_filter : path -> bool) =
  let world_props = List.map fst dfa in
  let dfa = List.map snd dfa in
  let rec dfs (fuel : int) (cur : path) =
    if fuel <= 0 || not (filter cur) then None
    else if res_filter cur then Some cur
    else
      let en = MPath.end_point cur in
      let nexts =
        List.map (fun (dfa, en) -> dfa.next #-> en) @@ List.combine dfa en
      in
      let rec aux res nexts =
        match (res, nexts) with
        | None, [] -> _failatwith __FILE__ __LINE__ "die"
        | None, next :: nexts ->
            CharMap.fold
              (fun se dest p ->
                match p with
                | Some p -> Some p
                | None ->
                    let op, vs, phi = _get_sevent_fields __FILE__ __LINE__ se in
                    aux (Some (op, vs, [ phi ], [ dest ])) nexts)
              next None
        | Some (op, vs, phis, dests), [] ->
            let ch = MPath.{ op; vs; phis } in
            if MPath.check ctx.sat_solver ctx.world world_props ch then
              let p = MPath.(append cur ({ op; vs; phis }, dests)) in
              dfs (fuel - 1) p
            else None
        | Some (op, vs, phis, dests), next :: nexts ->
            CharMap.fold
              (fun se dest p ->
                match p with
                | Some p -> Some p
                | None ->
                    let op', _, phi = _get_sevent_fields __FILE__ __LINE__ se in
                    if String.equal op' op then
                      aux
                        (Some (op, vs, phis @ [ phi ], dests @ [ dest ]))
                        nexts
                    else None)
              next None
      in
      aux None nexts
  in
  let start = MPath.(PathEmpty (List.map (fun dfa -> dfa.start) dfa)) in
  dfs _default_path_lengt_bound start

let mexplore_counterexample_paths (ctx : sym_explore_ctx) dfa =
  let* res =
    dfs_with_filter ctx dfa
      (request_length_filter ctx &&& path_length_filter ctx.step_bound)
      (terminate_filter (List.map snd dfa) &&& last_non_request_filter ctx)
  in
  let paths = MPath.to_paths res in
  let worlds = List.map fst dfa in
  Some (List.combine worlds paths)
