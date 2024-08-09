open Language
open Zzdatatype.Datatype

type sym_explore_ctx = {
  event_tyctx : Nt.t StrMap.t;
  event_kindctx : event_kind StrMap.t; (* the kind of these events *)
  world : world;
  request_bound : int;
  step_bound : int;
  checker : Nt.t prop -> bool;
  sat_solver : Nt.t prop -> bool;
}

let init_explore_ctx ~event_tyctx ~event_kindctx ~world ~step_bound
    ~request_bound =
  {
    event_tyctx;
    event_kindctx;
    world;
    step_bound;
    request_bound;
    checker = (fun p -> Prover.check_valid p);
    sat_solver = (fun p -> Prover.check_sat_bool p);
  }

let init_dummy_ctx ~event_tyctx ~event_kindctx ~world ~step_bound ~request_bound
    =
  let ctx =
    init_explore_ctx ~event_tyctx ~event_kindctx ~world ~step_bound
      ~request_bound
  in
  { ctx with sat_solver = (fun _ -> true); checker = (fun _ -> true) }

let layout_event_kindctx =
  StrMap.to_kv_list
  #> (List.split_by_comma (fun (x, kind) ->
          spf "%s:%s" x @@ layout_event_kind kind))

let layout_ctx ctx =
  let res =
    spf "event_kindctx:\n%s\n" @@ layout_event_kindctx ctx.event_kindctx
  in
  let res = spf "%srequest_bound:%i\n" res ctx.request_bound in
  let res = spf "%step_bound:%i\n" res ctx.step_bound in
  res

let layout_qautomata (world_prop, dfa) =
  let res = spf "world_prop:%s\n" @@ layout_prop world_prop in
  let res = spf "%s%s" res @@ SFA.layout_dfa dfa in
  res
