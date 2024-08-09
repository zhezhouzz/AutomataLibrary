include Front
include Backend
module Nt = Normalty.Ntyped
(* module Nt = struct *)
(*   include Normalty.Frontend *)
(*   include Normalty.Ntyped *)
(* end *)

module SeventLabel = struct
  type t = Nt.t sevent

  let compare = compare_se
  let layout = pprintRaw
  let delimit_cotexnt_char = delimit_cotexnt_se
end

module SFA = struct
  include MakeAA (SeventLabel)

  let from_desym_dfa (f : DesymFA.CharSet.t -> CharSet.t) (dfa : DesymFA.dfa) :
      dfa =
    let ss_next = DesymFA.dfa_next_to_ss_next dfa in
    let ss_next = StateMap.map (StateMap.map f) ss_next in
    let next = ss_next_to_next ss_next in
    let sfa = { start = dfa.start; finals = dfa.finals; next } in
    (* let () = Pp.printf "\n@{<bold>before normalize:@}\n%s\n" (layout_dfa sfa) in *)
    normalize_dfa sfa

  open Zzdatatype.Datatype

  let rename_sevent event_ctx (dfa : dfa) =
    let f = function
      | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
      | EffEvent { op; vs; phi } ->
          let l =
            match StrMap.find_opt event_ctx op with
            | Some (Nt.Ty_record l) -> l
            | None -> _failatwith __FILE__ __LINE__ (spf "die: None on %s" op)
            | Some ty ->
                _failatwith __FILE__ __LINE__ (spf "die: %s" (Nt.layout ty))
          in
          let vs' = List.map (fun (x, ty) -> x #: ty) l in
          (* let () = *)
          (*   Printf.printf "vs: %s\n" *)
          (*   @@ List.split_by_comma *)
          (*        (fun x -> spf "%s:%s" x.x (Nt.layout x.ty)) *)
          (*        vs *)
          (* in *)
          (* let () = *)
          (*   Printf.printf "vs': %s\n" *)
          (*   @@ List.split_by_comma *)
          (*        (fun x -> spf "%s:%s" x.x (Nt.layout x.ty)) *)
          (*        vs' *)
          (* in *)
          let phi' =
            List.fold_right
              (fun (v, v') -> subst_prop_instance v.x (AVar v'))
              (List.combine vs vs') phi
          in
          EffEvent { op; vs = vs'; phi = phi' }
    in
    dfa_map_c f dfa
end

let symbolic_dfa_to_event_name_dfa (dfa : SFA.dfa) =
  let open StrAutomata in
  let next =
    SFA.dfa_fold_transitions
      (fun (st, ch, dest) ->
        nfa_next_insert st (_get_sevent_name __FILE__ __LINE__ ch) dest)
      dfa StateMap.empty
  in
  let nfa : nfa =
    { start = StateSet.singleton dfa.start; finals = dfa.finals; next }
  in
  determinize nfa
