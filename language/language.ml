include Front
include Backend
module Nt = Normalty.Ntyped
(* module Nt = struct *)
(*   include Normalty.Frontend *)
(*   include Normalty.Ntyped *)
(* end *)

module MakeC (C : CHARAC) = struct
  open C

  type char_idx = {
    __id2c : (Int64.t, t) Hashtbl.t;
    __c2id : (t, Int64.t) Hashtbl.t;
    __counter : Int64.t ref;
  }

  let __incr __counter =
    let res = !__counter in
    __counter := Int64.add res 1L;
    res

  let init_char_map () : char_idx =
    {
      __counter = ref 0L;
      __c2id = Hashtbl.create 1000;
      __id2c = Hashtbl.create 1000;
    }

  let add_char_to_map { __counter; __c2id; __id2c } (c : t) =
    match Hashtbl.find_opt __c2id c with
    | None ->
        let id = __incr __counter in
        Hashtbl.add __c2id c id;
        Hashtbl.add __id2c id c
    | Some _ -> ()

  let id2c { __id2c; _ } = Hashtbl.find __id2c
  let c2id { __c2id; _ } = Hashtbl.find __c2id

  include C
end

module MakeA (C : CHARAC) = struct
  module Tmp = MakeAutomata (MakeC (C))
  include MakeAutomataDot (Tmp)
  include Tmp
end

module MakeAA (C : CHARAC) = struct
  include MakeA (C)

  let index_regex (regex : ('t, C.t) regex) : C.char_idx =
    let m = C.init_char_map () in
    let () = iter_label_in_regex (C.add_char_to_map m) regex in
    m

  let to_index_regex (m : C.char_idx) (regex : ('t, C.t) regex) :
      ('t, Int64.t) regex =
    map_label_in_regex (C.c2id m) regex

  let from_index_regex (m : C.char_idx) (regex : ('t, Int64.t) regex) :
      ('t, C.t) regex =
    map_label_in_regex (C.id2c m) regex

  open Core

  let save_as_digraph sfa filename =
    Format.fprintf
      (Format.formatter_of_out_channel @@ Out_channel.create filename)
      "%a@." format_digraph
      (digraph_of_nfa (inject sfa))
end

module StrAutomata = MakeAA (StringC)
module IdAutomata = MakeAA (Int64C)
module DesymFA = MakeAA (DesymLabel)

module SeventLabel = struct
  type t = Nt.t sevent

  let compare = compare_se
  let layout = pprintRaw
  let delimit_cotexnt_char = delimit_cotexnt_se
end

module SFA = struct
  include MakeAA (SeventLabel)

  let from_desym_dfa (f : DesymLabel.t list -> C.t list) (dfa : DesymFA.dfa) :
      dfa =
    let next = DesymFA.concretelize_dfa_aux (fun x -> x) dfa in
    let next =
      StateMap.map
        (fun m ->
          let seq = DesymFA.CharMap.to_seq m in
          let m =
            Seq.fold_left
              (fun res (c, d) ->
                StateMap.update d
                  (function None -> Some [ c ] | Some cs -> Some (c :: cs))
                  res)
              StateMap.empty seq
          in
          CharMap.of_seq @@ Seq.concat
          @@ Seq.map (fun (d, cs) ->
                 List.to_seq @@ List.map (fun c -> (c, d)) (f cs))
          @@ StateMap.to_seq m)
        next
    in
    let sfa =
      { start = dfa.start; finals = dfa.finals; next = construct_next next }
    in
    normalize_dfa sfa

  (* open Zzdatatype.Datatype *)

  let rename_sevent event_ctx (dfa : dfa) =
    let f = function
      | GuardEvent _ -> _failatwith __FILE__ __LINE__ "die"
      | EffEvent { op; vs; phi } ->
          let l =
            match get_opt event_ctx op with
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
    map_on_char_dfa dfa f
end
