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

  let index_regex (regex : C.t regex) : C.char_idx =
    let m = C.init_char_map () in
    let () = iter_label_in_regex (C.add_char_to_map m) regex in
    m

  let to_index_regex (m : C.char_idx) (regex : C.t regex) : Int64.t regex =
    map_label_in_regex (C.c2id m) regex

  let from_index_regex (m : C.char_idx) (regex : Int64.t regex) : C.t regex =
    map_label_in_regex (C.id2c m) regex
end

module StrAutomata = MakeAA (StringC)
module IdAutomata = MakeAA (Int64C)
module DesymFA = MakeAA (DesymLabel)

module SeventLabel = struct
  type t = Nt.t sevent

  let compare = compare_se
  let layout = pprintRaw
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
    { start = dfa.start; finals = dfa.finals; next = construct_next next }
end
