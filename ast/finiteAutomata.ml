open Common
open Sugar

type 'a automaton = {
  state_bound : (int * int); (* a continue range *)
  init_states : int;
  final_states : int list;
  total_labels : 'a list;
  transition_map : (int, 'a option * int) Hashtbl.t;
}

(* type 'a dfa = { *)
(*   initial_state : int; *)
(*   final_states : int list; *)
(*   total_states : int list; *)
(*   total_labels : 'a list; *)
(*   d_transition_map : (int * 'a, int) Hashtbl.t; *)
(* } *)

(* let automata_dump_to_dfa *)
(*     { initial_state; final_states; total_states; total_labels; transition_map } *)
(*     = *)
(*   let d_transition_map = *)
(*     Hashtbl.create (List.length total_labels * List.length total_states) *)
(*   in *)
(*   let () = *)
(*     Hashtbl.iter *)
(*       (fun s (a, d) -> *)
(*         match a with *)
(*         | None -> _failatwith __FILE__ __LINE__ "die" *)
(*         | Some label -> ( *)
(*             match Hashtbl.find_opt d_transition_map (s, label) with *)
(*             | None -> Hashtbl.add d_transition_map (s, label) d *)
(*             | Some _ -> _failatwith __FILE__ __LINE__ "die")) *)
(*       transition_map *)
(*   in *)
(*   { initial_state; final_states; total_states; total_labels; d_transition_map } *)

let rename_state (bound: int) (a: 'a automata) =
  let shift x = x + bound - (fst a.state_bound) in
  let final_states = List.map shift a.final_states in
  let tot

(* let connect (a1: 'a automaton) (a2: 'a automaton) = *)

(* let from_regex (regex: 'a regex) = *)
(*   let regex = in *)
(*   let rec gather  *)
