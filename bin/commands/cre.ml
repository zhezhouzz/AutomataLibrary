open Core
open Caux
open Language
open Zzdatatype.Datatype
open Ntypecheck

let parse = Ocaml5_parser.Frontend.parse

let read_ocaml_file source_file () =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:source_file in
  let code = ocaml_structure_to_items code in
  code

let read_source_file source_file () =
  let postfix = List.last @@ String.split source_file ~on:'.' in
  match postfix with
  | "ml" -> read_ocaml_file source_file ()
  | "p" -> Frontp.parse source_file
  | _ -> failwith @@ spf "wrong file extension *.%s" postfix

let get_fa_by_name code n =
  let tmp =
    List.filter_map
      (function
        | MFAImp { name; automata } ->
            if String.equal name n then Some (get_regex_from_qregex automata)
            else None
        | _ -> None)
      code
  in
  List.nth tmp 0

let get_sfa_by_name code n =
  let tmp =
    List.filter_map
      (function
        | MSFAImp { name; automata } ->
            if String.equal name n then Some (get_regex_from_qregex automata)
            else None
        | _ -> None)
      code
  in
  List.nth tmp 0

(* let test_fa2 code = *)
(*   let open StrAutomata in *)
(*   let a1 = get_fa_by_name code "a1" in *)
(*   let b1 = get_fa_by_name code "b1" in *)
(*   let nfa1 = compile [ "a"; "b" ] a1 in *)
(*   let nfa2 = compile [] b1 in *)
(*   let () = *)
(*     print_endline "NFA1: "; *)
(*     layout_nfa nfa1 *)
(*   in *)
(*   let () = *)
(*     print_endline "NFA2: "; *)
(*     layout_nfa nfa2 *)
(*   in *)
(*   let dfa1 = minimize @@ determinize @@ compile [ "a"; "b" ] a1 in *)
(*   let dfa2 = minimize @@ determinize @@ compile [] b1 in *)
(*   let () = *)
(*     print_endline "DFA1: "; *)
(*     layout_dfa dfa1 *)
(*   in *)
(*   let () = *)
(*     print_endline "DFA2: "; *)
(*     layout_dfa dfa2 *)
(*   in *)
(*   let dfa12 = intersect_dfa dfa1 dfa2 in *)
(*   let () = *)
(*     print_endline "DFA1 intersect DFA2: "; *)
(*     layout_dfa dfa12 *)
(*   in *)
(*   let dfa12 = minimize dfa12 in *)
(*   let () = *)
(*     print_endline "DFA1 intersect DFA2: "; *)
(*     layout_dfa dfa12 *)
(*   in *)
(*   () *)

let test_fa3 code =
  let open StrAutomata in
  let a1 = get_fa_by_name code "a1" in
  let a1 = delimit_context @@ desugar a1 in
  let m = index_regex a1 in
  let a1' = to_index_regex m a1 in
  let module IdA = IdAutomata in
  let dfa1 = IdA.compile2dfa a1' in
  let dfa1_dot = IdA.digraph_of_nfa (IdA.inject dfa1) in
  let () = Format.printf "%a@." format_digraph dfa1_dot in
  ()

let read_automata source_file () =
  let code = read_source_file source_file () in
  (* let () = Printf.printf "%s\n" @@ layout_opt_structure code in *)
  let _, code = struct_check emp code in
  (* let () = Printf.printf "%s\n" @@ layout_structure code in *)
  let () = test_fa3 code in
  ()

let test_sfa1 code =
  let srl = get_sfa_by_name code "poly_spec" in
  let srl = delimit_context @@ desugar srl in
  let bmap, rl = Desymbolic.desymbolic (fun _ -> true) srl in
  let () = Printf.printf "%s\n" @@ layout_desym_regex rl in
  let module DFA = DesymFA in
  let fa = DFA.compile2dfa rl in
  (* let () = DFA.save_as_digraph fa "tmp.dot" in *)
  let sfa = SFA.from_desym_dfa bmap fa in
  let () = Printf.printf "%s\n" @@ SFA.layout_dfa sfa in
  let () = SFA.save_as_digraph sfa "tmp.dot" in
  ()

let read_sfa source_file () =
  let code = read_source_file source_file () in
  let () = Printf.printf "%s\n" @@ layout_opt_structure code in
  let _, code = struct_check emp code in
  let () = Printf.printf "%s\n" @@ layout_structure code in
  let _, machines = Instantiate.interp_items emp code in
  let () =
    StrMap.iter
      (fun name m ->
        Printf.printf "machine %s:\n%s\n" name
        @@ Instantiate.layout_symbolic_machine m)
      machines
  in
  let machines = Instantiate.machines_to_fa_machines machines in
  (* let machine = StrMap.find "die" machines "client" in *)
  let () =
    StrMap.iter
      (fun name m ->
        let () =
          Printf.printf "machine %s:\n%s\n" name
          @@ Instantiate.layout_sfa_machine m
        in
        let () = SFA.save_as_digraph m.reg "tmp.dot" in
        ())
      machines
  in
  (* let () = test_sfa1 code in *)
  ()

let two_param message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      f meta_config_file source_file)

let one_param message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open source_file = anon ("source_code_file" %: regular_file) in
      f source_file)

let test =
  Command.group ~summary:"Poirot"
    [
      ("read-automata", one_param "read_automata" read_automata);
      ("read-sfa", one_param "read_sfa" read_sfa);
    ]
