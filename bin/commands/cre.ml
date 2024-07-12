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

let test_fa = function
  | MFAImp { name; automata } ->
      let regex = qregex2regex automata in
      let ctx = [ "a"; "b"; "c" ] in
      let nfa = StrAutomata.compile ctx regex in
      let () =
        print_endline "NFA: ";
        StrAutomata.layout_nfa nfa
      in
      let dfa = StrAutomata.determinize nfa in
      let () =
        print_endline "DFA: ";
        StrAutomata.layout_dfa dfa
      in
      let dfa = StrAutomata.minimize dfa in
      let () =
        print_endline "DFA: ";
        StrAutomata.layout_dfa dfa
      in
      let nfa' = StrAutomata.complete_nfa ctx (StrAutomata.inject dfa) in
      let () =
        print_endline "Complete NFA: ";
        StrAutomata.layout_nfa nfa'
      in
      let dfa' = StrAutomata.determinize nfa' in
      let () =
        print_endline "Complete DFA: ";
        StrAutomata.layout_dfa dfa'
      in
      let dfa' = StrAutomata.swap_dfa dfa' in
      let () =
        print_endline "Complement DFA: ";
        StrAutomata.layout_dfa dfa'
      in
      let dfa' = StrAutomata.normalize_dfa dfa' in
      let () =
        print_endline "Complement DFA: ";
        StrAutomata.layout_dfa dfa'
      in
      let dfa'' =
        StrAutomata.union_dfa StrAutomata.(determinize @@ compile ctx AnyA) dfa
      in
      let () =
        print_endline "Union DFA: ";
        StrAutomata.layout_dfa dfa''
      in
      ()
  | _ -> failwith "die"

let get_fa_by_name code n =
  let tmp =
    List.filter_map
      (function
        | MFAImp { name; automata } ->
            if String.equal name n then Some (qregex2regex automata) else None
        | _ -> None)
      code
  in
  List.nth tmp 0

let test_fa2 code =
  let open StrAutomata in
  let a1 = get_fa_by_name code "a1" in
  let b1 = get_fa_by_name code "b1" in
  let nfa1 = compile [ "a"; "b" ] a1 in
  let nfa2 = compile [] b1 in
  let () =
    print_endline "NFA1: ";
    layout_nfa nfa1
  in
  let () =
    print_endline "NFA2: ";
    layout_nfa nfa2
  in
  let dfa1 = minimize @@ determinize @@ compile [ "a"; "b" ] a1 in
  let dfa2 = minimize @@ determinize @@ compile [] b1 in
  let () =
    print_endline "DFA1: ";
    layout_dfa dfa1
  in
  let () =
    print_endline "DFA2: ";
    layout_dfa dfa2
  in
  let dfa12 = intersect_dfa dfa1 dfa2 in
  let () =
    print_endline "DFA1 intersect DFA2: ";
    layout_dfa dfa12
  in
  let dfa12 = minimize dfa12 in
  let () =
    print_endline "DFA1 intersect DFA2: ";
    layout_dfa dfa12
  in
  ()

let test_fa3 code =
  let open StrAutomata in
  let a1 = get_fa_by_name code "a1" in
  let dfa1 = compile2dfa [ "a"; "b" ] a1 in
  let () =
    print_endline "DFA1: ";
    layout_dfa dfa1
  in
  ()

let read_automata source_file () =
  let code = read_ocaml_file source_file () in
  let () = Printf.printf "%s\n" @@ layout_opt_structure code in
  let _, code = struct_check emp code in
  let () = Printf.printf "%s\n" @@ layout_structure code in
  let () = test_fa3 code in
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
      (* ("read-sfa", one_param "read_sfa" read_sfa); *)
    ]
