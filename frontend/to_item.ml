(* open Common *)
open Syntax
open Ocaml5_parser
open Parsetree

(* open Mutils *)
open Zzdatatype.Datatype
open To_id

let constrant_str = "const"
let inst_str = "inst"

(* type 't ocaml_item = *)
(*   | MTyDecl of type_declaration *)
(*   | MValDecl of ('t, string) typed *)
(*   | MMethodPred of ('t, string) typed *)
(*   | MAxiom of { name : string; prop : 't prop } *)
(*   (\* | MFuncImpRaw of { *\) *)
(*   (\*     name : ('t, string) typed; *\) *)
(*   (\*     if_rec : bool; *\) *)
(*   (\*     body : expression; *\) *)
(*   (\*   } *\) *)
(*   (\* | MFuncImp of { name : ('t, string) typed; if_rec : bool; body : expression } *\) *)
(*   | MAutomataImp of { name : string; automata : expression } *)
(* (\* | MRty of { is_assumption : bool; name : string; rty : expression } *\) *)

let ocaml_structure_item_to_item structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; pval_prim; pval_attributes; _ } ->
      Some
        (if String.equal pval_name.txt "method_predicates" then
           let mp = List.nth pval_prim 0 in
           MMethodPred mp #: (Some (Nt.core_type_to_t pval_type))
         else
           match pval_attributes with
           | [ x ] when String.equal x.attr_name.txt "method_pred" ->
               MMethodPred pval_name.txt #: (Some (Nt.core_type_to_t pval_type))
           | _ -> MValDecl pval_name.txt #: (Some (Nt.core_type_to_t pval_type)))
  | Pstr_type (_, [ type_dec ]) -> Some (To_type_dec.of_ocamltypedec type_dec)
  | Pstr_value (_, [ value_binding ]) ->
      Some
        (let name = id_of_pattern value_binding.pvb_pat in
         let expr = value_binding.pvb_expr in
         match value_binding.pvb_attributes with
         | [ x ] -> (
             match x.attr_name.txt with
             | "regex" ->
                 MFAImp
                   {
                     name;
                     automata =
                       To_qregex.of_expr (To_regex.of_expr id_of_expr) expr;
                   }
             | "sregex" ->
                 MSFAImp
                   {
                     name;
                     automata =
                       To_qregex.of_expr
                         (To_regex.of_expr To_sevent.of_expr)
                         expr;
                   }
             | "axiom" -> MAxiom { name; prop = To_prop.of_expr expr }
             | notation when String.equal notation constrant_str ->
                 MConstant
                   {
                     name = name #: None;
                     const = To_constant.expr_to_constant expr;
                   }
             | notation when String.equal notation inst_str ->
                 MInst { name; inst = To_inst.inst_of_expr expr }
             (* | "assert" -> *)
             (*     MRty *)
             (*       { is_assumption = false; name; rty = value_binding.pvb_expr } *)
             (* | "library" -> *)
             (*     MRty *)
             (*       { is_assumption = true; name; rty = value_binding.pvb_expr } *)
             | _ as x ->
                 _failatwith __FILE__ __LINE__
                 @@ spf
                      "syntax error: non known rty kind(%s), not axiom | \
                       assert | library"
                      x)
         | _ -> _failatwith __FILE__ __LINE__ "wrong syntax")
  | Pstr_attribute _ -> None
  | _ ->
      let () =
        Printf.printf "%s\n" (Pprintast.string_of_structure [ structure ])
      in
      _failatwith __FILE__ __LINE__ "translate not a func_decl"

let ocaml_structure_to_items structure =
  List.filter_map ocaml_structure_item_to_item structure

let layout_ct_opt = function
  | Some ct -> Nt.layout ct
  | None -> _failatwith __FILE__ __LINE__ "die"

let layout_opt_ty = function None -> "?" | Some t -> Nt.layout t

let layout_opt_item = function
  | MTyDecl _ -> _failatwith __FILE__ __LINE__ "die"
  | MMethodPred x ->
      spf "val[@method_predicate] %s: %s" x.x @@ layout_ct_opt x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ layout_ct_opt x.ty
  | MAxiom { name; prop } ->
      spf "let[@axiom] %s = %s" name (To_prop.layout_prop prop)
  | MFAImp { name; automata } ->
      spf "let[@regex] %s = %s" name
        (To_qregex.layout layout_opt_ty (To_regex.layout (fun x -> x)) automata)
  | MSFAImp { name; automata } ->
      spf "let[@sregex] %s = %s" name
        (To_qregex.layout layout_opt_ty
           (To_regex.layout To_sevent.layout)
           automata)
  | MConstant { name; const } ->
      spf "let[@%s] %s = %s" constrant_str name.x
        (To_constant.layout_constant const)
  | MInst { name; inst } ->
      spf "let[@%s] %s = %s" inst_str name
        (To_inst.layout_inst layout_opt_ty inst)
(* | MRty { is_assumption = false; name; rty } -> *)
(*     spf "let[@assert] %s = %s" name (Pprintast.string_of_expression rty) *)
(* | MRty { is_assumption = true; name; rty } -> *)
(*     spf "let[@library] %s = %s" name (Pprintast.string_of_expression rty) *)

let layout_item = function
  | MTyDecl _ -> _failatwith __FILE__ __LINE__ "die"
  | MMethodPred x -> spf "val[@method_predicate] %s: %s" x.x @@ Nt.layout x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MAxiom { name; prop } ->
      spf "let[@axiom] %s = %s" name (To_prop.layout_prop prop)
  | MFAImp { name; automata } ->
      spf "let[@regex] %s = %s" name
        (To_qregex.layout Nt.layout (To_regex.layout (fun x -> x)) automata)
  | MSFAImp { name; automata } ->
      spf "let[@sregex] %s = %s" name
        (To_qregex.layout Nt.layout (To_regex.layout To_sevent.layout) automata)
  | MConstant { name; const } ->
      spf "let[@%s] %s = %s" constrant_str name.x
        (To_constant.layout_constant const)
  | MInst { name; inst } ->
      spf "let[@%s] %s = %s" inst_str name (To_inst.layout_inst Nt.layout inst)

let layout_opt_structure l = spf "%s\n" (List.split_by "\n" layout_opt_item l)
let layout_structure l = spf "%s\n" (List.split_by "\n" layout_item l)
