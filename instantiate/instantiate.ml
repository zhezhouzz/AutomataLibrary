open Language
open Zzdatatype.Datatype

type res = (Nt.t, Nt.t sevent regex) machine

let interp (ctx : Nt.t inst ctx) (inst : Nt.t inst) : res =
  let binding = Hashtbl.create 10 in
  let rec aux = function
    | IVar name -> (
        match get_opt ctx name.x with
        | Some res -> res
        | None -> _failatwith __FILE__ __LINE__ (spf "undefined %s" name.x))
    | (IConst _ | IQregex _) as r -> r
    | IApp (r1, r2) -> (
        let r1, r2 = map2 aux (r1, r2) in
        match (r1, r2) with
        | IQregex (RPi { sort; body }), IConst c ->
            Hashtbl.add binding sort.x c;
            IQregex body
        | IQregex (RForall { qv; body }), IConst (I m) ->
            IQregex (subst_qregex_const body qv.x m)
        | _, _ -> _failatwith __FILE__ __LINE__ "die")
  in
  let inst = aux inst in
  let q =
    match inst with IQregex q -> q | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  to_machine binding q

let layout_quantifier binding qv =
  match StrMap.find_opt binding (Nt.layout qv.ty) with
  | Some c -> spf "(%s ∈ %s)." qv.x (layout_constant c)
  | None -> spf "%s:%s)." qv.x (Nt.layout qv.ty)

let layout_machine_ f { binding; reg } =
  let head =
    List.split_by "\n"
      (fun (name, qt, c) ->
        spf "%s(%s ∈ %s)"
          (Normalty.Connective.qt_pretty_layout qt)
          name (layout_constant c))
      binding
  in
  spf "%s\n%s" head (f reg)

let layout_symbolic_machine m = layout_machine_ layout_symbolic_regex m
let layout_sfa_machine m = layout_machine_ SFA.layout_dfa m

let interp_item (ctx : Nt.t inst ctx) (e : Nt.t item) :
    Nt.t inst ctx * (string * res) option =
  match e with
  | MTyDecl _ | MValDecl _ | MMethodPred _ | MAxiom _ | MFAImp _ -> (ctx, None)
  | MSFAImp { name; automata } ->
      (add_to_right ctx name #: (IQregex automata), None)
  | MConstant { name; const } ->
      (add_to_right ctx name.x #: (IConst const), None)
  | MInst { name; inst } -> (ctx, Some (name, interp ctx inst))

let interp_items (ctx : Nt.t inst ctx) (es : Nt.t item list) :
    Nt.t inst ctx * res StrMap.t =
  List.fold_left
    (fun (ctx, res) e ->
      (* let () = Printf.printf "item: %s\n" @@ layout_item e in *)
      (* let () = *)
      (*   Printf.printf "ctx.keys: %s\n" *)
      (*     (List.split_by_comma (fun x -> x) @@ List.map _get_x @@ to_list ctx) *)
      (* in *)
      let ctx, r = interp_item ctx e in
      match r with
      | None -> (ctx, res)
      | Some (name, inst) -> (ctx, StrMap.add name inst res))
    (ctx, StrMap.empty) es

let machines_to_fa_machines machines =
  StrMap.map
    (fun m ->
      let bmap, { binding; reg } =
        Desymbolic.desymbolic_machine (fun _ -> true) m
      in
      (* let () = Printf.printf " zz?: %s\n" @@ layout_symbolic_regex reg in *)
      let module DFA = DesymFA in
      let fa = DFA.compile2dfa reg in
      let () = Pp.printf "\n@{<bold>To DFA:@}\n%s\n" (DFA.layout_dfa fa) in
      let sfa = SFA.from_desym_dfa bmap fa in
      let () =
        Pp.printf "\n@{<bold>Back To SFA:@}\n%s\n" (SFA.layout_dfa sfa)
      in
      { binding; reg = sfa })
    machines
