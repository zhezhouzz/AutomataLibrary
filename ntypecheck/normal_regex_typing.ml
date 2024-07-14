open Language

type t = Nt.t

let bi_regex_check (type a b) (f : string -> t -> b)
    (label_check : t ctx -> a -> b) (ctx : t ctx) (regex : a regex) : b regex =
  let rec aux ctx regex =
    match regex with
    | EpsilonA -> EpsilonA
    | AnyA -> AnyA
    | EmptyA -> EmptyA
    | Atomic se -> Atomic (label_check ctx se)
    | MultiAtomic se -> MultiAtomic (List.map (label_check ctx) se)
    | LorA (t1, t2) -> LorA (aux ctx t1, aux ctx t2)
    | SetMinusA (t1, t2) -> SetMinusA (aux ctx t1, aux ctx t2)
    | LandA (t1, t2) -> LandA (aux ctx t1, aux ctx t2)
    | SeqA (t1, t2) -> SeqA (aux ctx t1, aux ctx t2)
    | StarA t -> StarA (aux ctx t)
    | ComplementA t -> ComplementA (aux ctx t)
    | DComplementA { atoms; body } ->
        DComplementA
          { atoms = List.map (label_check ctx) atoms; body = aux ctx body }
    | Ctx { atoms; body } ->
        Ctx { atoms = List.map (label_check ctx) atoms; body = aux ctx body }
    | CtxOp { op_names; body } ->
        let atoms =
          List.map
            (fun op_name ->
              match get_opt ctx op_name with
              | None ->
                  _failatwith __FILE__ __LINE__
                    (spf "event(%s) is not declared" op_name)
              | Some ty -> f op_name ty)
            op_names
        in
        Ctx { atoms; body = aux ctx body }
    (* CtxOp { op_names; body = aux ctx body } *)
  in
  aux ctx regex

let bi_symbolic_regex_check =
  bi_regex_check mk_top_sevent Normal_sevent_typing.bi_sevent_check

let bi_str_regex_check ctx regex =
  bi_regex_check (fun x _ -> x) (fun _ x -> x) ctx regex
