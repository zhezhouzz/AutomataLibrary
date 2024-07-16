open Ast

let inst_with_const (inst : 't inst) (name : string) (c : constant) =
  let rec aux = function
    | IVar x when String.equal name x.x -> IConst c
    | IApp (a, b) -> IApp (aux a, aux b)
    | (IVar _ | IConst _ | IQregex _) as inst -> inst
  in
  aux inst

let inst_with_qregex (inst : 't inst) (name : string)
    (q : ('t, 't sevent) qregex) =
  let rec aux = function
    | IVar x when String.equal name x.x -> IQregex q
    | IApp (a, b) -> IApp (aux a, aux b)
    | (IVar _ | IConst _ | IQregex _) as inst -> inst
  in
  aux inst

let get_interpreted_sort binding qv =
  match Hashtbl.find_opt binding (Nt.layout qv.ty) with
  | Some c -> c
  | None -> _failatwith __FILE__ __LINE__ "die"

let to_machine tab q =
  let rec aux (binding, q) =
    match q with
    | RPi _ -> _failatwith __FILE__ __LINE__ "die"
    | RForall { qv; body } ->
        let binding =
          binding
          @ [ (qv.x, Normalty.Connective.Fa, get_interpreted_sort tab qv) ]
        in
        aux (binding, body)
    | RExists { qv; body } ->
        let binding =
          binding
          @ [ (qv.x, Normalty.Connective.Ex, get_interpreted_sort tab qv) ]
        in
        aux (binding, body)
    | Regex reg -> { binding; reg }
  in
  aux ([], q)
