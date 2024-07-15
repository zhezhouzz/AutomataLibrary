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
