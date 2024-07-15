open Language
open Zzdatatype.Datatype

type res = { binding : constant StrMap.t; q : (Nt.t, Nt.t sevent) qregex }

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
  { binding = StrMap.of_seq @@ Hashtbl.to_seq binding; q }
