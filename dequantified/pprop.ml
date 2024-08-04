open Language
open Zzdatatype.Datatype

let const_to_p_const = function
  | U -> PUnit
  | B b -> PBool b
  | I i -> PInt i
  | SetLiteral _ -> _failatwith __FILE__ __LINE__ "die"
  | _ -> _failatwith __FILE__ __LINE__ "die"

let rec typed_lit_to_p_expr lit = (lit_to_p_expr lit.x) #: lit.ty

and lit_to_p_expr = function
  | AC c -> PConst (const_to_p_const c)
  | AVar id -> Pid id
  | AAppOp (op, args) ->
      let args = List.map typed_lit_to_p_expr args in
      PApp { pfunc = op; args }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_p_not a = mk_p_app "!" #: (Nt.mk_arr Nt.Ty_bool Nt.Ty_bool) [ a ]

let prop_to_p_prop p =
  let rec aux = function
    | Lit lit -> typed_lit_to_p_expr lit
    | Implies (a, b) -> aux (Or [ Not a; b ])
    | Ite (a, b, c) -> aux (Or [ And [ a; b ]; And [ Not a; c ] ])
    | Not a -> mk_p_not (aux a)
    | And es -> (
        match List.map aux es with
        | [] -> _failatwith __FILE__ __LINE__ "die"
        | [ e ] -> e
        | e :: es ->
            List.fold_left
              (fun res e ->
                mk_p_app
                  "&&"
                  #: (Nt.construct_arr_tp
                        ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
                  [ res; e ])
              e es)
    | Or es -> (
        match List.map aux es with
        | [] -> _failatwith __FILE__ __LINE__ "die"
        | [ e ] -> e
        | e :: es ->
            List.fold_left
              (fun res e ->
                mk_p_app
                  "||"
                  #: (Nt.construct_arr_tp
                        ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
                  [ res; e ])
              e es)
    | Iff (a, b) ->
        mk_p_app
          "==" #: (Nt.construct_arr_tp ([ Nt.Ty_bool; Nt.Ty_bool ], Nt.Ty_bool))
          [ aux a; aux b ]
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  aux p

let input_name = "input"
let prop_func_name (op, i) = spf "prop_%s_%i" op i

let _mk_p_prop_function_decl qvs (vs, prop) =
  let input = input_name #: (mk_p_record_ty vs) in
  let prepare =
    List.map (fun v -> mk_p_assign (mk_pid v, mk_field (mk_pid input) v.x)) vs
  in
  {
    params = qvs @ [ input ];
    local_vars = vs;
    body = mk_p_seqs prepare (mk_return @@ prop_to_p_prop prop);
  }

type pprop = string * int * (Nt.t, string) typed list * Nt.t prop

let global_event_name = "_global_"

let global_prop_func_decl i =
  (prop_func_name (global_event_name, i)) #: Nt.Ty_bool

let _mk_p_global_prop_function_decl i qvs prop =
  ( global_prop_func_decl i,
    { params = qvs; local_vars = []; body = mk_return @@ prop_to_p_prop prop }
  )
