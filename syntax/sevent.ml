open Ast
open Mtyped
open Sugar
open Prop

(* fv *)

let fv sevent =
  match sevent with
  | GuardEvent phi -> fv_prop phi
  | EffEvent { vs; phi; _ } ->
      Zzdatatype.Datatype.List.substract (typed_eq String.equal)
        ([] @ fv_prop phi)
        vs

(* subst *)

let subst_sevent (y : string) f sevent =
  match sevent with
  | GuardEvent phi -> GuardEvent (subst_prop y f phi)
  | EffEvent { op; vs; phi } ->
      if List.exists (fun x -> String.equal x.x y) vs then
        EffEvent { op; vs; phi }
      else EffEvent { op; vs; phi = subst_prop y f phi }

let subst_sevent_instance y z sevent =
  subst_f_to_instance subst_sevent y z sevent

(* normalize name *)

let normalize_name = function
  | GuardEvent phi -> GuardEvent phi
  | EffEvent { op; vs; phi } ->
      let vs' = vs_names (List.length vs) in
      let tmp = _safe_combine __FILE__ __LINE__ vs vs' in
      let phi =
        List.fold_left
          (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi)
          phi tmp
      in
      let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in
      EffEvent { op; vs; phi }
