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

(* gather lits *)
(** For Nt.t typed*)

let mk_top_sevent (op : string) (ty : Nt.t) =
  let argsty, _ = Nt.destruct_arr_tp ty in
  let vs = vs_names (List.length argsty) in
  let vs = List.map (fun (x, ty) -> x #: ty) @@ List.combine vs argsty in
  EffEvent { op; vs; phi = mk_true }

open Zzdatatype.Datatype

type gathered_lits = {
  global_lits : Nt.t lit list;
  local_lits : ((Nt.t, string) typed list * Nt.t lit list) StrMap.t;
}

let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

let gathered_rm_dup { global_lits; local_lits } =
  let global_lits = List.slow_rm_dup Lit.eq_lit global_lits in
  let local_lits =
    StrMap.map
      (fun (vs, lits) -> (vs, List.slow_rm_dup Lit.eq_lit lits))
      local_lits
  in
  { global_lits; local_lits }

let gather_se { global_lits; local_lits } sevent =
  (* let () = Env.show_log "gather" @@ fun _ -> Printf.printf ">>>>> gather:\n" in *)
  match sevent with
  | GuardEvent phi ->
      { global_lits = Prop.get_lits phi @ global_lits; local_lits }
  | EffEvent { op; phi; vs } ->
      let lits = Prop.get_lits phi in
      let vs' = List.map (fun x -> x.x) vs in
      let is_contain_local_free lit =
        match List.interset ( == ) vs' @@ Lit.fv_lit_id lit with
        | [] -> false
        | _ -> true
      in
      let llits, glits = List.partition is_contain_local_free lits in
      let local_lits =
        StrMap.update op
          (fun l ->
            match l with
            | None -> Some (vs, llits)
            | Some (_, l) -> Some (vs, l @ llits))
          local_lits
      in
      let global_lits = global_lits @ glits in
      { global_lits; local_lits }

let compare_se se1 se2 =
  Sexplib.Sexp.compare
    (sexp_of_sevent Nt.sexp_of_t se1)
    (sexp_of_sevent Nt.sexp_of_t se2)
