open Ast
open Zzdatatype.Datatype

(** types in P lang is shown in a different way from our types. *)
let rec layout_pnt t =
  let open Nt in
  let rec aux = function
    | Ty_constructor (name, [ ty ]) when String.equal name "set" ->
        spf "set[%s]" (aux ty)
    | Ty_constructor (name, [ ty ]) when String.equal name "seq" ->
        spf "seq[%s]" (aux ty)
    | Ty_constructor (name, [ ty ]) when String.equal name "ref" -> aux ty
    | Ty_constructor (name, [ ty1; ty2 ]) when String.equal name "map" ->
        spf "map[%s, %s]" (aux ty1) (aux ty2)
    | Ty_tuple ts when List.length ts > 1 ->
        spf "(%s)" @@ List.split_by_comma aux ts
    | Ty_record l -> (
        match l with
        | [] -> _failatwith __FILE__ __LINE__ "bad record"
        | [ _ ] -> _failatwith __FILE__ __LINE__ "bad record"
        | (name, _) :: _ when String.equal name "0" ->
            let l = List.map snd l in
            spf "(%s)" @@ List.split_by_comma layout_pnt l
        | _ ->
            spf "(%s)"
            @@ List.split_by_comma (fun (a, b) -> layout_pnt_typed a b) l)
    | _ as t -> layout t
  in
  aux t

and layout_pnt_typed str x =
  match x with NT.Ty_unit -> str | _ -> spf "%s: %s" str (layout_pnt x)

let layout_pnt_typed_var x = spf "%s: %s" x.x (layout_pnt x.ty)

let layout_const = function
  | PBool b -> string_of_bool b
  | PInt i -> string_of_int i
  | PStr str -> spf "\"%s\"" str
  | PHalt -> "halt"
  | PRandomBool -> "$"
  | PUnit -> ""
  | PDefault nt -> spf "default(%s)" (layout_pnt nt)
(* | _ -> _failatwith __FILE__ __LINE__ "unimp" *)

let mk_indent n str = spf "%s%s" (String.init (n * 2) (fun _ -> ' ')) str
let mk_indent_line n str = spf "%s%s\n" (String.init (n * 2) (fun _ -> ' ')) str

let mk_indent_semicolon_line n str =
  spf "%s%s;\n" (String.init (n * 2) (fun _ -> ' ')) str

let rec layout_p_expr n = function
  | PThis -> "this"
  | PNull -> "null"
  | Pid id -> id.x
  | PConst c -> layout_const c
  | PApp { pfunc = { x = "add_set"; _ }; args = [ e1; e2 ] } ->
      spf "%s += (%s)" (layout_typed_p_expr 0 e1) (layout_typed_p_expr 0 e2)
  | PApp { pfunc; args }
    when List.exists (String.equal pfunc.x) p_infix_operator -> (
      match args with
      | [ e1; e2 ] ->
          spf "(%s %s %s)" (layout_typed_p_expr 0 e1) pfunc.x
            (layout_typed_p_expr 0 e2)
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | PApp { pfunc; args } ->
      spf "%s(%s)" pfunc.x (List.split_by_comma (layout_typed_p_expr 0) args)
  | PRecord l -> (
      match l with
      | [] -> _failatwith __FILE__ __LINE__ "die"
      | [ (name, _) ] when String.equal name "0" ->
          _failatwith __FILE__ __LINE__ "die"
      | [ (a, b) ] -> spf "(%s = %s,)" a (layout_typed_p_expr 0 b)
      | (name, _) :: _ when String.equal name "0" ->
          spf "(%s)"
            (List.split_by_comma
               (fun (_, b) -> spf "%s" (layout_typed_p_expr 0 b))
               l)
      | _ ->
          spf "(%s)"
            (List.split_by_comma
               (fun (a, b) -> spf "%s = %s" a (layout_typed_p_expr 0 b))
               l))
  | PField { record; field } ->
      spf "(%s).%s" (layout_typed_p_expr 0 record) field
  | PAccess { container; index } ->
      spf "%s[%s]"
        (layout_typed_p_expr 0 container)
        (layout_typed_p_expr 0 index)
  | PDeref e -> layout_typed_p_expr n e (* P don't show the dereference *)
  | PAssign { lvalue; rvalue } ->
      spf "%s = %s"
        (layout_typed_p_expr 0 lvalue)
        (layout_typed_p_expr 0 rvalue)
  | PSeq { rhs; body } ->
      let rhs = layout_typed_p_expr n rhs in
      spf "%s;\n%s" rhs (mk_indent n @@ layout_typed_p_expr n body)
  | PSend { dest; event_name; payload } ->
      spf "send %s, %s, %s"
        (layout_typed_p_expr 0 dest)
        event_name
        (layout_typed_p_expr 0 payload)
  | PReturn { x = PConst PHalt; _ } -> spf "raise halt"
  | PReturn e -> spf "return %s" (layout_typed_p_expr n e)
  | PGoto state -> spf "goto %s" state
  | PBreak -> "break"
  | ForeachSet { elem; set; body } ->
      let head =
        spf "foreach (%s in %s) {" elem.x (layout_typed_p_expr 0 set)
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head
        (mk_indent_semicolon_line (n + 1) @@ layout_typed_p_expr (n + 1) body)
        last
  | ForeachMap { key; map; body } ->
      let head =
        spf "foreach (%s in keys(%s)) {" key.x (layout_typed_p_expr 0 map)
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head
        (mk_indent_semicolon_line (n + 1) @@ layout_typed_p_expr (n + 1) body)
        last
  | PIf { condition; tbranch; fbranch = None } ->
      let head = spf "if (%s) {" (layout_typed_p_expr 0 condition) in
      let tbranch =
        mk_indent_semicolon_line (n + 1) @@ layout_typed_p_expr (n + 1) tbranch
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head tbranch last
  | PIf { condition; tbranch; fbranch = Some fbranch } ->
      let head = spf "if (%s) {" (layout_typed_p_expr 0 condition) in
      let tbranch =
        mk_indent_semicolon_line (n + 1) @@ layout_typed_p_expr (n + 1) tbranch
      in
      let mid = mk_indent n "} else {" in
      let fbranch =
        mk_indent_semicolon_line (n + 1) @@ layout_typed_p_expr (n + 1) fbranch
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s\n%s%s" head tbranch mid fbranch last
  | PLet _ -> _failatwith __FILE__ __LINE__ "unimp"

and layout_typed_p_expr n { x; _ } = layout_p_expr n x

let layout_p_func_ if_omit n { params; local_vars; body } =
  let params_str = List.split_by "," layout_pnt_typed_var params in
  let local_vars_str =
    List.split_by ""
      (fun x ->
        mk_indent_semicolon_line (n + 1)
        @@ spf "var %s" @@ layout_pnt_typed_var x)
      local_vars
  in
  let head =
    if if_omit && List.length params == 0 then " {\n"
    else layout_pnt_typed (spf "(%s)" params_str) body.ty ^ " {\n"
  in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s" head local_vars_str
    (mk_indent_semicolon_line (n + 1) (layout_typed_p_expr (n + 1) body))
    last

let layout_p_func = layout_p_func_ false

let layout_state_label = function
  | Hot -> "hot"
  | Cold -> "cold"
  | Start -> "start"

let layout_func_label = function
  | Plain -> "plain"
  | Entry -> "entry"
  | Exit -> "exit"
  | Listen name -> spf "on %s do" name

let layout_p_state n { name; state_label; state_body } =
  let prefix = List.split_by " " layout_state_label state_label in
  let state_body_str =
    List.split_by ""
      (fun (l, f) ->
        mk_indent_line (n + 1)
        @@ spf "%s %s" (layout_func_label l.x) (layout_p_func_ true (n + 1) f))
      state_body
  in
  let head = mk_indent_line n @@ spf "%s state %s {" prefix name in
  let last = mk_indent_line n "}" in
  spf "%s%s%s" head state_body_str last

let layout_p_machine n { name; local_vars; local_funcs; states } =
  let local_funcs_str =
    List.split_by ""
      (fun (x, f) ->
        mk_indent (n + 1) @@ spf "fun %s %s" x.x (layout_p_func (n + 1) f))
      local_funcs
  in
  let local_vars_str =
    List.split_by ""
      (fun x ->
        mk_indent_semicolon_line (n + 1)
        @@ spf "var %s" @@ layout_pnt_typed_var x)
      local_vars
  in
  let states_str = List.split_by "" (layout_p_state (n + 1)) states in
  let head = mk_indent_line n @@ spf "machine %s {" name in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s%s" head local_vars_str states_str local_funcs_str last

let layout_global_function n (name, f) =
  mk_indent_line n @@ spf "fun %s = %s" name.x (layout_p_func n f)

let layout_item = function
  | PPrimFuncDecl _ -> ""
  | PTypeDecl x ->
      mk_indent_semicolon_line 0 @@ spf "type %s = %s" x.x (layout_pnt x.ty)
  | PEventDecl x ->
      mk_indent_semicolon_line 0 @@ spf "event %s: %s" x.x (layout_pnt x.ty)
  | PMachine m -> layout_p_machine 0 m
  | PGlobalFunc (name, f) -> layout_global_function 0 (name, f)

let layout_p_program prog = List.split_by "" layout_item prog
