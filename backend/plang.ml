open Ast
open Zzdatatype.Datatype

let layout_const = function
  | PBool b -> string_of_bool b
  | PInt i -> string_of_int i
  | PStr str -> spf "\"%s\"" str
  | PNull -> "null"
  | PHalt -> "halt"
  | PThis -> "this"
  | PRandomBool -> "$"
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

let mk_indent n str = spf "%s%s" (String.init (n * 2) (fun _ -> ' ')) str
let mk_indent_line n str = spf "%s%s\n" (String.init (n * 2) (fun _ -> ' ')) str

let mk_indent_semicolon_line n str =
  spf "%s%s;\n" (String.init (n * 2) (fun _ -> ' ')) str

let rec layout_p_expr n = function
  | Pid id -> id.x
  | PConst c -> layout_const c.x
  | PApp { pfunc; args }
    when List.exists (String.equal pfunc.x) p_infix_operator -> (
      match args with
      | [ e1; e2 ] ->
          spf "(%s %s %s)" (layout_typed_p_expr 0 e1) pfunc.x
            (layout_typed_p_expr 0 e2)
      | _ -> _failatwith __FILE__ __LINE__ "die")
  | PApp { pfunc; args } ->
      spf "%s(%s)" pfunc.x (List.split_by_comma (layout_typed_p_expr 0) args)
  | PRecord l ->
      spf "(%s)"
        (List.split_by_comma
           (fun (a, b) -> spf "%s = %s" a (layout_typed_p_expr 0 b))
           l)
  | PField { record; field } ->
      spf "(%s).%s" (layout_typed_p_expr 0 record) field
  | PAssign { lvalue; rvalue } ->
      spf "%s = %s"
        (layout_typed_p_expr 0 lvalue)
        (layout_typed_p_expr 0 rvalue)
  | PSeq { rhs; body } ->
      let rhs = layout_typed_p_expr n rhs in
      spf "%s;\n%s" rhs (mk_indent n @@ layout_typed_p_expr n body)
  | PReturn e -> spf "return %s" (layout_typed_p_expr n e)
  | PGoto state -> spf "goto %s" state
  | PLet _ -> _failatwith __FILE__ __LINE__ "unimp"

and layout_typed_p_expr n { x; _ } = layout_p_expr n x

let layout_p_func n { params; local_vars; body } =
  let params_str = List.split_by "," (fun x -> spf "%s: int" x.x) params in
  let local_vars_str =
    List.split_by ""
      (fun x -> mk_indent_semicolon_line (n + 1) @@ spf "var %s: int" x.x)
      local_vars
  in
  let head = spf "(%s) = {\n" params_str in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s" head local_vars_str
    (mk_indent_semicolon_line (n + 1) (layout_typed_p_expr (n + 1) body))
    last

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
        @@ spf "%s %s" (layout_func_label l) (layout_p_func (n + 1) f))
      state_body
  in
  let head = mk_indent_line n @@ spf "state %s %s {" name prefix in
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
      (fun x -> mk_indent_semicolon_line (n + 1) @@ spf "var %s: int" x.x)
      local_vars
  in
  let states_str = List.split_by "" (layout_p_state (n + 1)) states in
  let head = mk_indent_line n @@ spf "machine %s {" name in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s%s" head local_vars_str states_str local_funcs_str last

let layout_global_function n (name, f) =
  mk_indent_line n @@ spf "fun %s = %s" name.x (layout_p_func n f)

let layout_item = function
  | PMachine m -> layout_p_machine 0 m
  | PGlobalFunc (name, f) -> layout_global_function 0 (name, f)

let layout_p_program prog = List.split_by "" layout_item prog
