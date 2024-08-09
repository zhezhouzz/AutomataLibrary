open Sexplib.Std
open Mtyped
open Prop
open Sevent
open Regex
open Inst
open Constructor_declaration

type event_kind = Req | Resp | Hidden [@@deriving sexp]

type 't item =
  | MEnumDecl of (string * string list)
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decls : constructor_declaration list;
    }
  | MTyDeclSub of { type_name : string; super_ty : Nt.t }
  | MValDecl of ('t, string) typed
  | MEventDecl of { ev : ('t, string) typed; event_kind : event_kind }
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; prop : 't prop }
  | MRegex of { name : ('t, string) typed; automata : ('t, 't sevent) regex }
(* | MFAImp of { name : string; automata : ('t, string) re } *)
(* | MSFAImp of { name : string; automata : ('t, 't sevent) qregex } *)
[@@deriving sexp]

let default_serv_field = "dest" #: (Nt.Ty_constructor ("server", []))

let add_server_field_record_type = function
  | Nt.Ty_record l ->
      Nt.Ty_record ((default_serv_field.x, default_serv_field.ty) :: l)
  | _ -> Sugar._failatwith __FILE__ __LINE__ "die"

let remove_server_field_record_type = function
  | Nt.Ty_record l ->
      Nt.Ty_record
        (List.filter
           (fun (x, _) -> not (String.equal x default_serv_field.x))
           l)
  | _ -> Sugar._failatwith __FILE__ __LINE__ "die"

open Zzdatatype.Datatype

let mk_event_tyctx items =
  List.fold_right
    (function
      | MEventDecl { ev; _ } -> StrMap.add ev.x ev.ty | _ -> fun res -> res)
    items StrMap.empty

let mk_event_kindctx items =
  List.fold_right
    (function
      | MEventDecl { ev; event_kind; _ } -> StrMap.add ev.x event_kind
      | _ -> fun res -> res)
    items StrMap.empty

let layout_event_kind = function
  | Req -> "request"
  | Resp -> "response"
  | Hidden -> "hidden"
