open Sexplib.Std
open Mtyped
open Prop
open Sugar
open Common

type 't sevent =
  | GuardEvent of 't prop
  | EffEvent of { op : string; vs : ('t, string) typed list; phi : 't prop }
[@@deriving sexp]

let vs_names_from_types tps =
  let n = List.length tps in
  let vs = vs_names n in
  List.map (fun (x, ty) -> x #: ty) @@ _safe_combine __FILE__ __LINE__ vs tps
