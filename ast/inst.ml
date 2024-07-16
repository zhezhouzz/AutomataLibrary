open Mtyped
open Constant
open Sexplib.Std

type 't inst =
  | IVar of ('t, string) typed
  | IConst of constant
  | IQregex of ('t, 't Sevent.sevent) Qregex.qregex
  | IApp of ('t inst * 't inst)
[@@deriving sexp]

open Zzdatatype.Datatype

type ('t, 'a) machine = {
  binding : (string * Normalty.Connective.qt * constant) list;
  reg : 'a;
}
