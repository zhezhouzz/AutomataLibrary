open Mtyped
open Constant
open Sexplib.Std
open Zzdatatype.Datatype

type 'a machine = {
  binding : (string * Normalty.Connective.qt * constant) list;
  reg : 'a;
}
