open Mtyped
open Constant
open Sexplib.Std
open Zzdatatype.Datatype

type world =
  | WState (* always int *)
  | WSingle of {
      (* e.g., exists (a: account <: int) *)
      qv : (Nt.t, string) typed;
      abstract_type : Nt.t;
      world : world;
    }
  | WMap of {
      (* e.g., forall (a: account <: int) *)
      qv : (Nt.t, string) typed;
      abstract_type : Nt.t;
      world : world;
    }

type 'a regspec = { world : world; reg : 'a }

type 'a machine = {
  binding : (string * Normalty.Connective.qt * constant) list;
  reg : 'a;
}
