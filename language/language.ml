include Front
module Nt = Normalty.Ntyped
(* module Nt = struct *)
(*   include Normalty.Frontend *)
(*   include Normalty.Ntyped *)
(* end *)

module StringC = struct
  include String

  let layout x = x
end

module StringMap = Map.Make (StringC)
module StrAutomata = MakeAutomata (StringC) (StringMap)
