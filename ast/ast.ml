include Common
include Op
include Constant
include Lit
include Prop
include Sevent
include Regex
include Nfa
include Qregex
include Typectx
include Minterm
include Constructor_declaration
include Item
include Inst
include Mtyped
include Sugar

let ty_set (t : Nt.t) = Nt.Ty_constructor ("set", [ t ])

module StringC = struct
  include String

  let layout x = x
end

module Int64C = struct
  include Int64

  let layout = to_string
end

module DesymLabel = struct
  type t = string * int

  let compare (a : t) (b : t) = Stdlib.compare a b
  let layout (op, id) = op ^ ":" ^ string_of_int id
end
