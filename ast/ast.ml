include Common
include Op
include Constant
include Lit
include Prop
include Sevent
include Regex
include Nfa
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
  let delimit_cotexnt_char (_, c) = [ c ]
end

module Int64C = struct
  include Int64

  let layout = to_string
  let delimit_cotexnt_char (_, c) = [ c ]
end

module DesymLabel = struct
  type t = string * int

  let compare (a : t) (b : t) = Stdlib.compare a b
  let layout (op, id) = op ^ ":" ^ string_of_int id
  let delimit_cotexnt_char (_, c) = [ c ]
  let eq (s1, i1) (s2, i2) = String.equal s1 s2 && Int.equal i1 i2
end
