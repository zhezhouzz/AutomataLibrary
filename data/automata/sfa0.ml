val c : int -> unit
val ( == ) : int -> int -> bool
val ( != ) : int -> int -> bool

let[@sregex] a1 ((y [@forall]) : int) =
  starA (C (x, x != y));
  C (x, x == y);
  starA (C (x, x != y))
