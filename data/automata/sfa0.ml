val write : int -> unit
val read : int -> unit
val ( == ) : int -> int -> bool
val ( != ) : int -> int -> bool

let[@sregex] a1 ((valDom [@pi]) : int) ((y [@forall]) : valDom) =
  ctxOp [| read; write |]
    (starA (Write (x, x != y));
     anyA;
     starA (Read (x, x == y)))
