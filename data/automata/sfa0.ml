val write : int -> int -> unit
val read : int -> int -> unit
val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool

let[@sregex] poly_spec ((server [@pi]) : int) ((valDom [@pi]) : int)
    ((server [@forall]) : server) ((y [@forall]) : valDom) =
  ctxOp [| read; write |]
    (starA (Write (s, x, s == server && x != y));
     repeat 2 anyA;
     starA (Read (s, x, s == server && x == y)))

let[@const] server = [| 1; 2 |]
let[@const] values = [| 1; 2; 3 |]
let[@inst] client = poly_spec server values
