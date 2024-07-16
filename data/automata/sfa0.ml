val write : int -> int -> unit
val read : int -> unit
val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool

let[@sregex] poly_spec ((n [@forall]) : int) ((server [@pi]) : int)
    ((valDom [@pi]) : int) ((server [@forall]) : server)
    ((y [@forall]) : valDom) =
  ctxOp [| read; write |]
    (starA (Write (s, x, s == server && x != y));
     repeat n anyA;
     starA (Write (s, x, s == server && x == y)))

let[@typedef] serverType = [| 1; 2 |]
let[@typedef] valueType = [| 1; 2; 3 |]
let[@inst] client = poly_spec 3 serverType valueType
