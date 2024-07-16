val "==" : 'a -> 'a -> bool;
val "!=" : 'a -> 'a -> bool;

type server <: int;
type key <: int;

event write : server * key * int;
event read : server * int;

spec prop = forall (n: int), forall (serv : server), forall (y:key),
 ctx [| read write |]
   ((<[ write s x | s == serv && x != y ]>*)~(rep n .)~(<[ write s x |s == serv && x == y ]>*));

const serverType =[|1; 2|];
const valueType = [|1; 2; 3|];

machine client =
   let server = serverType in
   let key = valueType in
   prop 3
