val "==" : 'a -> 'a -> bool;
val "!=" : 'a -> 'a -> bool;

type server <: int;
type key <: int;

event write : <k : key; value: int>;
event read : <k : key >;

machine w1 (s: server) (y: key) =
   <[function
     | write -> k == y
     | all -> dest == s]>;

machine w2 (s: server) (y: key) =
   <[function
     | write -> k != y
     | all -> dest == s]>;

machine prop (n: int) =
   forall (serv : server), forall (y: key),
ctx [| read write |]
((w1 serv y) ~ (rep n .) ~ (w2 serv y)*);

const serverType = [|1; 2|];
const valueType = [|1; 2; 3|];

machine client =
   let server = serverType in
   let key = valueType in
   prop 3
