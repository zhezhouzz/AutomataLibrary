  val "==" : 'a -> 'a -> bool;
  val "!=" : 'a -> 'a -> bool;
  val ">" : 'a -> 'a -> bool;
  val ">=" : 'a -> 'a -> bool;
  val "<" : 'a -> 'a -> bool;
  val "<=" : 'a -> 'a -> bool;
  val "-" : 'a -> 'a -> 'a;
  val "+" : 'a -> 'a -> 'a;

  type server <: int;
  type account <: int;
  type amount <: int;
  type id <: int;

  request event eWithDrawReq: <accountId: account; amount: amount; rId: id>;
  response event eWithDrawResp: <status: bool; accountId: account; balance: amount; rId: id>;

  machine req_has_id (i: id) =
  <[function
  | eWithDrawReq -> rId == i
  ]>;

  machine no_event_has_id (i: id) =
  <[function
  | eWithDrawReq -> rId != i
  | eWithDrawResp -> rId != i
  ]>;

  machine resp_has_id (i: id) =
  <[function
  | eWithDrawResp -> rId == i
  ]>;

  machine req_has_greater_id (i: id) =
  <[function
  | eWithDrawReq -> rId > i
  | eWithDrawResp -> true
  ]>;

  machine req_has_less_id (i: id) =
  <[function
  | eWithDrawReq -> rId < i
  ]>;

  machine resp_balance (a: account) (am: amount) =
  <[function
  | eWithDrawResp -> accountId == a && status && balance == am
  ]>;

  machine resp_any_balance (a: account) =
  <[function
  | eWithDrawResp -> accountId == a && status
  ]>;

  machine req_bad_amount (a: account) (am: amount) =
  <[function
  | eWithDrawReq -> accountId == a && amount > am - (10: amount)
  ]>;

  machine req_any_amount (a: account) =
  <[function
  | eWithDrawReq -> accountId == a
  ]>;

  machine increasing_id (i: id) =
  (not (.* ~ (req_has_id i) ~ .* ~ (req_has_less_id i) ~ .*)) ;

  machine unique_id (i: id) =
  (not (.* ~ (req_has_id i) ~ .* ~ (req_has_id i) ~ .*)) ;

  machine liveness_id (i: id) =
  (no_event_has_id i)* ~ (req_has_id i) ~ (no_event_has_id i)* ~ (resp_has_id i) ~ (no_event_has_id i)*;

  machine balance_safety (a: account) (am: amount) =
  (not (.* ~ (resp_balance a am) ~ .* ~ (req_bad_amount a am) ~ .*)) ;

  machine balance_safety_violation (a: account) (am: amount) =
  (.* ~ (resp_balance a am) ~ .* ~ (req_bad_amount a am)) ;

  machine prop =
  exists (s: server), exists (a1: account), exists (am1: amount), forall (i: id), forall (a: account), forall (am: amount),
  ctx [| eWithDrawReq eWithDrawResp |]
  (unique_id i) && (liveness_id i) && (balance_safety_violation a1 am1)
