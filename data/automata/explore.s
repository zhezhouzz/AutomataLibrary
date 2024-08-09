  def "==" : 'a -> 'a -> bool   ;
  type server <: machine                                 ;
  type shard <: int             ;
  type router <: int            ;
  type tKey <: int              ;
  type tVal <: int              ;
  type tTime <: int             ;

  request event eReadReq: < key: tKey>;
  response event eReadRsp: < key: tKey, val: tVal, status: bool>;

  request event eUpdateReq: < key: tKey, val: tVal>;
  response event eUpdateRsp: < key: tKey, val: tVal>;

  machine ax_eReadReq (k: tKey) =
  not ((. - <[eReadReq| key == k]>)* ~ <[eReadRsp| key == k]> ~.*) ;

  machine ax_eUpdate  (k: tKey) (v: tVal) =
  not ((. - <[eUpdateReq|  key == k && val == v]>)* ~ <[eUpdateRsp|  key == k && val == v]> ~.*) ;

  machine ax_provenance_val  (k: tKey) (v: tVal) =
  not ((. - <[eUpdateReq| key == k && val == v]>)* ~ <[eReadRsp|  key == k && val == v]> ~.*) ;

  machine has_update  (k: tKey) = .* ~ <[eUpdateRsp|  key == k]> ~ .* ;
  machine last_update  (k: tKey) (v: tVal) =
  .* ~ <[eUpdateRsp| key == k && val == v]> ~ (. - <[eUpdateRsp| key == k ]>)*;

  machine read_active_violation (k: tKey) (v: tVal) =
  (last_update k v) ~ <[eReadRsp| key == k && not (val == v)]> ~ .* ;

  machine prop_tmp =
      exists (s: server),
    exists (k1: tKey), exists (v1: tVal),
    ctx [| eReadRsp eReadReq eUpdateRsp eUpdateReq |]
  (ax_eReadReq k1) && (ax_eUpdate k1 v1) &&
  (ax_provenance_val k1 v1) &&
  (read_active_violation k1 v1) ;

  machine prop =
    exists (s: server),
    exists (k1: tKey), exists (v1: tVal),
    forall (k: tKey), forall (v: tVal),
    ctx [| eReadRsp eReadReq eUpdateRsp eUpdateReq |]
  (ax_eReadReq k) && (ax_eUpdate k v) && (ax_provenance_val k v) &&
  (read_active_violation k1 v1)
