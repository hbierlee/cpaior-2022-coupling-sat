predicate array_bool_imp(array[int] of var bool: as, array[int] of var bool: bs) =
  forall(i in index_set(as) intersect index_set(bs))(as[i] -> bs[i]);

% predicate array_bool_eq_reif(array[int] of var bool: as, array[int] of var bool: bs, var bool: r) =
%   forall(i in index_set(as) union index_set(bs))(
%   let { var bool: a = as[i]::maybe_partial; var bool: b = bs[i]::maybe_partial; } in
%     ((r /\ a) -> b) /\
%     ((r /\ b) -> a) /\
%     ((not r /\ a) -> not b) % (= not r /\ b -> not a)
%   );

% predicate array_bool_ne(array[int] of var bool: as, array[int] of var bool: bs) =
%   % forall(i in index_set(as) diff index_set(bs))(as[i]) /\
%   % forall(i in index_set(bs) diff index_set(as))(bs[i]) /\
%   forall(i in index_set(as) intersect index_set(bs))(as[i] != bs[i]);
