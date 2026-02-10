# eventstream-verified — open work

- [ ] #1 Use Coq.Sorting.Mergesort for sort_events (define TotalLeBool instance outside Section, replace sort_events body, reconnect sort_events_perm and sort_events_sorted through Mergesort interface)
- [ ] #2 Prove map-batch equivalence: sort_events (map_values (apply_events_map stream empty)) = canonicalize stream. Route canonicalize through map path or export both with equivalence proof as bridge.
- [ ] #7 Update extraction to emit Mergesort/map-backed canonicalize (blocked by #1, #2)
