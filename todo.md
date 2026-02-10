# eventstream-verified — open work

- [x] #1 Replace insertion sort with bottom-up mergesort (O(n log n)). Defined merge/stack as direct fixpoints inside Section; reproved sort_events_perm and sort_events_sorted via merge_perm, merge_sorted, and stack invariants.
- [ ] #2 Prove map-batch equivalence: sort_events (map_values (apply_events_map stream empty)) = canonicalize stream. Route canonicalize through map path or export both with equivalence proof as bridge.
- [ ] #7 Update extraction to emit Mergesort/map-backed canonicalize (blocked by #1, #2)
