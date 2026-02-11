# eventstream-verified — open work

- [ ] #1 Prove map-batch equivalence: sort_events (map_values (apply_events_map stream empty)) = canonicalize stream. Route canonicalize through map path or export both with equivalence proof as bridge.
- [ ] #2 Update extraction to emit Mergesort/map-backed canonicalize (blocked by #1).
- [ ] #3 Prove in Coq that OCaml List.sort under extracted comparison equals extracted sort_events, or revert to using extracted sort.
- [ ] #4 Replace ExtrOcamlNatInt with Zarith extraction, or add input validation rejecting values exceeding 62 bits.
