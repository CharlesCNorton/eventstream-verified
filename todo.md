# eventstream-verified — open work

- [ ] #1 Prove map-batch equivalence: sort_events (map_values (apply_events_map stream empty)) = canonicalize stream. Route canonicalize through map path or export both with equivalence proof as bridge.
- [ ] #2 Update extraction to emit Mergesort/map-backed canonicalize (blocked by #1).
- [ ] #3 Prove in Coq that OCaml List.sort under extracted comparison equals extracted sort_events, or revert to using extracted sort.
- [ ] #4 Replace ExtrOcamlNatInt with Zarith extraction, or add input validation rejecting values exceeding 62 bits.
- [ ] #5 Check in generated eventstream.mli or make the build produce it automatically.
- [ ] #6 Add Makefile or dune build that chains coqc extraction into OCaml compile.
- [ ] #7 Add test: parse_fix_event (event_to_fix e) = Some e round-trip.
- [ ] #8 Add test: ingest N random FIX messages through streaming engine, flush, assert equality with batch ES.canonicalize.
- [ ] #9 Expand random test parameters and add at least one non-int functor instantiation test.
