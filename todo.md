# eventstream-verified — open work

- [ ] #1 Prove map-batch equivalence: sort_events (map_values (apply_events_map stream empty)) = canonicalize stream. Route canonicalize through map path or export both with equivalence proof as bridge.
- [ ] #2 Update extraction to emit Mergesort/map-backed canonicalize (blocked by #1).
- [ ] #3 Extract IntKey, IntPayload, IntConfig into a shared module; delete the three copies.
- [ ] #4 Add Makefile or dune build that chains coqc extraction into OCaml compile.
- [ ] #5 Check in generated eventstream.mli or make the build produce it automatically.
- [ ] #6 Add test: ingest N random FIX messages through streaming engine, flush, assert equality with batch ES.canonicalize.
- [ ] #7 Add test: parse_fix_event (event_to_fix e) = Some e round-trip.
- [ ] #8 Prove in Coq that OCaml List.sort under extracted comparison equals extracted sort_events, or revert to using extracted sort.
- [ ] #9 Replace ExtrOcamlNatInt with Zarith extraction, or add input validation rejecting values exceeding 62 bits.
- [ ] #10 Change nat_should_replace from Nat.leb to Nat.ltb so same-seq retransmits are absorbed.
- [ ] #11 Document that Cancel is positional in sorted-stream order, not a permanent ID blacklist.
- [ ] #12 Expand random test parameters and add at least one non-int functor instantiation test.
