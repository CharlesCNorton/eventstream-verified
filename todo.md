# eventstream-verified — open work

1. Factor `event_compare_not_gt_trans` (90 lines) into a generic lexicographic transitivity combinator.
2. Extract a shared `filter_satisfies` lemma to deduplicate the 6 near-identical `nat_cancel_handler_*` proofs.
3. Change nat instantiation lemmas from `Qed` to `Defined`.
4. Replace pointwise invariant (`map_list_agree'`) with a direct simulation proof showing `apply_events stream [] = map_values (apply_events_map stream kmap_empty)` by induction on the stream.
5. Replace unary `nat` with `Z` throughout the formalization and switch extraction to `ExtrOcamlZInt`.
6. Fix `fix_engine.ml` line 159 to go through the `ES` functor instead of directly referencing `IntConfig.should_replace`.
7. Fix `kind_to_exec_type` asymmetry: `Original → "0"` but `"F"` (Trade/Fill) also parses to `Original`, breaking round-trip for fills. Give fills a distinct mapping.
8. Fix `fix_engine.ml`: FIX `MsgSeqNum` (tag 34) is conflated with logical amendment `ev_seq` — these are semantically different in real FIX. Map tag 34 to a separate field or use a domain-appropriate source for `ev_seq`.
9. Add an OCaml test comparing `canonicalize_map` output against list-based `canonicalize` to catch extraction/Map mismatches.
10. Add a seed parameter to random tests for reproducible failure investigation.
