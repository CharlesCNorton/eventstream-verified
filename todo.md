# eventstream-verified — open work

1. Fix `.gitignore` to exclude `.vo`, `.vos`, `.vok`, `.glob`, `.aux`, `.lia.cache`, `*.cmo`, `*.cmi`, `*.exe`, `build/`, `*.txt` output files, and `nul`.
2. Remove committed build artifacts from the repo: binaries, bytecode, Coq compilation outputs, test output files, and the `nul` file.
3. Escape or restructure the Heraclitus quote in the header comment to eliminate the `comment-terminator-in-string` Coq warning.
4. Delete dead `lex_compare` section (lines 40–154) — defined outside the Section, never referenced in the main development.
5. Factor `event_compare_not_gt_trans` (90 lines) into a generic lexicographic transitivity combinator.
6. Extract a shared `filter_satisfies` lemma to deduplicate the 6 near-identical `nat_cancel_handler_*` proofs.
7. Change nat instantiation lemmas (lines 1986–2275) from `Qed` to `Defined`.
8. Replace pointwise invariant (`map_list_agree'`) with a direct simulation proof showing `apply_events stream [] = map_values (apply_events_map stream kmap_empty)` by induction on the stream.
9. Replace unary `nat` with `Z` throughout the formalization and switch extraction to `ExtrOcamlZInt`.
10. Fix `fix_engine.ml` line 159 to go through the `ES` functor instead of directly referencing `IntConfig.should_replace`.
11. Fix `kind_to_exec_type` asymmetry: `Original → "0"` but `"F"` (Trade/Fill) also parses to `Original`, breaking round-trip for fills. Give fills a distinct mapping.
12. Fix `fix_engine.ml`: FIX `MsgSeqNum` (tag 34) is conflated with logical amendment `ev_seq` — these are semantically different in real FIX. Map tag 34 to a separate field or use a domain-appropriate source for `ev_seq`.
13. Add an OCaml test comparing `canonicalize_map` output against list-based `canonicalize` to catch extraction/Map mismatches.
14. Add a seed parameter to random tests for reproducible failure investigation.
