# eventstream-verified — open work

- [x] #1 Update extraction to emit map-backed canonicalize.
- [ ] #2 Prove in Coq that OCaml List.sort under extracted comparison equals extracted sort_events, or revert to using extracted sort.
- [ ] #3 Replace ExtrOcamlNatInt with Zarith extraction, or add input validation rejecting values exceeding 62 bits.
