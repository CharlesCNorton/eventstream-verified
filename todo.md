# eventstream-verified — open work

1. Replace pointwise invariant (`map_list_agree'`) with a direct simulation proof showing `apply_events stream [] = map_values (apply_events_map stream kmap_empty)` by induction on the stream.
2. Replace unary `nat` with `Z` throughout the formalization and switch extraction to `ExtrOcamlZInt`.
