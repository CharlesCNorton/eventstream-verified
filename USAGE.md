# Usage

## Functor instantiation

Supply three modules to `Eventstream_functor.Make`:

```ocaml
module MyKey : Eventstream_functor.KEY = struct
  type t = int
  let compare a b = Eventstream.Nat.compare a b
  let ord_compare (a : int) (b : int) = Stdlib.compare a b
  let eqb a b = (a = b)
end

module MyPayload : Eventstream_functor.PAYLOAD = struct
  type t = int
  let compare a b = Eventstream.Nat.compare a b
  let eqb a b = (a = b)
end

module MyConfig : Eventstream_functor.CONFIG
  with type key = int and type payload = int = struct
  type key = int
  type payload = int
  type ev = (key, payload) Eventstream.event
  let should_replace old new_ = old.ev_seq < new_.ev_seq
  let cancel_handler e acc =
    List.filter (fun x -> not (x.ev_id = e.ev_id)) acc
  let validate (e : ev) =
    if e.ev_id < 0 then invalid_arg "negative id"
    (* validate other fields as needed *)
end

module ES = Eventstream_functor.Make(MyKey)(MyPayload)(MyConfig)
```

`KEY.compare` must return `Eventstream.comparison` (the Coq-extracted type). `KEY.ord_compare` must return a stdlib `int` for `Map.Make`.

## Public API

| Function | Complexity | Description |
|----------|-----------|-------------|
| `canonicalize` | O(n log n) | Sort-apply-sort via map-backed accumulator. The primary entry point. |
| `fold_stream` | O(n log n) | Sort input, fold with `process_one`, sort output. Proven equal to `canonicalize`. |
| `sort_events` | O(n log n) | Stable mergesort via `List.sort`. Proven equivalent to extracted sort by `external_sort_eq`. |
| `process_one` | O(log n) | Ingest one event into an accumulator. Calls `validate` on the event. |
| `event_leb` | O(1) | Total order: timestamp, seq, id, payload, kind. |
| `event_eqb` | O(1) | Structural equality on all five fields. |
| `detect_gaps` | O(n log n) | Returns input ids absent from canonical output (cancelled/superseded). |
| `ids_of` | O(n) | Extract event ids from a list. |

## Trust boundary

**Verified** (machine-checked in Coq, extracted to OCaml):
- `canonicalize`, `fold_stream`, `sort_events`, `process_one`
- `apply_events`, `apply_events_map`, `replace_or_add`, `replace_or_add_map`
- `event_compare`, `event_leb`, `event_eqb`
- `detect_gaps`, `ids_of`, `mem_key`, `dedup_key`
- All sorting, merging, and accumulation logic

**Verified by theorem, replaced at extraction**:
- `List.sort` replaces the extracted mergesort — justified by `external_sort_eq`
- `Map.Make` replaces the extracted AVL map — justified by `map_list_agree'` / `apply_events_map_equiv`

**Unverified** (hand-written OCaml):
- `eventstream_functor.ml` — functor plumbing, `validate` dispatch, `List.sort` bridge
- `int_instance.ml` — concrete `IntKey`, `IntPayload`, `IntConfig`
- `fix_engine.ml` — FIX 4.4 parser/serializer, streaming engine, synthetic data generator
- `eventstream.mli` — hand-written interface hiding extraction internals

**Invariant**: the `CONFIG.validate` function is called on every event entering `canonicalize`, `fold_stream`, and `process_one`. It is the caller's responsibility to reject values that would be invalid under `ExtrOcamlNatInt` (e.g., negative integers mapping to Coq `nat`).
