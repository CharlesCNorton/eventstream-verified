# eventstream-verified

Formally verified deterministic event-stream canonicalization in Rocq (Coq), with extraction to OCaml.

Raw event streams — carrying duplicates, reordering, corrections, and cancellations — are reduced to a canonical truth stream that is **bit-for-bit reproducible** regardless of input ordering.

## The problem

Any system that ingests event streams from multiple sources faces a fundamental challenge: the same logical state can be described by many different physical streams.  Messages arrive out of order, get retransmitted, are amended after the fact, or cancelled entirely.  If your pipeline's output depends on the *order* events arrived rather than their *content*, your results are non-deterministic — and non-determinism in financial data is a regulatory and operational liability.

This library provides a canonicalizer with machine-checked proofs that the output depends only on the *set* of input events, never their arrival order.

## Proven properties

All proofs are constructive (`Defined`, not `Qed`) and extract to executable OCaml.

| Property | Theorem | Meaning |
|----------|---------|---------|
| **Determinism** | `canonicalize_deterministic` | Any permutation of the input produces identical output |
| **Idempotence** | `canonicalize_idempotent` | Re-ingesting canonical output is a no-op |
| **Sort correctness** | `sort_events_perm`, `sort_events_sorted` | Output is a sorted permutation of the processed stream |
| **No cancel leakage** | `apply_events_no_cancels` | Cancel events are consumed during processing, never emitted |
| **Unique ids** | `apply_events_NoDup` | Each event id appears at most once in output |
| **Semantic spec** | `canonicalize_spec` | An id survives iff its last event (in sort order) is not a Cancel |
| **Output subset** | `canonicalize_ids_subset` | Every output id was present in the input |
| **Online-batch equivalence** | `online_batch_equiv` | Incremental `fold_stream` equals batch `canonicalize` |
| **Chunked processing** | `chunked_processing` | Arbitrary contiguous partitions of a sorted stream compose correctly |

## Event model

```
Record event : Type := mkEvent {
  ev_id        : nat;    (* unique event identifier *)
  ev_timestamp : nat;    (* arrival or trade time *)
  ev_seq       : nat;    (* sequence number for amendments *)
  ev_payload   : nat;    (* domain-specific value *)
  ev_kind      : event_kind  (* Original | Correction | Cancel *)
}.
```

- **Original**: a new event.  Duplicates (same id, same or lower seq) are absorbed.
- **Correction**: replaces an existing event with the same id if the seq is higher.
- **Cancel**: removes all events with the matching id from the output.

Total order is lexicographic over `(timestamp, seq, id, payload, kind)`, making the sort fully deterministic.

## Worked examples

The formalization includes seven domain scenarios computed and proof-checked inside Coq:

1. **Equity trading — flash-crash replay.** Executions from three venues with amendments, a bust, and a duplicate retransmit.
2. **IoT sensor mesh — industrial cooling loop.** Temperature sensors with drift correction, decommissioning, and stale LoRa retransmits.
3. **Regulatory trade reporting — MiFID II amendment chain.** Five trades with double amendments, a cancellation, and duplicate feeds from a backup ARM.
4. **Distributed event sourcing — order lifecycle.** E-commerce order with coupon repricing, inventory release, backorder, and microservice retries.
5. **High-frequency market data — depth-of-book reconstruction.** Two-exchange consolidated feed with order amendments, pulls, and a crossed book.
6. **Clinical trial data — adverse event reconciliation.** Multi-site pharmaceutical trial with MedDRA recoding, retraction, and EDC retransmits.
7. **Satellite telemetry — LEO constellation housekeeping.** Store-and-forward delays, on-board recalibration, and satellite deorbit.

Each scenario verifies idempotence, determinism, or online-batch equivalence on its specific data.

## Building

Requires [Coq Platform](https://github.com/coq/platform) 8.19+.

```bash
# Compile the formalization (produces .vo and extracts eventstream.ml)
coqc eventstream.v

# Build and run the OCaml test suite
ocamlfind ocamlc -package stdlib-shims -linkpkg \
  eventstream.mli eventstream.ml main.ml -o test.exe
ocamlrun test.exe

# Run random stress tests (1000 trials, 8 properties each)
ocamlfind ocamlc -package stdlib-shims -linkpkg \
  eventstream.mli eventstream.ml test_random.ml -o test_random.exe
ocamlrun test_random.exe
```

## Design notes

- **Insertion sort** is used for proof clarity.  The sort interface (`Permutation` + `Sorted`) is shared with `Coq.Sorting.Mergesort`, so swapping in O(n log n) for production is a drop-in change.
- **Unary nat** is the extraction base type, mapped to OCaml `int` via `ExtrOcamlNatInt`.  A production deployment would parameterize over a richer event type with structured payloads.
- All proofs use `Defined` rather than `Qed`, making the proof terms transparent and available for further composition.

## License

Proprietary — All Rights Reserved.

## Author

Charles C. Norton
