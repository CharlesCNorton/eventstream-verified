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
| **External sort equivalence** | `external_sort_eq` | Any function producing a sorted permutation equals `sort_events` |
| **Map-list equivalence** | `apply_events_map_equiv` | O(n log n) map-backed accumulator equals O(n^2) list-based spec |
| **No cancel leakage** | `apply_events_no_cancels` | Cancel events are consumed during processing, never emitted |
| **Unique ids** | `apply_events_NoDup` | Each event id appears at most once in output |
| **Semantic spec** | `canonicalize_spec` | An id survives iff its last event (in sort order) is not a Cancel |
| **Output subset** | `canonicalize_ids_subset` | Every output id was present in the input |
| **Online-batch equivalence** | `online_batch_equiv` | Incremental `fold_stream` equals batch `canonicalize` |
| **Chunked processing** | `chunked_processing` | Arbitrary contiguous partitions of a sorted stream compose correctly |

## Event model

The Coq formalization is parameterized over `Key`, `Payload`, comparison functions, conflict resolution (`should_replace`), and cancel semantics (`cancel_handler`).  The nat instantiation used for proof-checked examples:

```
Record event : Type := mkEvent {
  ev_id        : Key;       (* unique event identifier *)
  ev_timestamp : Key;       (* arrival or trade time *)
  ev_seq       : Key;       (* sequence number for amendments *)
  ev_payload   : Payload;   (* domain-specific value *)
  ev_kind      : event_kind (* Original | Correction | Cancel *)
}.
```

- **Original**: a new event.  Duplicates (same id, same or lower seq) are absorbed.
- **Correction**: replaces an existing event with the same id if the seq is higher.
- **Cancel**: removes all events with the matching id from the output.

Total order is lexicographic over `(timestamp, seq, id, payload, kind)`, making the sort fully deterministic.

## OCaml functor

The extracted code is wrapped in a parameterized functor (`eventstream_functor.ml`).  Instantiate with concrete `KEY`, `PAYLOAD`, and `CONFIG` modules:

```ocaml
module ES = Eventstream_functor.Make(IntKey)(IntPayload)(IntConfig)

let canonical = ES.canonicalize raw_events
let gaps = ES.detect_gaps raw_events
```

`CONFIG.validate` is called on every event entering `canonicalize`, `fold_stream`, and `process_one`.  The int instantiation rejects negative values (Coq nat is non-negative; `ExtrOcamlNatInt` maps nat to OCaml `int`).

## FIX protocol engine

`fix_engine.ml` is an unverified adapter mapping FIX 4.4 ExecutionReport messages to the verified event type.  It includes:

- FIX field parsing and serialization (pipe-delimited wire format)
- Per-symbol streaming engine with O(1) Hashtbl accumulator and authoritative batch flush
- Synthetic market data generator (100 symbols, 6 venues, realistic event distribution)
- Demo mode (`--demo`) and throughput benchmark (`--bench [N]`)

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

Requires [Coq Platform](https://github.com/coq/platform) 8.19+ and OCaml 4.14+.

```bash
# Compile the formalization (produces .vo and extracts eventstream.ml)
coqc eventstream.v

# Restore the hand-written .mli (coqc overwrites it)
git checkout eventstream.mli

# Build and run everything via Makefile
make all
```

Or manually:

```bash
# Unit tests (16 tests)
ocamlc eventstream.mli eventstream.ml eventstream_functor.ml \
  int_instance.ml main.ml -o test.exe
ocamlrun test.exe

# Random stress tests (1000 trials, 8 properties each, int + string keys)
ocamlc eventstream.mli eventstream.ml eventstream_functor.ml \
  int_instance.ml test_random.ml -o test_random.exe
ocamlrun test_random.exe

# FIX round-trip + streaming tests
ocamlc eventstream.mli eventstream.ml eventstream_functor.ml \
  int_instance.ml fix_engine.ml test_fix.ml -o test_fix.exe
ocamlrun test_fix.exe

# FIX engine demo / benchmark
ocamlc eventstream.mli eventstream.ml eventstream_functor.ml \
  int_instance.ml fix_engine.ml fix_engine_main.ml -o fix_engine.exe
ocamlrun fix_engine.exe --demo
ocamlrun fix_engine.exe --bench 5000000
```

## Design notes

- **Bottom-up mergesort** is defined directly as fixpoints inside the parameterized Section.  `external_sort_eq` proves that any function producing a sorted permutation equals `sort_events`, justifying the use of OCaml's `List.sort` in the functor.
- **Map-backed accumulator** (`apply_events_map`) uses an abstract map interface proven equivalent to the list-based spec via `map_list_agree'`.  The functor supplies OCaml's stdlib `Map` for O(n log n) canonicalization.
- **Unary nat** is the extraction base type, mapped to OCaml `int` via `ExtrOcamlNatInt`.  Input validation rejects negative values at the system boundary.
- All proofs use `Defined` rather than `Qed`, making the proof terms transparent and available for further composition.

## License

Proprietary — All Rights Reserved.

## Author

Charles C. Norton
