(** Verified event-stream canonicalization — extracted from Rocq.

    This is a hand-written interface exposing only the public API.
    The full extracted .mli is ~3000 lines of FMapAVL internals;
    this file hides them.  Regenerate the .ml with [coqc eventstream.v]. *)

(** {1 Basic types} *)

val negb : bool -> bool

type comparison = Eq | Lt | Gt

module Nat : sig
  val compare : int -> int -> comparison
end

(** {1 Event types} *)

type event_kind = Original | Correction | Cancel

type ('key, 'payload) event = {
  ev_id        : 'key;
  ev_timestamp : 'key;
  ev_seq       : 'key;
  ev_payload   : 'payload;
  ev_kind      : event_kind;
}

(** {1 Comparison} *)

val event_kind_eqb : event_kind -> event_kind -> bool

val event_compare :
  ('a -> 'a -> comparison) ->
  ('b -> 'b -> comparison) ->
  ('a, 'b) event -> ('a, 'b) event -> comparison

val event_leb :
  ('a -> 'a -> comparison) ->
  ('b -> 'b -> comparison) ->
  ('a, 'b) event -> ('a, 'b) event -> bool

val event_eqb :
  ('a -> 'a -> bool) ->
  ('b -> 'b -> bool) ->
  ('a, 'b) event -> ('a, 'b) event -> bool

(** {1 Sorting} *)

val sort_events :
  ('a -> 'a -> comparison) ->
  ('b -> 'b -> comparison) ->
  ('a, 'b) event list -> ('a, 'b) event list

(** {1 Event processing — list-based (specification)} *)

val replace_or_add :
  ('a -> 'a -> bool) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  ('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list

val apply_events :
  ('a -> 'a -> bool) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  (('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list) ->
  ('a, 'b) event list -> ('a, 'b) event list -> ('a, 'b) event list

val process_one :
  ('a -> 'a -> bool) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  (('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list) ->
  ('a, 'b) event list -> ('a, 'b) event -> ('a, 'b) event list

(** {1 Event processing — map-based (O(n log n) accumulator)} *)

val replace_or_add_map :
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  ('a -> 'c -> ('a, 'b) event option) ->
  ('a -> ('a, 'b) event -> 'c -> 'c) ->
  ('a, 'b) event -> 'c -> 'c

val apply_events_map :
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  ('a -> 'c -> ('a, 'b) event option) ->
  ('a -> ('a, 'b) event -> 'c -> 'c) ->
  ('a -> 'c -> 'c) ->
  ('a, 'b) event list -> 'c -> 'c

val map_values :
  ('c -> ('a * ('a, 'b) event) list) ->
  'c -> ('a, 'b) event list

(** {1 Canonicalization} *)

val canonicalize :
  ('a -> 'a -> comparison) ->
  ('a -> 'a -> bool) ->
  ('b -> 'b -> comparison) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  (('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list) ->
  ('a, 'b) event list -> ('a, 'b) event list

val canonicalize_map :
  ('a -> 'a -> comparison) ->
  ('b -> 'b -> comparison) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  ('a -> 'c -> ('a, 'b) event option) ->
  ('a -> ('a, 'b) event -> 'c -> 'c) ->
  ('a -> 'c -> 'c) ->
  ('c -> ('a * ('a, 'b) event) list) ->
  'c ->
  ('a, 'b) event list -> ('a, 'b) event list

val fold_stream :
  ('a -> 'a -> comparison) ->
  ('a -> 'a -> bool) ->
  ('b -> 'b -> comparison) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  (('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list) ->
  ('a, 'b) event list -> ('a, 'b) event list

(** {1 Utilities} *)

val ids_of : ('a, 'b) event list -> 'a list

val mem_key : ('a -> 'a -> bool) -> 'a -> 'a list -> bool

val dedup_key : ('a -> 'a -> bool) -> 'a list -> 'a list

val detect_gaps :
  ('a -> 'a -> comparison) ->
  ('a -> 'a -> bool) ->
  ('b -> 'b -> comparison) ->
  (('a, 'b) event -> ('a, 'b) event -> bool) ->
  (('a, 'b) event -> ('a, 'b) event list -> ('a, 'b) event list) ->
  ('a, 'b) event list -> 'a list
