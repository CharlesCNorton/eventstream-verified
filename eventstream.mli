
val negb : bool -> bool

type comparison =
| Eq
| Lt
| Gt

module Nat :
 sig
  val compare : int -> int -> comparison
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val lex_compare : int list -> int list -> comparison

val lex_leb : int list -> int list -> bool

type event_kind =
| Original
| Correction
| Cancel

type event = { ev_id : int; ev_timestamp : int; ev_seq : int;
               ev_payload : int; ev_kind : event_kind }

val event_kind_eqb : event_kind -> event_kind -> bool

val event_eqb : event -> event -> bool

val kind_index : event_kind -> int

val event_keys : event -> int list

val event_leb : event -> event -> bool

val insert : event -> event list -> event list

val sort_events : event list -> event list

val replace_or_add : event -> event list -> event list

val apply_events : event list -> event list -> event list

val canonicalize : event list -> event list

val ids_of : event list -> int list

val mem_nat : int -> int list -> bool

val dedup_nat : int list -> int list

val detect_gaps : event list -> int list
