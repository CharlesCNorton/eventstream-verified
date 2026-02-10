(******************************************************************************)
(*                                                                          *)
(*   OCaml Functor Interface over Verified Event-Stream Canonicalization    *)
(*                                                                          *)
(*   Wraps the Rocq-extracted parameterized functions (eventstream.ml)      *)
(*   into a clean functor.  All canonicalization logic inside the functor   *)
(*   is machine-checked; this file is pure plumbing.                        *)
(*                                                                          *)
(******************************************************************************)

open Eventstream

(** Key type: used for ev_id, ev_timestamp, ev_seq. *)
module type KEY = sig
  type t
  val compare : t -> t -> Eventstream.comparison
  val eqb     : t -> t -> bool
end

(** Payload type: carried data inside each event. *)
module type PAYLOAD = sig
  type t
  val compare : t -> t -> Eventstream.comparison
  val eqb     : t -> t -> bool
end

(** Conflict resolution and cancel semantics. *)
module type CONFIG = sig
  type key
  type payload
  type ev = (key, payload) Eventstream.event

  (** [should_replace old_ev new_ev] returns true if new_ev wins. *)
  val should_replace : ev -> ev -> bool

  (** [cancel_handler cancel_ev acc] removes the cancelled event. *)
  val cancel_handler : ev -> ev list -> ev list
end

(** The functor.  Instantiate with concrete Key, Payload, and Config
    to get a module whose every function is backed by extracted,
    machine-checked Rocq code. *)
module Make
    (K : KEY)
    (P : PAYLOAD)
    (C : CONFIG with type key = K.t and type payload = P.t)
: sig
  type key     = K.t
  type payload = P.t
  type ev      = (key, payload) Eventstream.event

  val canonicalize  : ev list -> ev list
  val fold_stream   : ev list -> ev list
  val sort_events   : ev list -> ev list
  val apply_events  : ev list -> ev list -> ev list
  val process_one   : ev list -> ev -> ev list
  val event_leb     : ev -> ev -> bool
  val event_eqb     : ev -> ev -> bool
  val detect_gaps   : ev list -> key list
  val ids_of        : ev list -> key list
end = struct
  type key     = K.t
  type payload = P.t
  type ev      = (key, payload) Eventstream.event

  let canonicalize stream =
    Eventstream.canonicalize K.compare K.eqb P.compare
      C.should_replace C.cancel_handler stream

  let fold_stream stream =
    Eventstream.fold_stream K.compare K.eqb P.compare
      C.should_replace C.cancel_handler stream

  let sort_events stream =
    Eventstream.sort_events K.compare P.compare stream

  let apply_events sorted acc =
    Eventstream.apply_events K.eqb C.should_replace C.cancel_handler
      sorted acc

  let process_one acc e =
    Eventstream.process_one K.eqb C.should_replace C.cancel_handler
      acc e

  let event_leb e1 e2 =
    Eventstream.event_leb K.compare P.compare e1 e2

  let event_eqb e1 e2 =
    Eventstream.event_eqb K.eqb P.eqb e1 e2

  let detect_gaps stream =
    Eventstream.detect_gaps K.compare K.eqb P.compare
      C.should_replace C.cancel_handler stream

  let ids_of = Eventstream.ids_of
end
