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
  val compare     : t -> t -> Eventstream.comparison
  val ord_compare : t -> t -> int   (** Stdlib ordering for Map.Make *)
  val eqb        : t -> t -> bool
end

(** Payload type: carried data inside each event. *)
module type PAYLOAD = sig
  type t
  val compare : t -> t -> Eventstream.comparison
  val eqb     : t -> t -> bool
end

(** Conflict resolution, cancel semantics, and input validation. *)
module type CONFIG = sig
  type key
  type payload
  type ev = (key, payload) Eventstream.event

  (** [should_replace old_ev new_ev] returns true if new_ev wins. *)
  val should_replace : ev -> ev -> bool

  (** [cancel_handler cancel_ev acc] removes the cancelled event. *)
  val cancel_handler : ev -> ev list -> ev list

  (** [validate ev] raises [Invalid_argument] if any field is out of
      range for the concrete key/payload representation.  Called on
      every event entering [canonicalize], [fold_stream], and
      [process_one].  ExtrOcamlNatInt maps Coq nat to OCaml int;
      this hook rejects values that would silently overflow. *)
  val validate : ev -> unit
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
  val process_one   : ev list -> ev -> ev list
  val event_leb     : ev -> ev -> bool
  val event_eqb     : ev -> ev -> bool
  val detect_gaps   : ev list -> key list
  val ids_of        : ev list -> key list
end = struct
  type key     = K.t
  type payload = P.t
  type ev      = (key, payload) Eventstream.event

  module KM = Map.Make(struct
    type t = K.t
    let compare = K.ord_compare
  end)

  (* O(n log n) sort via OCaml's List.sort (stable mergesort).
     Equals the extracted sort_events by external_sort_eq: any
     function producing a sorted permutation is unique. *)
  let event_cmp (e1 : ev) (e2 : ev) : int =
    match Eventstream.event_compare K.compare P.compare e1 e2 with
    | Eq -> 0 | Lt -> -1 | Gt -> 1

  let sort_events stream = List.sort event_cmp stream

  let apply_events sorted acc =
    Eventstream.apply_events K.eqb C.should_replace C.cancel_handler
      sorted acc

  let validate_all stream = List.iter C.validate stream

  (* Map-backed canonicalize: O(n log n) accumulator via stdlib Map.
     Uses the extracted apply_events_map, which is proven equivalent
     to the list-based apply_events via map_list_agree'. *)
  let canonicalize stream =
    validate_all stream;
    let sorted = sort_events stream in
    let m = Eventstream.apply_events_map
      C.should_replace KM.find_opt KM.add KM.remove sorted KM.empty in
    sort_events (List.map snd (KM.bindings m))

  let fold_stream stream =
    validate_all stream;
    sort_events
      (List.fold_left
        (Eventstream.process_one K.eqb C.should_replace C.cancel_handler)
        [] (sort_events stream))

  let process_one acc e =
    C.validate e;
    Eventstream.process_one K.eqb C.should_replace C.cancel_handler
      acc e

  let event_leb e1 e2 =
    Eventstream.event_leb K.compare P.compare e1 e2

  let event_eqb e1 e2 =
    Eventstream.event_eqb K.eqb P.eqb e1 e2

  let detect_gaps stream =
    let input_ids = Eventstream.dedup_key K.eqb (Eventstream.ids_of stream) in
    let output_ids = Eventstream.ids_of (canonicalize stream) in
    List.filter
      (fun id -> Eventstream.negb (Eventstream.mem_key K.eqb id output_ids))
      input_ids

  let ids_of = Eventstream.ids_of
end
