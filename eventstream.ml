
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type comparison =
| Eq
| Lt
| Gt

module Nat =
 struct
  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val lex_compare : int list -> int list -> comparison **)

let rec lex_compare l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> Eq
           | _ :: _ -> Lt)
  | k1 :: rest1 ->
    (match l2 with
     | [] -> Gt
     | k2 :: rest2 ->
       (match Nat.compare k1 k2 with
        | Eq -> lex_compare rest1 rest2
        | x -> x))

(** val lex_leb : int list -> int list -> bool **)

let lex_leb l1 l2 =
  match lex_compare l1 l2 with
  | Gt -> false
  | _ -> true

type event_kind =
| Original
| Correction
| Cancel

type event = { ev_id : int; ev_timestamp : int; ev_seq : int;
               ev_payload : int; ev_kind : event_kind }

(** val event_kind_eqb : event_kind -> event_kind -> bool **)

let event_kind_eqb k1 k2 =
  match k1 with
  | Original -> (match k2 with
                 | Original -> true
                 | _ -> false)
  | Correction -> (match k2 with
                   | Correction -> true
                   | _ -> false)
  | Cancel -> (match k2 with
               | Cancel -> true
               | _ -> false)

(** val event_eqb : event -> event -> bool **)

let event_eqb e1 e2 =
  (&&)
    ((&&)
      ((&&)
        ((&&) ((=) e1.ev_id e2.ev_id) ((=) e1.ev_timestamp e2.ev_timestamp))
        ((=) e1.ev_seq e2.ev_seq)) ((=) e1.ev_payload e2.ev_payload))
    (event_kind_eqb e1.ev_kind e2.ev_kind)

(** val kind_index : event_kind -> int **)

let kind_index = function
| Original -> 0
| Correction -> Stdlib.Int.succ 0
| Cancel -> Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val event_keys : event -> int list **)

let event_keys e =
  e.ev_timestamp :: (e.ev_seq :: (e.ev_id :: (e.ev_payload :: ((kind_index
                                                                 e.ev_kind) :: []))))

(** val event_leb : event -> event -> bool **)

let event_leb e1 e2 =
  lex_leb (event_keys e1) (event_keys e2)

(** val insert : event -> event list -> event list **)

let rec insert e = function
| [] -> e :: []
| h :: t -> if event_leb e h then e :: (h :: t) else h :: (insert e t)

(** val sort_events : event list -> event list **)

let rec sort_events = function
| [] -> []
| h :: t -> insert h (sort_events t)

(** val replace_or_add : event -> event list -> event list **)

let rec replace_or_add e = function
| [] -> e :: []
| h :: t ->
  if (=) h.ev_id e.ev_id
  then if (<=) h.ev_seq e.ev_seq then e :: t else h :: t
  else h :: (replace_or_add e t)

(** val apply_events : event list -> event list -> event list **)

let rec apply_events sorted acc =
  match sorted with
  | [] -> acc
  | e :: rest ->
    (match e.ev_kind with
     | Cancel ->
       apply_events rest (filter (fun x -> negb ((=) x.ev_id e.ev_id)) acc)
     | _ -> apply_events rest (replace_or_add e acc))

(** val canonicalize : event list -> event list **)

let canonicalize stream =
  sort_events (apply_events (sort_events stream) [])

(** val ids_of : event list -> int list **)

let ids_of l =
  map (fun e -> e.ev_id) l

(** val process_one : event list -> event -> event list **)

let process_one acc e =
  match e.ev_kind with
  | Cancel -> filter (fun x -> negb ((=) x.ev_id e.ev_id)) acc
  | _ -> replace_or_add e acc

(** val fold_stream : event list -> event list **)

let fold_stream stream =
  sort_events (fold_left process_one (sort_events stream) [])

(** val mem_nat : int -> int list -> bool **)

let rec mem_nat n = function
| [] -> false
| h :: t -> (||) ((=) n h) (mem_nat n t)

(** val dedup_nat : int list -> int list **)

let rec dedup_nat = function
| [] -> []
| h :: t -> if mem_nat h t then dedup_nat t else h :: (dedup_nat t)

(** val detect_gaps : event list -> int list **)

let detect_gaps stream =
  let input_ids = dedup_nat (ids_of stream) in
  let output_ids = ids_of (canonicalize stream) in
  filter (fun id -> negb (mem_nat id output_ids)) input_ids
