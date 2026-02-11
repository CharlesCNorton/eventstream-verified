open Eventstream
open Eventstream_functor

module IntKey : KEY with type t = int = struct
  type t = int
  let compare a b = Nat.compare a b
  let ord_compare (a : int) (b : int) = Stdlib.compare a b
  let eqb a b = (a = b)
end

module IntPayload : PAYLOAD with type t = int = struct
  type t = int
  let compare a b = Nat.compare a b
  let eqb a b = (a = b)
end

module IntConfig : CONFIG with type key = int and type payload = int = struct
  type key = int
  type payload = int
  type ev = (key, payload) Eventstream.event
  let should_replace old_ new_ = (<) old_.ev_seq new_.ev_seq
  let cancel_handler e acc =
    List.filter (fun x -> not (x.ev_id = e.ev_id)) acc
end

module ES = Make(IntKey)(IntPayload)(IntConfig)

let mkEvent id ts seq pl kd =
  { ev_id = id; ev_timestamp = ts; ev_seq = seq; ev_payload = pl; ev_kind = kd }
