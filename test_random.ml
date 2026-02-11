open Eventstream
open Eventstream_functor
open Int_instance

let canonicalize = ES.canonicalize
let fold_stream = ES.fold_stream
let detect_gaps = ES.detect_gaps

let random_kind () =
  match Random.int 10 with
  | 0 -> Cancel        (* 10% cancel *)
  | 1 | 2 -> Correction (* 20% correction *)
  | _ -> Original       (* 70% original *)

let random_event max_id max_ts =
  let id = Random.int max_id + 1 in
  let ts = Random.int max_ts in
  let seq = Random.int 20 in
  let pl = Random.int 10000 in
  let kd = random_kind () in
  mkEvent id ts seq pl kd

let random_stream n max_id max_ts =
  List.init n (fun _ -> random_event max_id max_ts)

let shuffle lst =
  let arr = Array.of_list lst in
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = Random.int (i + 1) in
    let tmp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- tmp
  done;
  Array.to_list arr

let event_leb a b = ES.event_leb a b

let is_sorted lst =
  let rec check = function
    | [] | [_] -> true
    | a :: (b :: _ as rest) ->
      event_leb a b && check rest
  in check lst

let has_no_cancels lst =
  List.for_all (fun e -> e.ev_kind <> Cancel) lst

let ids_unique lst =
  let ids = List.map (fun e -> e.ev_id) lst in
  let sorted = List.sort compare ids in
  let rec check = function
    | [] | [_] -> true
    | a :: (b :: _ as rest) -> a <> b && check rest
  in check sorted

let output_ids_subset input output =
  let input_ids = List.sort_uniq compare (List.map (fun e -> e.ev_id) input) in
  List.for_all (fun e -> List.mem e.ev_id input_ids) output

(* === String-keyed functor instantiation === *)

module StrKey : KEY with type t = string = struct
  type t = string
  let compare a b =
    let c = String.compare a b in
    if c < 0 then Lt else if c > 0 then Gt else Eq
  let ord_compare = String.compare
  let eqb a b = (a = b)
end

module StrPayload : PAYLOAD with type t = string = struct
  type t = string
  let compare a b =
    let c = String.compare a b in
    if c < 0 then Lt else if c > 0 then Gt else Eq
  let eqb a b = (a = b)
end

module StrConfig : CONFIG with type key = string and type payload = string = struct
  type key = string
  type payload = string
  type ev = (key, payload) Eventstream.event
  let should_replace old_ new_ = String.compare old_.ev_seq new_.ev_seq < 0
  let cancel_handler e acc =
    List.filter (fun x -> not (x.ev_id = e.ev_id)) acc
  let validate _ = ()
end

module StrES = Make(StrKey)(StrPayload)(StrConfig)

let str_mkEvent id ts seq pl kd =
  { ev_id = id; ev_timestamp = ts; ev_seq = seq; ev_payload = pl; ev_kind = kd }

let () =
  Random.self_init ();

  (* === Part 1: Int-keyed random stress test === *)

  let num_trials = 1000 in
  let max_n = 200 in
  let max_id = 50 in
  let max_ts = 1000 in

  Printf.printf "=== Random Stress Test (%d trials, up to %d events) ===\n\n" num_trials max_n;

  let failures = ref 0 in

  for trial = 1 to num_trials do
    let n = Random.int max_n + 1 in
    let stream = random_stream n max_id max_ts in
    let canon = canonicalize stream in

    (* Property 1: output is sorted *)
    if not (is_sorted canon) then begin
      Printf.printf "FAIL trial %d: output not sorted\n" trial;
      incr failures
    end;

    (* Property 2: no cancels in output *)
    if not (has_no_cancels canon) then begin
      Printf.printf "FAIL trial %d: cancel events in output\n" trial;
      incr failures
    end;

    (* Property 3: unique ids *)
    if not (ids_unique canon) then begin
      Printf.printf "FAIL trial %d: duplicate ids in output\n" trial;
      incr failures
    end;

    (* Property 4: output ids are subset of input ids *)
    if not (output_ids_subset stream canon) then begin
      Printf.printf "FAIL trial %d: output id not in input\n" trial;
      incr failures
    end;

    (* Property 5: idempotence *)
    let canon2 = canonicalize canon in
    if canon <> canon2 then begin
      Printf.printf "FAIL trial %d: not idempotent\n" trial;
      incr failures
    end;

    (* Property 6: determinism — shuffle and re-canonicalize *)
    let shuffled = shuffle stream in
    let canon_shuffled = canonicalize shuffled in
    if canon <> canon_shuffled then begin
      Printf.printf "FAIL trial %d: not deterministic under permutation\n" trial;
      incr failures
    end;

    (* Property 7: online-batch equivalence *)
    let online = fold_stream stream in
    if canon <> online then begin
      Printf.printf "FAIL trial %d: fold_stream != canonicalize\n" trial;
      incr failures
    end;

    (* Property 8: gap detection consistency *)
    let gaps = detect_gaps stream in
    let output_ids = List.map (fun e -> e.ev_id) canon in
    List.iter (fun gid ->
      if List.mem gid output_ids then begin
        Printf.printf "FAIL trial %d: gap id %d found in output\n" trial gid;
        incr failures
      end
    ) gaps;

    if trial mod 100 = 0 then
      Printf.printf "  ... %d trials done\n" trial
  done;

  Printf.printf "\n";
  if !failures = 0 then
    Printf.printf "All %d int-keyed random trials passed. 8 properties per trial.\n" num_trials
  else
    Printf.printf "FAILED: %d property violations across %d int-keyed trials.\n" !failures num_trials;

  (* === Part 2: String-keyed functor test === *)

  Printf.printf "\n=== String-Keyed Functor Test (100 trials) ===\n\n";

  let str_failures = ref 0 in
  let str_trials = 100 in

  let random_str () =
    let len = 2 + Random.int 6 in
    String.init len (fun _ -> Char.chr (97 + Random.int 26))
  in

  for trial = 1 to str_trials do
    let n = 10 + Random.int 50 in
    let ids = Array.init 10 (fun _ -> random_str ()) in
    let stream = List.init n (fun _ ->
      let id = ids.(Random.int (Array.length ids)) in
      let ts = random_str () in
      let seq = string_of_int (Random.int 20) in
      let pl = random_str () in
      let kd = random_kind () in
      str_mkEvent id ts seq pl kd
    ) in

    let canon = StrES.canonicalize stream in

    (* Idempotence *)
    let canon2 = StrES.canonicalize canon in
    if canon <> canon2 then begin
      Printf.printf "FAIL str trial %d: not idempotent\n" trial;
      incr str_failures
    end;

    (* Determinism *)
    let shuffled = shuffle stream in
    let canon_s = StrES.canonicalize shuffled in
    if canon <> canon_s then begin
      Printf.printf "FAIL str trial %d: not deterministic\n" trial;
      incr str_failures
    end;

    (* No cancels *)
    if not (List.for_all (fun e -> e.ev_kind <> Cancel) canon) then begin
      Printf.printf "FAIL str trial %d: cancel in output\n" trial;
      incr str_failures
    end;

    (* Unique ids *)
    let ids_out = List.map (fun e -> e.ev_id) canon in
    let sorted_ids = List.sort String.compare ids_out in
    let rec dup_check = function
      | [] | [_] -> false
      | a :: (b :: _ as rest) -> a = b || dup_check rest
    in
    if dup_check sorted_ids then begin
      Printf.printf "FAIL str trial %d: duplicate ids\n" trial;
      incr str_failures
    end;

    if trial mod 25 = 0 then
      Printf.printf "  ... %d trials done\n" trial
  done;

  Printf.printf "\n";
  if !str_failures = 0 then
    Printf.printf "All %d string-keyed trials passed.\n" str_trials
  else
    Printf.printf "FAILED: %d string-keyed violations.\n" !str_failures
