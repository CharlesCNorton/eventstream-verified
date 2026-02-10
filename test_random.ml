open Eventstream

let mkEvent id ts seq pl kd =
  { ev_id = id; ev_timestamp = ts; ev_seq = seq; ev_payload = pl; ev_kind = kd }

let pcmp = Nat.compare
let srep old_ new_ = (<=) old_.ev_seq new_.ev_seq
let canonicalize s = canonicalize pcmp srep s
let fold_stream s = fold_stream pcmp srep s
let detect_gaps s = detect_gaps pcmp srep s

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

let event_leb a b = event_leb pcmp a b

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

let () =
  Random.self_init ();
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
    Printf.printf "All %d random trials passed. 8 properties verified per trial.\n" num_trials
  else
    Printf.printf "FAILED: %d property violations across %d trials.\n" !failures num_trials
