open Eventstream

let mkEvent id ts seq pl kd =
  { ev_id = id; ev_timestamp = ts; ev_seq = seq; ev_payload = pl; ev_kind = kd }

let string_of_kind = function
  | Original -> "Original"
  | Correction -> "Correction"
  | Cancel -> "Cancel"

let print_event e =
  Printf.printf "  {id=%d ts=%d seq=%d payload=%d kind=%s}\n"
    e.ev_id e.ev_timestamp e.ev_seq e.ev_payload (string_of_kind e.ev_kind)

let print_stream label events =
  Printf.printf "%s (%d events):\n" label (List.length events);
  List.iter print_event events;
  print_newline ()

let print_gaps label gaps =
  Printf.printf "%s: [%s]\n\n" label (String.concat "; " (List.map string_of_int gaps))

let () =
  Printf.printf "=== Eventstream Canonicalization (Verified, Extracted) ===\n\n";

  (* Test 1: Deduplication *)
  let raw1 = [
    mkEvent 1 100 0 42 Original;
    mkEvent 1 100 0 42 Original;
    mkEvent 2 200 0 99 Original;
  ] in
  let canon1 = canonicalize raw1 in
  print_stream "Test 1 - Dedup input" raw1;
  print_stream "Test 1 - Dedup output" canon1;
  assert (List.length canon1 = 2);

  (* Test 2: Reordering *)
  let raw2 = [
    mkEvent 3 300 0 30 Original;
    mkEvent 1 100 0 10 Original;
    mkEvent 2 200 0 20 Original;
  ] in
  let canon2 = canonicalize raw2 in
  print_stream "Test 2 - Reorder input" raw2;
  print_stream "Test 2 - Reorder output" canon2;
  assert ((List.hd canon2).ev_timestamp = 100);
  assert ((List.nth canon2 1).ev_timestamp = 200);
  assert ((List.nth canon2 2).ev_timestamp = 300);

  (* Test 3: Correction replaces original with higher seq *)
  let raw3 = [
    mkEvent 1 100 0 42 Original;
    mkEvent 1 100 1 99 Correction;
  ] in
  let canon3 = canonicalize raw3 in
  print_stream "Test 3 - Correction input" raw3;
  print_stream "Test 3 - Correction output" canon3;
  assert (List.length canon3 = 1);
  assert ((List.hd canon3).ev_payload = 99);

  (* Test 4: Cancel removes event *)
  let raw4 = [
    mkEvent 1 100 0 42 Original;
    mkEvent 2 200 0 99 Original;
    mkEvent 1 300 1 0 Cancel;
  ] in
  let canon4 = canonicalize raw4 in
  print_stream "Test 4 - Cancel input" raw4;
  print_stream "Test 4 - Cancel output" canon4;
  assert (List.length canon4 = 1);
  assert ((List.hd canon4).ev_id = 2);

  (* Test 5: Idempotence *)
  let raw5 = [
    mkEvent 5 500 0 50 Original;
    mkEvent 3 300 0 30 Original;
    mkEvent 3 300 1 31 Correction;
    mkEvent 1 100 0 10 Original;
    mkEvent 1 400 1 0 Cancel;
    mkEvent 4 400 0 40 Original;
    mkEvent 2 200 0 20 Original;
  ] in
  let canon5a = canonicalize raw5 in
  let canon5b = canonicalize canon5a in
  print_stream "Test 5 - Complex input" raw5;
  print_stream "Test 5 - First canonicalize" canon5a;
  print_stream "Test 5 - Second canonicalize (idempotence)" canon5b;
  assert (canon5a = canon5b);

  (* Test 6: Determinism - same events, different order *)
  let raw6a = [mkEvent 2 200 0 20 Original; mkEvent 1 100 0 10 Original] in
  let raw6b = [mkEvent 1 100 0 10 Original; mkEvent 2 200 0 20 Original] in
  let canon6a = canonicalize raw6a in
  let canon6b = canonicalize raw6b in
  print_stream "Test 6a - Order A" raw6a;
  print_stream "Test 6a - Canonicalized" canon6a;
  print_stream "Test 6b - Order B" raw6b;
  print_stream "Test 6b - Canonicalized" canon6b;
  assert (canon6a = canon6b);

  (* Test 7: Empty stream *)
  assert (canonicalize [] = []);

  (* Test 8: Low-seq correction ignored *)
  let raw8 = [
    mkEvent 1 100 5 42 Original;
    mkEvent 1 100 3 99 Correction;
  ] in
  let canon8 = canonicalize raw8 in
  print_stream "Test 8 - Low-seq correction input" raw8;
  print_stream "Test 8 - Low-seq correction output" canon8;
  assert (List.length canon8 = 1);
  assert ((List.hd canon8).ev_payload = 42);

  (* Test 9: Gap detection *)
  let raw9 = [
    mkEvent 1 100 0 10 Original;
    mkEvent 2 200 0 20 Original;
    mkEvent 3 300 0 30 Original;
    mkEvent 1 400 1 0 Cancel;
    mkEvent 3 500 1 0 Cancel;
  ] in
  let gaps = detect_gaps raw9 in
  print_stream "Test 9 - Gap detection input" raw9;
  print_gaps "Test 9 - Gaps (cancelled ids)" gaps;
  assert (List.mem 1 gaps);
  assert (List.mem 3 gaps);
  assert (not (List.mem 2 gaps));

  Printf.printf "All tests passed.\n"
