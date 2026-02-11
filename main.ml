open Eventstream
open Int_instance

let canonicalize = ES.canonicalize
let fold_stream = ES.fold_stream
let detect_gaps = ES.detect_gaps

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

  (* Test 10: Cancel then re-add same id *)
  let raw10 = [
    mkEvent 1 100 0 10 Original;
    mkEvent 1 200 1 0 Cancel;
    mkEvent 1 300 2 99 Original;
  ] in
  let canon10 = canonicalize raw10 in
  print_stream "Test 10 - Cancel then re-add" raw10;
  print_stream "Test 10 - Output" canon10;
  assert (List.length canon10 = 1);
  assert ((List.hd canon10).ev_payload = 99);
  assert ((List.hd canon10).ev_timestamp = 300);

  (* Test 11: Multiple corrections to same id, highest seq wins *)
  let raw11 = [
    mkEvent 1 100 0 10 Original;
    mkEvent 1 100 3 30 Correction;
    mkEvent 1 100 1 11 Correction;
    mkEvent 1 100 5 50 Correction;
    mkEvent 1 100 2 20 Correction;
  ] in
  let canon11 = canonicalize raw11 in
  print_stream "Test 11 - Multiple corrections" raw11;
  print_stream "Test 11 - Output" canon11;
  assert (List.length canon11 = 1);
  assert ((List.hd canon11).ev_payload = 50);
  assert ((List.hd canon11).ev_seq = 5);

  (* Test 12: Cancel of nonexistent id is harmless *)
  let raw12 = [
    mkEvent 1 100 0 10 Original;
    mkEvent 99 200 0 0 Cancel;
  ] in
  let canon12 = canonicalize raw12 in
  print_stream "Test 12 - Cancel nonexistent" raw12;
  print_stream "Test 12 - Output" canon12;
  assert (List.length canon12 = 1);
  assert ((List.hd canon12).ev_id = 1);

  (* Test 13: Online-batch equivalence via fold_stream *)
  let raw13 = [
    mkEvent 3 300 0 30 Original;
    mkEvent 1 100 0 10 Original;
    mkEvent 2 200 1 0 Cancel;
    mkEvent 2 150 0 20 Original;
    mkEvent 1 100 1 15 Correction;
  ] in
  let batch13 = canonicalize raw13 in
  let online13 = fold_stream raw13 in
  print_stream "Test 13 - Batch" batch13;
  print_stream "Test 13 - Online (fold_stream)" online13;
  assert (batch13 = online13);

  (* Test 14: All events cancelled *)
  let raw14 = [
    mkEvent 1 100 0 10 Original;
    mkEvent 2 200 0 20 Original;
    mkEvent 1 300 1 0 Cancel;
    mkEvent 2 400 1 0 Cancel;
  ] in
  let canon14 = canonicalize raw14 in
  print_stream "Test 14 - All cancelled" raw14;
  print_stream "Test 14 - Output" canon14;
  assert (canon14 = []);

  (* Test 15: Singleton *)
  let raw15 = [mkEvent 1 100 0 42 Original] in
  let canon15 = canonicalize raw15 in
  assert (List.length canon15 = 1);
  assert ((List.hd canon15).ev_payload = 42);

  (* Test 16: Idempotence on complex stream *)
  let canon13a = canonicalize raw13 in
  let canon13b = canonicalize canon13a in
  let canon13c = canonicalize canon13b in
  assert (canon13a = canon13b);
  assert (canon13b = canon13c);

  Printf.printf "All 16 tests passed.\n"
