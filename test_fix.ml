open Eventstream
open Int_instance
open Fix_engine

let mkEvent id ts seq pl kd =
  { ev_id = id; ev_timestamp = ts; ev_seq = seq; ev_payload = pl; ev_kind = kd }

let event_eq a b =
  a.ev_id = b.ev_id &&
  a.ev_timestamp = b.ev_timestamp &&
  a.ev_seq = b.ev_seq &&
  a.ev_payload = b.ev_payload &&
  a.ev_kind = b.ev_kind

let () =
  Printf.printf "=== FIX Round-Trip & Streaming Tests ===\n\n";

  (* --- Test group 1: parse_fix_event (event_to_fix e) = Some (symbol, e) --- *)

  Printf.printf "--- Round-trip tests ---\n";

  let cases = [
    ("AAPL", mkEvent 1001 100 0 18523 Original);
    ("MSFT", mkEvent 2001 101 1 41255 Correction);
    ("GOOG", mkEvent 3001 100 1 0     Cancel);
    ("TSLA", mkEvent 9999 999999 99 49999 Original);
    ("V",    mkEvent 1 0 0 0 Original);
  ] in

  List.iteri (fun i (sym, ev) ->
    let fix_str = event_to_fix ~sender:"TEST" ~symbol:sym ev in
    match parse_fix_event fix_str with
    | None ->
      Printf.printf "  FAIL test %d: parse returned None for %s\n" (i+1) fix_str;
      assert false
    | Some (parsed_sym, parsed_ev) ->
      assert (parsed_sym = sym);
      assert (event_eq parsed_ev ev);
      Printf.printf "  PASS test %d: %s round-trips\n" (i+1) sym
  ) cases;

  (* --- Test group 2: streaming engine vs batch canonicalize --- *)

  Printf.printf "\n--- Streaming vs batch equivalence ---\n";

  let num_trials = 100 in
  let failures = ref 0 in

  for trial = 1 to num_trials do
    let n = 50 + Random.int 200 in
    let msgs = generate_messages n in

    (* Streaming path *)
    let engine = create_engine () in
    Array.iter (ingest_message engine) msgs;
    let streaming = flush_all engine in

    (* Batch path: collect raw events per symbol, canonicalize each *)
    let per_sym : (string, (int, int) event list) Hashtbl.t = Hashtbl.create 64 in
    Array.iter (fun msg ->
      match parse_fix_event msg with
      | None -> ()
      | Some (sym, ev) ->
        let prev = try Hashtbl.find per_sym sym with Not_found -> [] in
        Hashtbl.replace per_sym sym (ev :: prev)
    ) msgs;
    let batch =
      Hashtbl.fold (fun sym raw acc ->
        (sym, ES.canonicalize raw) :: acc
      ) per_sym []
      |> List.sort (fun (a, _) (b, _) -> String.compare a b)
    in

    if streaming <> batch then begin
      Printf.printf "  FAIL trial %d: streaming != batch (%d msgs)\n" trial n;
      incr failures
    end;

    if trial mod 25 = 0 then
      Printf.printf "  ... %d trials done\n" trial
  done;

  Printf.printf "\n";
  if !failures = 0 then
    Printf.printf "All %d round-trip + %d streaming trials passed.\n"
      (List.length cases) num_trials
  else
    Printf.printf "FAILED: %d streaming mismatches across %d trials.\n"
      !failures num_trials
