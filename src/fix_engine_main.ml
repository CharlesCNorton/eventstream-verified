let () =
  Random.self_init ();
  let args = Array.to_list Sys.argv in
  match args with
  | _ :: "--demo" :: _ -> Fix_engine.run_demo ()
  | _ :: "--bench" :: n_str :: _ ->
    (try Fix_engine.run_benchmark (int_of_string n_str)
     with _ -> Printf.eprintf "Usage: fix_engine --bench N\n"; exit 1)
  | _ :: "--bench" :: [] -> Fix_engine.run_benchmark 5000000
  | _ ->
    Printf.printf "Usage: fix_engine [--demo | --bench [N]]\n";
    Printf.printf "  --demo      Run narrated demo with 3 symbols\n";
    Printf.printf "  --bench N   Benchmark N messages (default 5000000)\n";
    Fix_engine.run_demo ()
