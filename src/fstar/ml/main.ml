let x = 
      Printexc.record_backtrace true;
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };
      (* enable Jacques-Henri Jourdan's statistical memory profiler
         (send SIGUSR1 to output results, which will create a
         memory_profile file). For more info:
         https://github.com/jhjourdan/ocaml/tree/memprof *)
      let () =
        let filename = Printf.sprintf "statistical-memprof-%d" (Unix.getpid ()) in
        let sampling_rate = 1E-4 in
        let callstack_size = 20 in
        let threshold = 100 in
        MemprofHelpers.start filename sampling_rate callstack_size threshold
      in
      FStar_FStar.main ()
