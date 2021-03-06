open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result:
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____15,('Auu____14,'Auu____13) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____15,'Auu____14) FStar_Util.either
  =
  fun uu___87_31  ->
    match uu___87_31 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____46) -> FStar_Util.Inr r
let recorded_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let replaying_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db:
  'Auu____87 . Prims.string -> 'Auu____87 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____97 = FStar_Options.record_hints () in
       if uu____97
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____123 = FStar_Options.use_hints () in
       if uu____123
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____126 = FStar_Options.hint_file () in
           match uu____126 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____130 = FStar_Util.read_hints val_filename in
         match uu____130 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____136 = FStar_Options.hint_info () in
               if uu____136
               then
                 let uu____137 =
                   let uu____138 = FStar_Options.hint_file () in
                   match uu____138 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____142 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____137
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____165 = FStar_Options.hint_info () in
             (if uu____165
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____173 = FStar_Options.record_hints () in
     if uu____173
     then
       let hints =
         let uu____175 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____175 in
       let hints_db =
         let uu____197 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____197; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____200 = FStar_Options.hint_file () in
         match uu____200 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db: 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let filter_using_facts_from:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____280 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____292 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____302 =
        FStar_List.fold_left
          (fun uu____325  ->
             fun d  ->
               match uu____325 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____362 =
                          matches_fact_ids include_assumption_names a in
                        if uu____362
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____387 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____302 with | (pruned_theory,uu____399) -> pruned_theory
let filter_assertions:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____434 = filter_using_facts_from e theory in
            (uu____434, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____444 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____468  ->
                     match uu____468 with
                     | (theory1,n_retained,n_pruned) ->
                         (match d with
                          | FStar_SMTEncoding_Term.Assume a ->
                              if
                                FStar_List.contains
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  core1
                              then
                                ((d :: theory1),
                                  (n_retained + (Prims.parse_int "1")),
                                  n_pruned)
                              else
                                if
                                  FStar_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + (Prims.parse_int "1")))
                          | uu____525 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____444 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____559 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____569 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___88_574  ->
                                         match uu___88_574 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____576 -> false)) in
                               FStar_All.pipe_right uu____569
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____559
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____580 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___89_589  ->
                               match uu___89_589 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____593 -> [])) in
                     FStar_All.pipe_right uu____580
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____597 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____597
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____605 = FStar_Util.string_of_int n_retained in
                     let uu____606 =
                       if n1 <> n_retained
                       then
                         let uu____611 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____611 missed
                       else "" in
                     let uu____619 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____605 uu____606 uu____619
                   else ());
                  (let uu____621 =
                     let uu____624 =
                       let uu____627 =
                         let uu____628 =
                           let uu____629 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____629 in
                         FStar_SMTEncoding_Term.Caption uu____628 in
                       [uu____627] in
                     FStar_List.append theory' uu____624 in
                   (uu____621, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____648 = filter_using_facts_from e x in (uu____648, false)
type errors =
  {
  error_reason: Prims.string;
  error_fuel: Prims.int;
  error_ifuel: Prims.int;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  error_messages:
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list;}
let __proj__Mkerrors__item__error_reason: errors -> Prims.string =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
let __proj__Mkerrors__item__error_fuel: errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
let __proj__Mkerrors__item__error_ifuel: errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
let __proj__Mkerrors__item__error_hint:
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
let __proj__Mkerrors__item__error_messages:
  errors ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
let error_to_short_string: errors -> Prims.string =
  fun err1  ->
    let uu____802 = FStar_Util.string_of_int err1.error_fuel in
    let uu____803 = FStar_Util.string_of_int err1.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason
      uu____802 uu____803
      (if FStar_Option.isSome err1.error_hint then "with hint" else "")
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env;
  query_decl: FStar_SMTEncoding_Term.decl;
  query_name: Prims.string;
  query_index: Prims.int;
  query_range: FStar_Range.range;
  query_fuel: Prims.int;
  query_ifuel: Prims.int;
  query_rlimit: Prims.int;
  query_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  query_errors: errors Prims.list;
  query_all_labels: FStar_SMTEncoding_Term.error_labels;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list;}
let __proj__Mkquery_settings__item__query_env:
  query_settings -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_env
let __proj__Mkquery_settings__item__query_decl:
  query_settings -> FStar_SMTEncoding_Term.decl =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_decl
let __proj__Mkquery_settings__item__query_name:
  query_settings -> Prims.string =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_name
let __proj__Mkquery_settings__item__query_index: query_settings -> Prims.int
  =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_index
let __proj__Mkquery_settings__item__query_range:
  query_settings -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_range
let __proj__Mkquery_settings__item__query_fuel: query_settings -> Prims.int =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_fuel
let __proj__Mkquery_settings__item__query_ifuel: query_settings -> Prims.int
  =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_ifuel
let __proj__Mkquery_settings__item__query_rlimit: query_settings -> Prims.int
  =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_rlimit
let __proj__Mkquery_settings__item__query_hint:
  query_settings -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_hint
let __proj__Mkquery_settings__item__query_errors:
  query_settings -> errors Prims.list =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_errors
let __proj__Mkquery_settings__item__query_all_labels:
  query_settings -> FStar_SMTEncoding_Term.error_labels =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_all_labels
let __proj__Mkquery_settings__item__query_suffix:
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_suffix
let with_fuel_and_diagnostics:
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list
  =
  fun settings  ->
    fun label_assumptions  ->
      let n1 = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1184 =
        let uu____1187 =
          let uu____1188 =
            let uu____1189 = FStar_Util.string_of_int n1 in
            let uu____1190 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1189 uu____1190 in
          FStar_SMTEncoding_Term.Caption uu____1188 in
        let uu____1191 =
          let uu____1194 =
            let uu____1195 =
              let uu____1202 =
                let uu____1203 =
                  let uu____1208 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1211 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1208, uu____1211) in
                FStar_SMTEncoding_Util.mkEq uu____1203 in
              (uu____1202, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1195 in
          let uu____1214 =
            let uu____1217 =
              let uu____1218 =
                let uu____1225 =
                  let uu____1226 =
                    let uu____1231 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1234 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1231, uu____1234) in
                  FStar_SMTEncoding_Util.mkEq uu____1226 in
                (uu____1225, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1218 in
            [uu____1217; settings.query_decl] in
          uu____1194 :: uu____1214 in
        uu____1187 :: uu____1191 in
      let uu____1237 =
        let uu____1240 =
          let uu____1243 =
            let uu____1246 =
              let uu____1247 =
                let uu____1252 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1252) in
              FStar_SMTEncoding_Term.SetOption uu____1247 in
            [uu____1246;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1253 =
            let uu____1256 =
              let uu____1259 = FStar_Options.record_hints () in
              if uu____1259
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1263 =
              let uu____1266 =
                let uu____1269 = FStar_Options.print_z3_statistics () in
                if uu____1269
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1266 settings.query_suffix in
            FStar_List.append uu____1256 uu____1263 in
          FStar_List.append uu____1243 uu____1253 in
        FStar_List.append label_assumptions uu____1240 in
      FStar_List.append uu____1184 uu____1237
let used_hint: query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint
let next_hint:
  query_settings -> FStar_Util.hint FStar_Pervasives_Native.option =
  fun uu____1284  ->
    match uu____1284 with
    | { query_env = uu____1287; query_decl = uu____1288; query_name = qname;
        query_index = qindex; query_range = uu____1291;
        query_fuel = uu____1292; query_ifuel = uu____1293;
        query_rlimit = uu____1294; query_hint = uu____1295;
        query_errors = uu____1296; query_all_labels = uu____1297;
        query_suffix = uu____1298;_} ->
        let uu____1307 = FStar_ST.op_Bang replaying_hints in
        (match uu____1307 with
         | FStar_Pervasives_Native.Some hints ->
             FStar_Util.find_map hints
               (fun uu___90_1335  ->
                  match uu___90_1335 with
                  | FStar_Pervasives_Native.Some hint when
                      (hint.FStar_Util.hint_name = qname) &&
                        (hint.FStar_Util.hint_index = qindex)
                      -> FStar_Pervasives_Native.Some hint
                  | uu____1341 -> FStar_Pervasives_Native.None)
         | uu____1344 -> FStar_Pervasives_Native.None)
let query_errors:
  'Auu____1355 'Auu____1356 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1356,'Auu____1355)
        FStar_Pervasives_Native.tuple3 ->
        errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun uu____1372  ->
      match uu____1372 with
      | (z3status,elapsed_time,stats) ->
          (match z3status with
           | FStar_SMTEncoding_Z3.UNSAT uu____1384 ->
               FStar_Pervasives_Native.None
           | uu____1385 ->
               let uu____1386 =
                 FStar_SMTEncoding_Z3.status_string_and_errors z3status in
               (match uu____1386 with
                | (msg,error_labels) ->
                    let err1 =
                      let uu____1396 =
                        FStar_List.map
                          (fun uu____1417  ->
                             match uu____1417 with
                             | (uu____1428,x,y) -> (x, y)) error_labels in
                      {
                        error_reason = msg;
                        error_fuel = (settings.query_fuel);
                        error_ifuel = (settings.query_ifuel);
                        error_hint = (settings.query_hint);
                        error_messages = uu____1396
                      } in
                    FStar_Pervasives_Native.Some err1))
let detail_hint_replay:
  'Auu____1439 'Auu____1440 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1440,'Auu____1439)
        FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun settings  ->
    fun uu____1454  ->
      match uu____1454 with
      | (z3status,uu____1462,uu____1463) ->
          let uu____1464 =
            (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
          if uu____1464
          then
            (match z3status with
             | FStar_SMTEncoding_Z3.UNSAT uu____1465 -> ()
             | _failed ->
                 let ask_z3 label_assumptions =
                   let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   (let uu____1483 =
                      with_fuel_and_diagnostics settings label_assumptions in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions settings.query_env
                         settings.query_hint) settings.query_all_labels
                      uu____1483 FStar_Pervasives_Native.None
                      (fun r  ->
                         FStar_ST.op_Colon_Equals res
                           (FStar_Pervasives_Native.Some r)));
                   (let uu____1520 = FStar_ST.op_Bang res in
                    FStar_Option.get uu____1520) in
                 FStar_SMTEncoding_ErrorReporting.detail_errors true
                   settings.query_env settings.query_all_labels ask_z3)
          else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err1  ->
            match err1.error_messages with | [] -> false | uu____1576 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1591 = find_localized_errors errs in
    FStar_Option.isSome uu____1591
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1598 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1600 = FStar_Options.n_cores () in
         uu____1600 = (Prims.parse_int "1")) in
    if uu____1598
    then
      let initial_fuel1 =
        let uu___91_1602 = settings in
        let uu____1603 = FStar_Options.initial_fuel () in
        let uu____1604 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___91_1602.query_env);
          query_decl = (uu___91_1602.query_decl);
          query_name = (uu___91_1602.query_name);
          query_index = (uu___91_1602.query_index);
          query_range = (uu___91_1602.query_range);
          query_fuel = uu____1603;
          query_ifuel = uu____1604;
          query_rlimit = (uu___91_1602.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___91_1602.query_errors);
          query_all_labels = (uu___91_1602.query_all_labels);
          query_suffix = (uu___91_1602.query_suffix)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1623 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env)
           settings.query_all_labels uu____1623 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1660 = FStar_ST.op_Bang res in FStar_Option.get uu____1660) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1696 = find_localized_errors settings.query_errors in
       match uu____1696 with
       | FStar_Pervasives_Native.Some err1 ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1706 =
                      let uu____1707 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1707 in
                    FStar_Errors.diag settings.query_range uu____1706));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err1.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1709 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1719 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1719)) in
             FStar_All.pipe_right uu____1709 (FStar_String.concat "; ") in
           let uu____1722 =
             let uu____1729 =
               let uu____1734 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (uu____1734, (settings.query_range)) in
             [uu____1729] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1722)
let query_info:
  query_settings ->
    (FStar_SMTEncoding_Z3.z3status,Prims.int,Prims.string FStar_Util.smap)
      FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1767 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1767
      then
        let uu____1768 = z3result in
        match uu____1768 with
        | (z3status,elapsed_time,statistics) ->
            let uu____1784 =
              FStar_SMTEncoding_Z3.status_string_and_errors z3status in
            (match uu____1784 with
             | (status_string,errs) ->
                 let tag =
                   match z3status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____1792 -> "succeeded"
                   | uu____1793 ->
                       Prims.strcat "failed {reason-unknown="
                         (Prims.strcat status_string "}") in
                 let range =
                   let uu____1795 =
                     let uu____1796 =
                       FStar_Range.string_of_range settings.query_range in
                     let uu____1797 =
                       let uu____1798 = FStar_SMTEncoding_Z3.at_log_file () in
                       Prims.strcat uu____1798 ")" in
                     Prims.strcat uu____1796 uu____1797 in
                   Prims.strcat "(" uu____1795 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu____1802 = FStar_Options.print_z3_statistics () in
                   if uu____1802
                   then
                     let f k v1 a =
                       Prims.strcat a
                         (Prims.strcat k
                            (Prims.strcat "=" (Prims.strcat v1 " "))) in
                     let str =
                       FStar_Util.smap_fold statistics f "statistics={" in
                     let uu____1814 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1")) in
                     Prims.strcat uu____1814 "}"
                   else "" in
                 ((let uu____1817 =
                     let uu____1820 =
                       let uu____1823 =
                         let uu____1826 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu____1827 =
                           let uu____1830 =
                             let uu____1833 =
                               let uu____1836 =
                                 FStar_Util.string_of_int elapsed_time in
                               let uu____1837 =
                                 let uu____1840 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu____1841 =
                                   let uu____1844 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu____1845 =
                                     let uu____1848 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu____1848; stats] in
                                   uu____1844 :: uu____1845 in
                                 uu____1840 :: uu____1841 in
                               uu____1836 :: uu____1837 in
                             used_hint_tag :: uu____1833 in
                           tag :: uu____1830 in
                         uu____1826 :: uu____1827 in
                       (settings.query_name) :: uu____1823 in
                     range :: uu____1820 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____1817);
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____1862  ->
                          match uu____1862 with
                          | (uu____1869,msg,range1) ->
                              let e =
                                FStar_Errors.mk_issue FStar_Errors.EInfo
                                  (FStar_Pervasives_Native.Some range1) msg in
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              let uu____1875 = FStar_Errors.format_issue e in
                              FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1875))))
      else ()
let record_hint:
  'Auu____1885 'Auu____1886 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1886,'Auu____1885)
        FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1907 = z3result in
      match uu____1907 with
      | (z3status,elapsed_time,uu____1916) ->
          let mk_hint core =
            {
              FStar_Util.hint_name = (settings.query_name);
              FStar_Util.hint_index = (settings.query_index);
              FStar_Util.fuel = (settings.query_fuel);
              FStar_Util.ifuel = (settings.query_ifuel);
              FStar_Util.unsat_core = core;
              FStar_Util.query_elapsed_time = (Prims.parse_int "0")
            } in
          let hint_opt =
            let uu____1932 =
              (Prims.op_Negation (used_hint settings)) &&
                (FStar_Options.record_hints ()) in
            if uu____1932
            then
              match z3status with
              | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
                  FStar_Pervasives_Native.Some (mk_hint unsat_core)
              | uu____1938 -> FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some (mk_hint settings.query_hint) in
          let uu____1940 = FStar_ST.op_Bang recorded_hints in
          (match uu____1940 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [hint_opt]))
           | uu____1990 -> ())
let process_result:
  query_settings ->
    (FStar_SMTEncoding_Z3.z3status,Prims.int,Prims.string FStar_Util.smap)
      FStar_Pervasives_Native.tuple3 -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2022 =
         (used_hint settings) &&
           (let uu____2024 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2024) in
       if uu____2022 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
let fold_queries:
  query_settings Prims.list ->
    (query_settings ->
       (FStar_SMTEncoding_Z3.z3result -> Prims.unit) -> Prims.unit)
      ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> Prims.unit) -> Prims.unit
  =
  fun qs  ->
    fun ask1  ->
      fun f  ->
        fun report1  ->
          let rec aux acc qs1 =
            match qs1 with
            | [] -> report1 acc
            | q::qs2 ->
                ask1 q
                  (fun res  ->
                     let uu____2120 = f q res in
                     match uu____2120 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2) in
          aux [] qs
let ask_and_report_errors:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let default_settings =
               let uu____2154 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2154 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2180 = FStar_Options.z3_rlimit_factor () in
                     let uu____2181 =
                       let uu____2182 = FStar_Options.z3_rlimit () in
                       uu____2182 * (Prims.parse_int "544656") in
                     uu____2180 * uu____2181 in
                   let uu____2183 = FStar_TypeChecker_Env.get_range env in
                   let uu____2184 = FStar_Options.initial_fuel () in
                   let uu____2185 = FStar_Options.initial_ifuel () in
                   {
                     query_env = env;
                     query_decl = query;
                     query_name = qname;
                     query_index = index1;
                     query_range = uu____2183;
                     query_fuel = uu____2184;
                     query_ifuel = uu____2185;
                     query_rlimit = rlimit;
                     query_hint = FStar_Pervasives_Native.None;
                     query_errors = [];
                     query_all_labels = all_labels;
                     query_suffix = suffix
                   } in
             let use_hints_setting =
               let uu____2191 = next_hint default_settings in
               match uu____2191 with
               | FStar_Pervasives_Native.Some
                   { FStar_Util.hint_name = uu____2196;
                     FStar_Util.hint_index = uu____2197; FStar_Util.fuel = i;
                     FStar_Util.ifuel = j;
                     FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                       core;
                     FStar_Util.query_elapsed_time = uu____2201;_}
                   ->
                   [(let uu___92_2207 = default_settings in
                     {
                       query_env = (uu___92_2207.query_env);
                       query_decl = (uu___92_2207.query_decl);
                       query_name = (uu___92_2207.query_name);
                       query_index = (uu___92_2207.query_index);
                       query_range = (uu___92_2207.query_range);
                       query_fuel = i;
                       query_ifuel = j;
                       query_rlimit = (uu___92_2207.query_rlimit);
                       query_hint = (FStar_Pervasives_Native.Some core);
                       query_errors = (uu___92_2207.query_errors);
                       query_all_labels = (uu___92_2207.query_all_labels);
                       query_suffix = (uu___92_2207.query_suffix)
                     })]
               | uu____2210 -> [] in
             let initial_fuel_max_ifuel =
               let uu____2216 =
                 let uu____2217 = FStar_Options.max_ifuel () in
                 let uu____2218 = FStar_Options.initial_ifuel () in
                 uu____2217 > uu____2218 in
               if uu____2216
               then
                 let uu____2221 =
                   let uu___93_2222 = default_settings in
                   let uu____2223 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___93_2222.query_env);
                     query_decl = (uu___93_2222.query_decl);
                     query_name = (uu___93_2222.query_name);
                     query_index = (uu___93_2222.query_index);
                     query_range = (uu___93_2222.query_range);
                     query_fuel = (uu___93_2222.query_fuel);
                     query_ifuel = uu____2223;
                     query_rlimit = (uu___93_2222.query_rlimit);
                     query_hint = (uu___93_2222.query_hint);
                     query_errors = (uu___93_2222.query_errors);
                     query_all_labels = (uu___93_2222.query_all_labels);
                     query_suffix = (uu___93_2222.query_suffix)
                   } in
                 [uu____2221]
               else [] in
             let half_max_fuel_max_ifuel =
               let uu____2228 =
                 let uu____2229 =
                   let uu____2230 = FStar_Options.max_fuel () in
                   uu____2230 / (Prims.parse_int "2") in
                 let uu____2237 = FStar_Options.initial_fuel () in
                 uu____2229 > uu____2237 in
               if uu____2228
               then
                 let uu____2240 =
                   let uu___94_2241 = default_settings in
                   let uu____2242 =
                     let uu____2243 = FStar_Options.max_fuel () in
                     uu____2243 / (Prims.parse_int "2") in
                   let uu____2250 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___94_2241.query_env);
                     query_decl = (uu___94_2241.query_decl);
                     query_name = (uu___94_2241.query_name);
                     query_index = (uu___94_2241.query_index);
                     query_range = (uu___94_2241.query_range);
                     query_fuel = uu____2242;
                     query_ifuel = uu____2250;
                     query_rlimit = (uu___94_2241.query_rlimit);
                     query_hint = (uu___94_2241.query_hint);
                     query_errors = (uu___94_2241.query_errors);
                     query_all_labels = (uu___94_2241.query_all_labels);
                     query_suffix = (uu___94_2241.query_suffix)
                   } in
                 [uu____2240]
               else [] in
             let max_fuel_max_ifuel =
               let uu____2255 =
                 (let uu____2260 = FStar_Options.max_fuel () in
                  let uu____2261 = FStar_Options.initial_fuel () in
                  uu____2260 > uu____2261) &&
                   (let uu____2264 = FStar_Options.max_ifuel () in
                    let uu____2265 = FStar_Options.initial_ifuel () in
                    uu____2264 >= uu____2265) in
               if uu____2255
               then
                 let uu____2268 =
                   let uu___95_2269 = default_settings in
                   let uu____2270 = FStar_Options.max_fuel () in
                   let uu____2271 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___95_2269.query_env);
                     query_decl = (uu___95_2269.query_decl);
                     query_name = (uu___95_2269.query_name);
                     query_index = (uu___95_2269.query_index);
                     query_range = (uu___95_2269.query_range);
                     query_fuel = uu____2270;
                     query_ifuel = uu____2271;
                     query_rlimit = (uu___95_2269.query_rlimit);
                     query_hint = (uu___95_2269.query_hint);
                     query_errors = (uu___95_2269.query_errors);
                     query_all_labels = (uu___95_2269.query_all_labels);
                     query_suffix = (uu___95_2269.query_suffix)
                   } in
                 [uu____2268]
               else [] in
             let min_fuel1 =
               let uu____2276 =
                 let uu____2277 = FStar_Options.min_fuel () in
                 let uu____2278 = FStar_Options.initial_fuel () in
                 uu____2277 < uu____2278 in
               if uu____2276
               then
                 let uu____2281 =
                   let uu___96_2282 = default_settings in
                   let uu____2283 = FStar_Options.min_fuel () in
                   {
                     query_env = (uu___96_2282.query_env);
                     query_decl = (uu___96_2282.query_decl);
                     query_name = (uu___96_2282.query_name);
                     query_index = (uu___96_2282.query_index);
                     query_range = (uu___96_2282.query_range);
                     query_fuel = uu____2283;
                     query_ifuel = (Prims.parse_int "1");
                     query_rlimit = (uu___96_2282.query_rlimit);
                     query_hint = (uu___96_2282.query_hint);
                     query_errors = (uu___96_2282.query_errors);
                     query_all_labels = (uu___96_2282.query_all_labels);
                     query_suffix = (uu___96_2282.query_suffix)
                   } in
                 [uu____2281]
               else [] in
             let all_configs =
               FStar_List.append use_hints_setting
                 (FStar_List.append [default_settings]
                    (FStar_List.append initial_fuel_max_ifuel
                       (FStar_List.append half_max_fuel_max_ifuel
                          max_fuel_max_ifuel))) in
             let check_one_config config k =
               (let uu____2301 =
                  (used_hint config) || (FStar_Options.z3_refresh ()) in
                if uu____2301 then FStar_SMTEncoding_Z3.refresh () else ());
               (let uu____2303 = with_fuel_and_diagnostics config [] in
                let uu____2306 =
                  let uu____2309 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                  FStar_Pervasives_Native.Some uu____2309 in
                FStar_SMTEncoding_Z3.ask
                  (filter_assertions config.query_env config.query_hint)
                  config.query_all_labels uu____2303 uu____2306 k) in
             let check_all_configs configs =
               let report1 errs =
                 report_errors
                   (let uu___97_2328 = default_settings in
                    {
                      query_env = (uu___97_2328.query_env);
                      query_decl = (uu___97_2328.query_decl);
                      query_name = (uu___97_2328.query_name);
                      query_index = (uu___97_2328.query_index);
                      query_range = (uu___97_2328.query_range);
                      query_fuel = (uu___97_2328.query_fuel);
                      query_ifuel = (uu___97_2328.query_ifuel);
                      query_rlimit = (uu___97_2328.query_rlimit);
                      query_hint = (uu___97_2328.query_hint);
                      query_errors = errs;
                      query_all_labels = (uu___97_2328.query_all_labels);
                      query_suffix = (uu___97_2328.query_suffix)
                    }) in
               fold_queries configs check_one_config process_result report1 in
             let uu____2329 =
               let uu____2336 = FStar_Options.admit_smt_queries () in
               let uu____2337 = FStar_Options.admit_except () in
               (uu____2336, uu____2337) in
             match uu____2329 with
             | (true ,uu____2342) -> ()
             | (false ,FStar_Pervasives_Native.None ) ->
                 check_all_configs all_configs
             | (false ,FStar_Pervasives_Native.Some id) ->
                 let skip =
                   if FStar_Util.starts_with id "("
                   then
                     let full_query_id =
                       let uu____2354 =
                         let uu____2355 =
                           let uu____2356 =
                             let uu____2357 =
                               FStar_Util.string_of_int
                                 default_settings.query_index in
                             Prims.strcat uu____2357 ")" in
                           Prims.strcat ", " uu____2356 in
                         Prims.strcat default_settings.query_name uu____2355 in
                       Prims.strcat "(" uu____2354 in
                     full_query_id <> id
                   else default_settings.query_name <> id in
                 if Prims.op_Negation skip
                 then check_all_configs all_configs
                 else ())
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2382 =
           let uu____2383 =
             let uu____2384 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2384 in
           FStar_Util.format1 "Starting query at %s" uu____2383 in
         FStar_SMTEncoding_Encode.push uu____2382);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2386 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2386 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2420 =
               let uu____2421 =
                 let uu____2422 =
                   let uu____2423 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2423 in
                 FStar_Util.format1 "Ending query at %s" uu____2422 in
               FStar_SMTEncoding_Encode.pop uu____2421 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2424);
                        FStar_SMTEncoding_Term.freevars = uu____2425;
                        FStar_SMTEncoding_Term.rng = uu____2426;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2427;
                    FStar_SMTEncoding_Term.assumption_name = uu____2428;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2429;_}
                  -> pop1 ()
              | uu____2444 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2445 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2447 -> failwith "Impossible"))
let solver: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark;
    FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark;
    FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark;
    FStar_TypeChecker_Env.encode_modul =
      FStar_SMTEncoding_Encode.encode_modul;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2453 =
             let uu____2460 = FStar_Options.peek () in (e, g, uu____2460) in
           [uu____2453]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2475  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2477  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2479  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____2481  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____2483  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____2485  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2488  -> fun uu____2489  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2492  -> fun uu____2493  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2499 =
             let uu____2506 = FStar_Options.peek () in (e, g, uu____2506) in
           [uu____2499]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2522  -> fun uu____2523  -> fun uu____2524  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____2531  -> fun uu____2532  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____2534  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2536  -> ())
  }