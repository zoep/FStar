open Prims
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut
let uu___is_VerifyAll: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____5 -> false
let uu___is_VerifyUserList: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____10 -> false
let uu___is_VerifyFigureItOut: verify_mode -> Prims.bool =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____15 -> false
type map =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
type color =
  | White
  | Gray
  | Black
let uu___is_White: color -> Prims.bool =
  fun projectee  -> match projectee with | White  -> true | uu____30 -> false
let uu___is_Gray: color -> Prims.bool =
  fun projectee  -> match projectee with | Gray  -> true | uu____35 -> false
let uu___is_Black: color -> Prims.bool =
  fun projectee  -> match projectee with | Black  -> true | uu____40 -> false
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____45 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____50 -> false
let check_and_strip_suffix:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"] in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext in
           let l = FStar_String.length f in
           let uu____77 =
             (l > lext) &&
               (let uu____89 = FStar_String.substring f (l - lext) lext in
                uu____89 = ext) in
           if uu____77
           then
             let uu____106 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext) in
             FStar_Pervasives_Native.Some uu____106
           else FStar_Pervasives_Native.None) suffixes in
    let uu____118 = FStar_List.filter FStar_Util.is_some matches in
    match uu____118 with
    | (FStar_Pervasives_Native.Some m)::uu____128 ->
        FStar_Pervasives_Native.Some m
    | uu____135 -> FStar_Pervasives_Native.None
let is_interface: Prims.string -> Prims.bool =
  fun f  ->
    let uu____144 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")) in
    uu____144 = 'i'
let is_implementation: Prims.string -> Prims.bool =
  fun f  -> let uu____149 = is_interface f in Prims.op_Negation uu____149
let list_of_option:
  'Auu____154 .
    'Auu____154 FStar_Pervasives_Native.option -> 'Auu____154 Prims.list
  =
  fun uu___83_162  ->
    match uu___83_162 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
let list_of_pair:
  'Auu____170 .
    ('Auu____170 FStar_Pervasives_Native.option,'Auu____170
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____170 Prims.list
  =
  fun uu____184  ->
    match uu____184 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
let lowercase_module_name: Prims.string -> Prims.string =
  fun f  ->
    let uu____207 =
      let uu____210 = FStar_Util.basename f in
      check_and_strip_suffix uu____210 in
    match uu____207 with
    | FStar_Pervasives_Native.Some longname ->
        FStar_String.lowercase longname
    | FStar_Pervasives_Native.None  ->
        let uu____212 =
          let uu____213 = FStar_Util.format1 "not a valid FStar file: %s\n" f in
          FStar_Errors.Err uu____213 in
        FStar_Exn.raise uu____212
let build_map: Prims.string Prims.list -> map =
  fun filenames  ->
    let include_directories = FStar_Options.include_path () in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories in
    let include_directories2 = FStar_List.unique include_directories1 in
    let cwd =
      let uu____232 = FStar_Util.getcwd () in
      FStar_Util.normalize_file_path uu____232 in
    let map1 = FStar_Util.smap_create (Prims.parse_int "41") in
    let add_entry key full_path =
      let uu____259 = FStar_Util.smap_try_find map1 key in
      match uu____259 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____296 = is_interface full_path in
          if uu____296
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____330 = is_interface full_path in
          if uu____330
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path)) in
    FStar_List.iter
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d in
           FStar_List.iter
             (fun f  ->
                let f1 = FStar_Util.basename f in
                let uu____371 = check_and_strip_suffix f1 in
                match uu____371 with
                | FStar_Pervasives_Native.Some longname ->
                    let full_path =
                      if d = cwd then f1 else FStar_Util.join_paths d f1 in
                    let key = FStar_String.lowercase longname in
                    add_entry key full_path
                | FStar_Pervasives_Native.None  -> ()) files
         else
           (let uu____379 =
              let uu____380 =
                FStar_Util.format1 "not a valid include directory: %s\n" d in
              FStar_Errors.Err uu____380 in
            FStar_Exn.raise uu____379)) include_directories2;
    FStar_List.iter
      (fun f  ->
         let uu____385 = lowercase_module_name f in add_entry uu____385 f)
      filenames;
    map1
let enter_namespace: map -> map -> Prims.string -> Prims.bool =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false in
        let prefix2 = Prims.strcat prefix1 "." in
        (let uu____403 =
           let uu____406 = FStar_Util.smap_keys original_map in
           FStar_List.unique uu____406 in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2)) in
                let filename =
                  let uu____432 = FStar_Util.smap_try_find original_map k in
                  FStar_Util.must uu____432 in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____403);
        FStar_ST.op_Bang found
let string_of_lid: FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else [] in
      let names =
        let uu____534 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns in
        FStar_List.append uu____534 suffix in
      FStar_String.concat "." names
let lowercase_join_longident:
  FStar_Ident.lident -> Prims.bool -> Prims.string =
  fun l  ->
    fun last1  ->
      let uu____547 = string_of_lid l last1 in
      FStar_String.lowercase uu____547
let namespace_of_lid: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____552 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns in
    FStar_String.concat "_" uu____552
let check_module_declaration_against_filename:
  FStar_Ident.lident -> Prims.string -> Prims.unit =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true in
      let uu____564 =
        let uu____565 =
          let uu____566 =
            let uu____567 =
              let uu____570 = FStar_Util.basename filename in
              check_and_strip_suffix uu____570 in
            FStar_Util.must uu____567 in
          FStar_String.lowercase uu____566 in
        uu____565 <> k' in
      if uu____564
      then
        let uu____571 = string_of_lid lid true in
        FStar_Util.print2_warning
          "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n"
          uu____571 filename
      else ()
exception Exit
let uu___is_Exit: Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Exit  -> true | uu____577 -> false
let hard_coded_dependencies:
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun filename  ->
    let filename1 = FStar_Util.basename filename in
    let corelibs =
      let uu____592 = FStar_Options.prims_basename () in
      let uu____593 =
        let uu____596 = FStar_Options.pervasives_basename () in
        let uu____597 =
          let uu____600 = FStar_Options.pervasives_native_basename () in
          [uu____600] in
        uu____596 :: uu____597 in
      uu____592 :: uu____593 in
    if FStar_List.mem filename1 corelibs
    then []
    else
      [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
      (FStar_Parser_Const.prims_lid, Open_module);
      (FStar_Parser_Const.pervasives_lid, Open_module)]
let collect_one:
  (Prims.string,Prims.bool FStar_ST.ref) FStar_Pervasives_Native.tuple2
    Prims.list ->
    verify_mode ->
      Prims.bool -> map -> Prims.string -> Prims.string Prims.list
  =
  fun verify_flags  ->
    fun verify_mode  ->
      fun is_user_provided_filename  ->
        fun original_map  ->
          fun filename  ->
            let deps = FStar_Util.mk_ref [] in
            let add_dep d =
              let uu____679 =
                let uu____680 =
                  let uu____681 = FStar_ST.op_Bang deps in
                  FStar_List.existsML (fun d'  -> d' = d) uu____681 in
                Prims.op_Negation uu____680 in
              if uu____679
              then
                let uu____718 =
                  let uu____721 = FStar_ST.op_Bang deps in d :: uu____721 in
                FStar_ST.op_Colon_Equals deps uu____718
              else () in
            let working_map = FStar_Util.smap_copy original_map in
            let record_open_module let_open lid =
              let key = lowercase_join_longident lid true in
              let uu____816 = FStar_Util.smap_try_find working_map key in
              match uu____816 with
              | FStar_Pervasives_Native.Some pair ->
                  (FStar_List.iter
                     (fun f  ->
                        let uu____856 = lowercase_module_name f in
                        add_dep uu____856) (list_of_pair pair);
                   true)
              | FStar_Pervasives_Native.None  ->
                  let r = enter_namespace original_map working_map key in
                  (if Prims.op_Negation r
                   then
                     (if let_open
                      then
                        FStar_Exn.raise
                          (FStar_Errors.Err
                             "let-open only supported for modules, not namespaces")
                      else
                        (let uu____868 = string_of_lid lid true in
                         FStar_Util.print2_warning
                           "Warning: in %s: no modules in namespace %s and no file with that name either\n"
                           filename uu____868))
                   else ();
                   false) in
            let record_open_namespace error_msg lid =
              let key = lowercase_join_longident lid true in
              let r = enter_namespace original_map working_map key in
              if Prims.op_Negation r
              then
                match error_msg with
                | FStar_Pervasives_Native.Some e ->
                    FStar_Exn.raise (FStar_Errors.Err e)
                | FStar_Pervasives_Native.None  ->
                    let uu____884 = string_of_lid lid true in
                    FStar_Util.print1_warning
                      "Warning: no modules in namespace %s and no file with that name either\n"
                      uu____884
              else () in
            let record_open let_open lid =
              let uu____893 = record_open_module let_open lid in
              if uu____893
              then ()
              else
                (let msg =
                   if let_open
                   then
                     FStar_Pervasives_Native.Some
                       "let-open only supported for modules, not namespaces"
                   else FStar_Pervasives_Native.None in
                 record_open_namespace msg lid) in
            let record_open_module_or_namespace uu____908 =
              match uu____908 with
              | (lid,kind) ->
                  (match kind with
                   | Open_namespace  ->
                       record_open_namespace FStar_Pervasives_Native.None lid
                   | Open_module  ->
                       let uu____915 = record_open_module false lid in ()) in
            let record_module_alias ident lid =
              let key = FStar_String.lowercase (FStar_Ident.text_of_id ident) in
              let alias = lowercase_join_longident lid true in
              let uu____925 = FStar_Util.smap_try_find original_map alias in
              match uu____925 with
              | FStar_Pervasives_Native.Some deps_of_aliased_module ->
                  FStar_Util.smap_add working_map key deps_of_aliased_module
              | FStar_Pervasives_Native.None  ->
                  let uu____977 =
                    let uu____978 =
                      FStar_Util.format1
                        "module not found in search path: %s\n" alias in
                    FStar_Errors.Err uu____978 in
                  FStar_Exn.raise uu____977 in
            let record_lid lid =
              let try_key key =
                let uu____987 = FStar_Util.smap_try_find working_map key in
                match uu____987 with
                | FStar_Pervasives_Native.Some pair ->
                    FStar_List.iter
                      (fun f  ->
                         let uu____1026 = lowercase_module_name f in
                         add_dep uu____1026) (list_of_pair pair)
                | FStar_Pervasives_Native.None  ->
                    let uu____1035 =
                      ((FStar_List.length lid.FStar_Ident.ns) >
                         (Prims.parse_int "0"))
                        && (FStar_Options.debug_any ()) in
                    if uu____1035
                    then
                      let uu____1036 =
                        FStar_Range.string_of_range
                          (FStar_Ident.range_of_lid lid) in
                      let uu____1037 = string_of_lid lid false in
                      FStar_Util.print2_warning
                        "%s (Warning): unbound module reference %s\n"
                        uu____1036 uu____1037
                    else () in
              let uu____1040 = lowercase_join_longident lid false in
              try_key uu____1040 in
            let auto_open = hard_coded_dependencies filename in
            FStar_List.iter record_open_module_or_namespace auto_open;
            (let num_of_toplevelmods =
               FStar_Util.mk_ref (Prims.parse_int "0") in
             let rec collect_file uu___84_1130 =
               match uu___84_1130 with
               | modul::[] -> collect_module modul
               | modules ->
                   (FStar_Util.print1_warning
                      "Warning: file %s does not respect the one module per file convention\n"
                      filename;
                    FStar_List.iter collect_module modules)
             and collect_module uu___85_1138 =
               match uu___85_1138 with
               | FStar_Parser_AST.Module (lid,decls) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1147 =
                         let uu____1148 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1148 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1151 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1151
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1152 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1152
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1220  ->
                              match uu____1220 with
                              | (m,r) ->
                                  let uu____1401 =
                                    let uu____1402 =
                                      let uu____1403 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1403 in
                                    (FStar_String.lowercase m) = uu____1402 in
                                  if uu____1401
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
               | FStar_Parser_AST.Interface (lid,decls,uu____1513) ->
                   (check_module_declaration_against_filename lid filename;
                    if
                      (FStar_List.length lid.FStar_Ident.ns) >
                        (Prims.parse_int "0")
                    then
                      (let uu____1520 =
                         let uu____1521 = namespace_of_lid lid in
                         enter_namespace original_map working_map uu____1521 in
                       ())
                    else ();
                    (match verify_mode with
                     | VerifyAll  ->
                         let uu____1524 = string_of_lid lid true in
                         FStar_Options.add_verify_module uu____1524
                     | VerifyFigureItOut  ->
                         if is_user_provided_filename
                         then
                           let uu____1525 = string_of_lid lid true in
                           FStar_Options.add_verify_module uu____1525
                         else ()
                     | VerifyUserList  ->
                         FStar_List.iter
                           (fun uu____1593  ->
                              match uu____1593 with
                              | (m,r) ->
                                  let uu____1774 =
                                    let uu____1775 =
                                      let uu____1776 = string_of_lid lid true in
                                      FStar_String.lowercase uu____1776 in
                                    (FStar_String.lowercase m) = uu____1775 in
                                  if uu____1774
                                  then FStar_ST.op_Colon_Equals r true
                                  else ()) verify_flags);
                    collect_decls decls)
             and collect_decls decls =
               FStar_List.iter
                 (fun x  ->
                    collect_decl x.FStar_Parser_AST.d;
                    FStar_List.iter collect_term x.FStar_Parser_AST.attrs)
                 decls
             and collect_decl uu___86_1891 =
               match uu___86_1891 with
               | FStar_Parser_AST.Include lid -> record_open false lid
               | FStar_Parser_AST.Open lid -> record_open false lid
               | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
                   ((let uu____1897 = lowercase_join_longident lid true in
                     add_dep uu____1897);
                    record_module_alias ident lid)
               | FStar_Parser_AST.TopLevelLet (uu____1898,patterms) ->
                   FStar_List.iter
                     (fun uu____1920  ->
                        match uu____1920 with
                        | (pat,t) -> (collect_pattern pat; collect_term t))
                     patterms
               | FStar_Parser_AST.Main t -> collect_term t
               | FStar_Parser_AST.Assume (uu____1929,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1931;
                     FStar_Parser_AST.mdest = uu____1932;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.NonReifiableLift t;_}
                   -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1934;
                     FStar_Parser_AST.mdest = uu____1935;
                     FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree
                       t;_}
                   -> collect_term t
               | FStar_Parser_AST.Val (uu____1937,t) -> collect_term t
               | FStar_Parser_AST.SubEffect
                   { FStar_Parser_AST.msource = uu____1939;
                     FStar_Parser_AST.mdest = uu____1940;
                     FStar_Parser_AST.lift_op =
                       FStar_Parser_AST.ReifiableLift (t0,t1);_}
                   -> (collect_term t0; collect_term t1)
               | FStar_Parser_AST.Tycon (uu____1944,ts) ->
                   let ts1 =
                     FStar_List.map
                       (fun uu____1974  ->
                          match uu____1974 with | (x,docnik) -> x) ts in
                   FStar_List.iter collect_tycon ts1
               | FStar_Parser_AST.Exception (uu____1987,t) ->
                   FStar_Util.iter_opt t collect_term
               | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
               | FStar_Parser_AST.Fsdoc uu____1994 -> ()
               | FStar_Parser_AST.Pragma uu____1995 -> ()
               | FStar_Parser_AST.TopLevelModule lid ->
                   (FStar_Util.incr num_of_toplevelmods;
                    (let uu____2019 =
                       let uu____2020 = FStar_ST.op_Bang num_of_toplevelmods in
                       uu____2020 > (Prims.parse_int "1") in
                     if uu____2019
                     then
                       let uu____2045 =
                         let uu____2046 =
                           let uu____2047 = string_of_lid lid true in
                           FStar_Util.format1
                             "Automatic dependency analysis demands one module per file (module %s not supported)"
                             uu____2047 in
                         FStar_Errors.Err uu____2046 in
                       FStar_Exn.raise uu____2045
                     else ()))
             and collect_tycon uu___87_2049 =
               match uu___87_2049 with
               | FStar_Parser_AST.TyconAbstract (uu____2050,binders,k) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term)
               | FStar_Parser_AST.TyconAbbrev (uu____2062,binders,k,t) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    collect_term t)
               | FStar_Parser_AST.TyconRecord
                   (uu____2076,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2122  ->
                         match uu____2122 with
                         | (uu____2131,t,uu____2133) -> collect_term t)
                      identterms)
               | FStar_Parser_AST.TyconVariant
                   (uu____2138,binders,k,identterms) ->
                   (collect_binders binders;
                    FStar_Util.iter_opt k collect_term;
                    FStar_List.iter
                      (fun uu____2197  ->
                         match uu____2197 with
                         | (uu____2210,t,uu____2212,uu____2213) ->
                             FStar_Util.iter_opt t collect_term) identterms)
             and collect_effect_decl uu___88_2222 =
               match uu___88_2222 with
               | FStar_Parser_AST.DefineEffect (uu____2223,binders,t,decls)
                   ->
                   (collect_binders binders;
                    collect_term t;
                    collect_decls decls)
               | FStar_Parser_AST.RedefineEffect (uu____2237,binders,t) ->
                   (collect_binders binders; collect_term t)
             and collect_binders binders =
               FStar_List.iter collect_binder binders
             and collect_binder uu___89_2248 =
               match uu___89_2248 with
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.Annotated
                     (uu____2249,t);
                   FStar_Parser_AST.brange = uu____2251;
                   FStar_Parser_AST.blevel = uu____2252;
                   FStar_Parser_AST.aqual = uu____2253;_} -> collect_term t
               | {
                   FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated
                     (uu____2254,t);
                   FStar_Parser_AST.brange = uu____2256;
                   FStar_Parser_AST.blevel = uu____2257;
                   FStar_Parser_AST.aqual = uu____2258;_} -> collect_term t
               | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
                   FStar_Parser_AST.brange = uu____2260;
                   FStar_Parser_AST.blevel = uu____2261;
                   FStar_Parser_AST.aqual = uu____2262;_} -> collect_term t
               | uu____2263 -> ()
             and collect_term t = collect_term' t.FStar_Parser_AST.tm
             and collect_constant uu___90_2265 =
               match uu___90_2265 with
               | FStar_Const.Const_int
                   (uu____2266,FStar_Pervasives_Native.Some
                    (signedness,width))
                   ->
                   let u =
                     match signedness with
                     | FStar_Const.Unsigned  -> "u"
                     | FStar_Const.Signed  -> "" in
                   let w =
                     match width with
                     | FStar_Const.Int8  -> "8"
                     | FStar_Const.Int16  -> "16"
                     | FStar_Const.Int32  -> "32"
                     | FStar_Const.Int64  -> "64" in
                   let uu____2281 = FStar_Util.format2 "fstar.%sint%s" u w in
                   add_dep uu____2281
               | uu____2282 -> ()
             and collect_term' uu___91_2283 =
               match uu___91_2283 with
               | FStar_Parser_AST.Wild  -> ()
               | FStar_Parser_AST.Const c -> collect_constant c
               | FStar_Parser_AST.Op (s,ts) ->
                   (if (FStar_Ident.text_of_id s) = "@"
                    then
                      (let uu____2292 =
                         let uu____2293 =
                           FStar_Ident.lid_of_path
                             (FStar_Ident.path_of_text
                                "FStar.List.Tot.Base.append")
                             FStar_Range.dummyRange in
                         FStar_Parser_AST.Name uu____2293 in
                       collect_term' uu____2292)
                    else ();
                    FStar_List.iter collect_term ts)
               | FStar_Parser_AST.Tvar uu____2295 -> ()
               | FStar_Parser_AST.Uvar uu____2296 -> ()
               | FStar_Parser_AST.Var lid -> record_lid lid
               | FStar_Parser_AST.Projector (lid,uu____2299) ->
                   record_lid lid
               | FStar_Parser_AST.Discrim lid -> record_lid lid
               | FStar_Parser_AST.Name lid -> record_lid lid
               | FStar_Parser_AST.Construct (lid,termimps) ->
                   (if (FStar_List.length termimps) = (Prims.parse_int "1")
                    then record_lid lid
                    else ();
                    FStar_List.iter
                      (fun uu____2329  ->
                         match uu____2329 with
                         | (t,uu____2335) -> collect_term t) termimps)
               | FStar_Parser_AST.Abs (pats,t) ->
                   (collect_patterns pats; collect_term t)
               | FStar_Parser_AST.App (t1,t2,uu____2345) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Let (uu____2347,patterms,t) ->
                   (FStar_List.iter
                      (fun uu____2371  ->
                         match uu____2371 with
                         | (pat,t1) -> (collect_pattern pat; collect_term t1))
                      patterms;
                    collect_term t)
               | FStar_Parser_AST.LetOpen (lid,t) ->
                   (record_open true lid; collect_term t)
               | FStar_Parser_AST.Bind (uu____2382,t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Seq (t1,t2) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.If (t1,t2,t3) ->
                   (collect_term t1; collect_term t2; collect_term t3)
               | FStar_Parser_AST.Match (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.TryWith (t,bs) ->
                   (collect_term t; collect_branches bs)
               | FStar_Parser_AST.Ascribed
                   (t1,t2,FStar_Pervasives_Native.None ) ->
                   (collect_term t1; collect_term t2)
               | FStar_Parser_AST.Ascribed
                   (t1,t2,FStar_Pervasives_Native.Some tac) ->
                   (collect_term t1; collect_term t2; collect_term tac)
               | FStar_Parser_AST.Record (t,idterms) ->
                   (FStar_Util.iter_opt t collect_term;
                    FStar_List.iter
                      (fun uu____2478  ->
                         match uu____2478 with
                         | (uu____2483,t1) -> collect_term t1) idterms)
               | FStar_Parser_AST.Project (t,uu____2486) -> collect_term t
               | FStar_Parser_AST.Product (binders,t) ->
                   (collect_binders binders; collect_term t)
               | FStar_Parser_AST.Sum (binders,t) ->
                   (collect_binders binders; collect_term t)
               | FStar_Parser_AST.QForall (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.QExists (binders,ts,t) ->
                   (collect_binders binders;
                    FStar_List.iter (FStar_List.iter collect_term) ts;
                    collect_term t)
               | FStar_Parser_AST.Refine (binder,t) ->
                   (collect_binder binder; collect_term t)
               | FStar_Parser_AST.NamedTyp (uu____2542,t) -> collect_term t
               | FStar_Parser_AST.Paren t -> collect_term t
               | FStar_Parser_AST.Assign (uu____2545,t) -> collect_term t
               | FStar_Parser_AST.Requires (t,uu____2548) -> collect_term t
               | FStar_Parser_AST.Ensures (t,uu____2554) -> collect_term t
               | FStar_Parser_AST.Labeled (t,uu____2560,uu____2561) ->
                   collect_term t
               | FStar_Parser_AST.Attributes cattributes ->
                   FStar_List.iter collect_term cattributes
             and collect_patterns ps = FStar_List.iter collect_pattern ps
             and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
             and collect_pattern' uu___92_2569 =
               match uu___92_2569 with
               | FStar_Parser_AST.PatWild  -> ()
               | FStar_Parser_AST.PatOp uu____2570 -> ()
               | FStar_Parser_AST.PatConst uu____2571 -> ()
               | FStar_Parser_AST.PatApp (p,ps) ->
                   (collect_pattern p; collect_patterns ps)
               | FStar_Parser_AST.PatVar uu____2579 -> ()
               | FStar_Parser_AST.PatName uu____2586 -> ()
               | FStar_Parser_AST.PatTvar uu____2587 -> ()
               | FStar_Parser_AST.PatList ps -> collect_patterns ps
               | FStar_Parser_AST.PatOr ps -> collect_patterns ps
               | FStar_Parser_AST.PatTuple (ps,uu____2601) ->
                   collect_patterns ps
               | FStar_Parser_AST.PatRecord lidpats ->
                   FStar_List.iter
                     (fun uu____2620  ->
                        match uu____2620 with
                        | (uu____2625,p) -> collect_pattern p) lidpats
               | FStar_Parser_AST.PatAscribed (p,t) ->
                   (collect_pattern p; collect_term t)
             and collect_branches bs = FStar_List.iter collect_branch bs
             and collect_branch uu____2649 =
               match uu____2649 with
               | (pat,t1,t2) ->
                   (collect_pattern pat;
                    FStar_Util.iter_opt t1 collect_term;
                    collect_term t2) in
             let uu____2667 = FStar_Parser_Driver.parse_file filename in
             match uu____2667 with
             | (ast,uu____2681) -> (collect_file ast; FStar_ST.op_Bang deps))
let print_graph:
  'Auu____2731 .
    (Prims.string Prims.list,'Auu____2731) FStar_Pervasives_Native.tuple2
      FStar_Util.smap -> Prims.unit
  =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____2755 =
       let uu____2756 =
         let uu____2757 =
           let uu____2758 =
             let uu____2761 =
               let uu____2764 = FStar_Util.smap_keys graph in
               FStar_List.unique uu____2764 in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____2780 =
                      let uu____2787 = FStar_Util.smap_try_find graph k in
                      FStar_Util.must uu____2787 in
                    FStar_Pervasives_Native.fst uu____2780 in
                  let r s = FStar_Util.replace_char s '.' '_' in
                  FStar_List.map
                    (fun dep1  ->
                       FStar_Util.format2 "  %s -> %s" (r k) (r dep1)) deps)
               uu____2761 in
           FStar_String.concat "\n" uu____2758 in
         Prims.strcat uu____2757 "\n}\n" in
       Prims.strcat "digraph {\n" uu____2756 in
     FStar_Util.write_file "dep.graph" uu____2755)
let collect:
  verify_mode ->
    Prims.string Prims.list ->
      ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
         Prims.list,Prims.string Prims.list,(Prims.string Prims.list,
                                              color)
                                              FStar_Pervasives_Native.tuple2
                                              FStar_Util.smap)
        FStar_Pervasives_Native.tuple3
  =
  fun verify_mode  ->
    fun filenames  ->
      let graph = FStar_Util.smap_create (Prims.parse_int "41") in
      let verify_flags =
        let uu____2876 = FStar_Options.verify_module () in
        FStar_List.map
          (fun f  ->
             let uu____2888 = FStar_Util.mk_ref false in (f, uu____2888))
          uu____2876 in
      let partial_discovery =
        let uu____2908 =
          (FStar_Options.verify_all ()) || (FStar_Options.extract_all ()) in
        Prims.op_Negation uu____2908 in
      let m = build_map filenames in
      let file_names_of_key k =
        let uu____2914 =
          let uu____2923 = FStar_Util.smap_try_find m k in
          FStar_Util.must uu____2923 in
        match uu____2914 with
        | (intf,impl) ->
            (match (intf, impl) with
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "Impossible"
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some i)
                 -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.None )
                 -> i
             | (FStar_Pervasives_Native.Some i,uu____2979) when
                 partial_discovery -> i
             | (FStar_Pervasives_Native.Some i,FStar_Pervasives_Native.Some
                j) -> Prims.strcat i (Prims.strcat " && " j)) in
      let collect_one1 = collect_one verify_flags verify_mode in
      let rec discover_one is_user_provided_filename interface_only key =
        let uu____3011 =
          let uu____3012 = FStar_Util.smap_try_find graph key in
          uu____3012 = FStar_Pervasives_Native.None in
        if uu____3011
        then
          let uu____3041 =
            let uu____3050 = FStar_Util.smap_try_find m key in
            FStar_Util.must uu____3050 in
          match uu____3041 with
          | (intf,impl) ->
              let intf_deps =
                match intf with
                | FStar_Pervasives_Native.Some intf1 ->
                    collect_one1 is_user_provided_filename m intf1
                | FStar_Pervasives_Native.None  -> [] in
              let impl_deps =
                match (impl, intf) with
                | (FStar_Pervasives_Native.Some
                   impl1,FStar_Pervasives_Native.Some uu____3103) when
                    interface_only -> []
                | (FStar_Pervasives_Native.Some impl1,uu____3109) ->
                    collect_one1 is_user_provided_filename m impl1
                | (FStar_Pervasives_Native.None ,uu____3116) -> [] in
              let deps =
                FStar_List.unique (FStar_List.append impl_deps intf_deps) in
              (FStar_Util.smap_add graph key (deps, White);
               FStar_List.iter (discover_one false partial_discovery) deps)
        else () in
      let discover_command_line_argument f =
        let m1 = lowercase_module_name f in
        let interface_only =
          (is_interface f) &&
            (let uu____3143 =
               FStar_List.existsML
                 (fun f1  ->
                    (let uu____3148 = lowercase_module_name f1 in
                     uu____3148 = m1) && (is_implementation f1)) filenames in
             Prims.op_Negation uu____3143) in
        discover_one true interface_only m1 in
      FStar_List.iter discover_command_line_argument filenames;
      (let immediate_graph = FStar_Util.smap_copy graph in
       let topologically_sorted = FStar_Util.mk_ref [] in
       let rec discover cycle key =
         let uu____3185 =
           let uu____3192 = FStar_Util.smap_try_find graph key in
           FStar_Util.must uu____3192 in
         match uu____3185 with
         | (direct_deps,color) ->
             (match color with
              | Gray  ->
                  (FStar_Util.print1
                     "Warning: recursive dependency on module %s\n" key;
                   (let cycle1 =
                      FStar_All.pipe_right cycle
                        (FStar_List.map file_names_of_key) in
                    FStar_Util.print1
                      "The cycle contains a subset of the modules in:\n%s \n"
                      (FStar_String.concat "\n`used by` " cycle1);
                    print_graph immediate_graph;
                    FStar_Util.print_string "\n";
                    FStar_All.exit (Prims.parse_int "1")))
              | Black  -> direct_deps
              | White  ->
                  (FStar_Util.smap_add graph key (direct_deps, Gray);
                   (let all_deps =
                      let uu____3248 =
                        let uu____3251 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____3261 = discover (key :: cycle) dep1 in
                               dep1 :: uu____3261) direct_deps in
                        FStar_List.flatten uu____3251 in
                      FStar_List.unique uu____3248 in
                    FStar_Util.smap_add graph key (all_deps, Black);
                    (let uu____3274 =
                       let uu____3277 = FStar_ST.op_Bang topologically_sorted in
                       key :: uu____3277 in
                     FStar_ST.op_Colon_Equals topologically_sorted uu____3274);
                    all_deps))) in
       let discover1 = discover [] in
       let must_find k =
         let uu____3355 =
           let uu____3364 = FStar_Util.smap_try_find m k in
           FStar_Util.must uu____3364 in
         match uu____3355 with
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             (Prims.op_Negation partial_discovery) &&
               (let uu____3400 =
                  FStar_List.existsML
                    (fun f  ->
                       let uu____3404 = lowercase_module_name f in
                       uu____3404 = k) filenames in
                Prims.op_Negation uu____3400)
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,FStar_Pervasives_Native.Some
            impl) when
             FStar_List.existsML
               (fun f  ->
                  (is_implementation f) &&
                    (let uu____3414 = lowercase_module_name f in
                     uu____3414 = k)) filenames
             -> [intf; impl]
         | (FStar_Pervasives_Native.Some intf,uu____3416) -> [intf]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some impl)
             -> [impl]
         | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
             [] in
       let must_find_r f =
         let uu____3438 = must_find f in FStar_List.rev uu____3438 in
       let by_target =
         let uu____3450 =
           let uu____3453 = FStar_Util.smap_keys graph in
           FStar_List.sortWith (fun x  -> fun y  -> FStar_String.compare x y)
             uu____3453 in
         FStar_List.collect
           (fun k  ->
              let as_list = must_find k in
              let is_interleaved =
                (FStar_List.length as_list) = (Prims.parse_int "2") in
              FStar_List.map
                (fun f  ->
                   let should_append_fsti =
                     (is_implementation f) && is_interleaved in
                   let k1 = lowercase_module_name f in
                   let suffix =
                     let uu____3498 =
                       let uu____3507 = FStar_Util.smap_try_find m k1 in
                       FStar_Util.must uu____3507 in
                     match uu____3498 with
                     | (FStar_Pervasives_Native.Some intf,uu____3537) when
                         should_append_fsti -> [intf]
                     | uu____3544 -> [] in
                   let deps =
                     let uu____3556 = discover1 k1 in
                     FStar_List.rev uu____3556 in
                   let deps_as_filenames =
                     let uu____3562 = FStar_List.collect must_find deps in
                     FStar_List.append uu____3562 suffix in
                   (f, deps_as_filenames)) as_list) uu____3450 in
       let topologically_sorted1 =
         let uu____3570 = FStar_ST.op_Bang topologically_sorted in
         FStar_List.collect must_find_r uu____3570 in
       FStar_List.iter
         (fun uu____3674  ->
            match uu____3674 with
            | (m1,r) ->
                let uu____3855 =
                  (let uu____3858 = FStar_ST.op_Bang r in
                   Prims.op_Negation uu____3858) &&
                    (let uu____3966 = FStar_Options.interactive () in
                     Prims.op_Negation uu____3966) in
                if uu____3855
                then
                  let maybe_fst =
                    let k = FStar_String.length m1 in
                    let uu____3969 =
                      (k > (Prims.parse_int "4")) &&
                        (let uu____3977 =
                           FStar_String.substring m1
                             (k - (Prims.parse_int "4"))
                             (Prims.parse_int "4") in
                         uu____3977 = ".fst") in
                    if uu____3969
                    then
                      let uu____3984 =
                        FStar_String.substring m1 (Prims.parse_int "0")
                          (k - (Prims.parse_int "4")) in
                      FStar_Util.format1 " Did you mean %s ?" uu____3984
                    else "" in
                  let uu____3992 =
                    let uu____3993 =
                      FStar_Util.format3
                        "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n"
                        m1 m1 maybe_fst in
                    FStar_Errors.Err uu____3993 in
                  FStar_Exn.raise uu____3992
                else ()) verify_flags;
       (by_target, topologically_sorted1, immediate_graph))
let print_make:
  (Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.unit
  =
  fun deps  ->
    FStar_List.iter
      (fun uu____4043  ->
         match uu____4043 with
         | (f,deps1) ->
             let deps2 =
               FStar_List.map
                 (fun s  -> FStar_Util.replace_chars s ' ' "\\ ") deps1 in
             FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2))
      deps
let print:
  'a 'b .
    ((Prims.string,Prims.string Prims.list) FStar_Pervasives_Native.tuple2
       Prims.list,'a,(Prims.string Prims.list,'b)
                       FStar_Pervasives_Native.tuple2 FStar_Util.smap)
      FStar_Pervasives_Native.tuple3 -> Prims.unit
  =
  fun uu____4094  ->
    match uu____4094 with
    | (make_deps,uu____4118,graph) ->
        let uu____4152 = FStar_Options.dep () in
        (match uu____4152 with
         | FStar_Pervasives_Native.Some "make" -> print_make make_deps
         | FStar_Pervasives_Native.Some "graph" -> print_graph graph
         | FStar_Pervasives_Native.Some uu____4155 ->
             FStar_Exn.raise (FStar_Errors.Err "unknown tool for --dep\n")
         | FStar_Pervasives_Native.None  -> ())