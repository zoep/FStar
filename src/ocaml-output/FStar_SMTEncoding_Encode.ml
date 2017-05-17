open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___104_74  ->
       match uu___104_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___129_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___129_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___129_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____142
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____155 =
          let uu____156 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t in
              uu____163.FStar_Syntax_Syntax.n in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____193 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____200 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____200
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____207 =
        let uu____210 = mk_term_projector_name lid a in
        (uu____210,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____207
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____217 =
        let uu____220 = mk_term_projector_name_by_pos lid i in
        (uu____220,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____217
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____410 =
    let uu____411 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____411, uu____413) in
  let scopes =
    let uu____424 = let uu____430 = new_scope () in [uu____430] in
    FStar_Util.mk_ref uu____424 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____455 =
        let uu____457 = FStar_ST.read scopes in
        FStar_Util.find_map uu____457
          (fun uu____474  ->
             match uu____474 with
             | (names1,uu____481) -> FStar_Util.smap_try_find names1 y1) in
      match uu____455 with
      | None  -> y1
      | Some uu____486 ->
          (FStar_Util.incr ctr;
           (let uu____491 =
              let uu____492 =
                let uu____493 = FStar_ST.read ctr in
                Prims.string_of_int uu____493 in
              Prims.strcat "__" uu____492 in
            Prims.strcat y1 uu____491)) in
    let top_scope =
      let uu____498 =
        let uu____503 = FStar_ST.read scopes in FStar_List.hd uu____503 in
      FStar_All.pipe_left Prims.fst uu____498 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____542 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____553 =
      let uu____554 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____554 in
    FStar_Util.format2 "%s_%s" pfx uu____553 in
  let string_const s =
    let uu____559 =
      let uu____561 = FStar_ST.read scopes in
      FStar_Util.find_map uu____561
        (fun uu____578  ->
           match uu____578 with
           | (uu____584,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____559 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593 in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes in FStar_List.hd uu____601 in
          FStar_All.pipe_left Prims.snd uu____596 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____629 =
    let uu____630 =
      let uu____636 = new_scope () in
      let uu____641 = FStar_ST.read scopes in uu____636 :: uu____641 in
    FStar_ST.write scopes uu____630 in
  let pop1 uu____668 =
    let uu____669 =
      let uu____675 = FStar_ST.read scopes in FStar_List.tl uu____675 in
    FStar_ST.write scopes uu____669 in
  let mark1 uu____702 = push1 () in
  let reset_mark1 uu____706 = pop1 () in
  let commit_mark1 uu____710 =
    let uu____711 = FStar_ST.read scopes in
    match uu____711 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____771 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___130_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___130_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___130_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___105_1001  ->
            match uu___105_1001 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1004 -> [])) in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____1012 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___106_1016  ->
              match uu___106_1016 with
              | Binding_var (x,uu____1018) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1020,uu____1021,uu____1022) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1012 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____1055 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1055
      then
        let uu____1057 = FStar_Syntax_Print.term_to_string t in
        Some uu____1057
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1068 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1068)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___131_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___131_1080.tcenv);
           warn = (uu___131_1080.warn);
           cache = (uu___131_1080.cache);
           nolabels = (uu___131_1080.nolabels);
           use_zfuel_name = (uu___131_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___131_1080.encode_non_total_function_typ);
           current_module_name = (uu___131_1080.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___132_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___132_1093.depth);
           tcenv = (uu___132_1093.tcenv);
           warn = (uu___132_1093.warn);
           cache = (uu___132_1093.cache);
           nolabels = (uu___132_1093.nolabels);
           use_zfuel_name = (uu___132_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___132_1093.encode_non_total_function_typ);
           current_module_name = (uu___132_1093.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___133_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___133_1109.depth);
             tcenv = (uu___133_1109.tcenv);
             warn = (uu___133_1109.warn);
             cache = (uu___133_1109.cache);
             nolabels = (uu___133_1109.nolabels);
             use_zfuel_name = (uu___133_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___133_1109.encode_non_total_function_typ);
             current_module_name = (uu___133_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___134_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___134_1119.depth);
          tcenv = (uu___134_1119.tcenv);
          warn = (uu___134_1119.warn);
          cache = (uu___134_1119.cache);
          nolabels = (uu___134_1119.nolabels);
          use_zfuel_name = (uu___134_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___134_1119.encode_non_total_function_typ);
          current_module_name = (uu___134_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___107_1135  ->
             match uu___107_1135 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1143 -> None) in
      let uu____1146 = aux a in
      match uu____1146 with
      | None  ->
          let a2 = unmangle a in
          let uu____1153 = aux a2 in
          (match uu____1153 with
           | None  ->
               let uu____1159 =
                 let uu____1160 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1161 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1160 uu____1161 in
               failwith uu____1159
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1181 =
        let uu___135_1182 = env in
        let uu____1183 =
          let uu____1185 =
            let uu____1186 =
              let uu____1193 =
                let uu____1195 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1195 in
              (x, fname, uu____1193, None) in
            Binding_fvar uu____1186 in
          uu____1185 :: (env.bindings) in
        {
          bindings = uu____1183;
          depth = (uu___135_1182.depth);
          tcenv = (uu___135_1182.tcenv);
          warn = (uu___135_1182.warn);
          cache = (uu___135_1182.cache);
          nolabels = (uu___135_1182.nolabels);
          use_zfuel_name = (uu___135_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___135_1182.encode_non_total_function_typ);
          current_module_name = (uu___135_1182.current_module_name)
        } in
      (fname, ftok, uu____1181)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___108_1217  ->
           match uu___108_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___109_1253  ->
             match uu___109_1253 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1263 -> None) in
      FStar_All.pipe_right uu____1251 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1276 = try_lookup_lid env a in
      match uu____1276 with
      | None  ->
          let uu____1293 =
            let uu____1294 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1294 in
          failwith uu____1293
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___136_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___136_1325.depth);
            tcenv = (uu___136_1325.tcenv);
            warn = (uu___136_1325.warn);
            cache = (uu___136_1325.cache);
            nolabels = (uu___136_1325.nolabels);
            use_zfuel_name = (uu___136_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___136_1325.encode_non_total_function_typ);
            current_module_name = (uu___136_1325.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1337 = lookup_lid env x in
        match uu____1337 with
        | (t1,t2,uu____1345) ->
            let t3 =
              let uu____1351 =
                let uu____1355 =
                  let uu____1357 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1357] in
                (f, uu____1355) in
              FStar_SMTEncoding_Util.mkApp uu____1351 in
            let uu___137_1360 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___137_1360.depth);
              tcenv = (uu___137_1360.tcenv);
              warn = (uu___137_1360.warn);
              cache = (uu___137_1360.cache);
              nolabels = (uu___137_1360.nolabels);
              use_zfuel_name = (uu___137_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_1360.encode_non_total_function_typ);
              current_module_name = (uu___137_1360.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1370 = try_lookup_lid env l in
      match uu____1370 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1397 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1402,fuel::[]) ->
                         let uu____1405 =
                           let uu____1406 =
                             let uu____1407 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1407 Prims.fst in
                           FStar_Util.starts_with uu____1406 "fuel" in
                         if uu____1405
                         then
                           let uu____1409 =
                             let uu____1410 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1410
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1409
                         else Some t
                     | uu____1413 -> Some t)
                | uu____1414 -> None))
let lookup_free_var env a =
  let uu____1432 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1432 with
  | Some t -> t
  | None  ->
      let uu____1435 =
        let uu____1436 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1436 in
      failwith uu____1435
let lookup_free_var_name env a =
  let uu____1453 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1453 with | (x,uu____1460,uu____1461) -> x
let lookup_free_var_sym env a =
  let uu____1485 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1485 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1506;
             FStar_SMTEncoding_Term.rng = uu____1507;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1515 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1529 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___110_1538  ->
           match uu___110_1538 with
           | Binding_fvar (uu____1540,nm',tok,uu____1543) when nm = nm' ->
               tok
           | uu____1548 -> None)
let mkForall_fuel' n1 uu____1565 =
  match uu____1565 with
  | (pats,vars,body) ->
      let fallback uu____1581 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1584 = FStar_Options.unthrottle_inductives () in
      if uu____1584
      then fallback ()
      else
        (let uu____1586 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1586 with
         | (fsym,fterm) ->
             let add_fuel1 tms =
               FStar_All.pipe_right tms
                 (FStar_List.map
                    (fun p  ->
                       match p.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Var "HasType",args) ->
                           FStar_SMTEncoding_Util.mkApp
                             ("HasTypeFuel", (fterm :: args))
                       | uu____1605 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1619 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1619
                     | uu____1621 ->
                         let uu____1622 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1622 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1625 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow _
        |FStar_Syntax_Syntax.Tm_refine _
         |FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_abs _|FStar_Syntax_Syntax.Tm_constant _
          -> true
      | FStar_Syntax_Syntax.Tm_fvar fv|FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
           FStar_Syntax_Syntax.vars = _;_},_)
          ->
          let uu____1669 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1669 FStar_Option.isNone
      | uu____1682 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1689 =
        let uu____1690 = FStar_Syntax_Util.un_uinst t in
        uu____1690.FStar_Syntax_Syntax.n in
      match uu____1689 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1693,uu____1694,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___111_1723  ->
                  match uu___111_1723 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1724 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1725,uu____1726,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1753 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1753 FStar_Option.isSome
      | uu____1766 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1773 = head_normal env t in
      if uu____1773
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____1784 =
      let uu____1785 = FStar_Syntax_Syntax.null_binder t in [uu____1785] in
    let uu____1786 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1784 uu____1786 None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match Prims.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1813 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1813
                | s ->
                    let uu____1816 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1816) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___112_1828  ->
    match uu___112_1828 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1829 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1857;
                       FStar_SMTEncoding_Term.rng = uu____1858;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1872) ->
              let uu____1877 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1887 -> false) args (FStar_List.rev xs)) in
              if uu____1877 then tok_of_name env f else None
          | (uu____1890,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1893 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1895 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1895)) in
              if uu____1893 then Some t else None
          | uu____1898 -> None in
        check_partial_applications body (FStar_List.rev vars)
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____1982 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___113_1985  ->
    match uu___113_1985 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1987 =
          let uu____1991 =
            let uu____1993 =
              let uu____1994 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1994 in
            [uu____1993] in
          ("FStar.Char.Char", uu____1991) in
        FStar_SMTEncoding_Util.mkApp uu____1987
    | FStar_Const.Const_int (i,None ) ->
        let uu____2002 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2002
    | FStar_Const.Const_int (i,Some uu____2004) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2013) ->
        let uu____2016 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2016
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2020 =
          let uu____2021 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2021 in
        failwith uu____2020
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____2040 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2048 ->
            let uu____2053 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2053
        | uu____2054 ->
            if norm1
            then let uu____2055 = whnf env t1 in aux false uu____2055
            else
              (let uu____2057 =
                 let uu____2058 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2059 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2058 uu____2059 in
               failwith uu____2057) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2080 ->
        let uu____2081 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2081)
let rec encode_binders:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2224 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2224
         then
           let uu____2225 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2225
         else ());
        (let uu____2227 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2263  ->
                   fun b  ->
                     match uu____2263 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2306 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2315 = gen_term_var env1 x in
                           match uu____2315 with
                           | (xxsym,xx,env') ->
                               let uu____2329 =
                                 let uu____2332 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2332 env1 xx in
                               (match uu____2329 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2306 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2227 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2420 = encode_term t env in
          match uu____2420 with
          | (t1,decls) ->
              let uu____2427 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2427, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2435 = encode_term t env in
          match uu____2435 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2444 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2444, decls)
               | Some f ->
                   let uu____2446 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2446, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2453 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2453
       then
         let uu____2454 = FStar_Syntax_Print.tag_of_term t in
         let uu____2455 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2456 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2454 uu____2455
           uu____2456
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2461 =
             let uu____2462 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2463 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2464 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2465 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2462
               uu____2463 uu____2464 uu____2465 in
           failwith uu____2461
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2469 =
             let uu____2470 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2470 in
           failwith uu____2469
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2475) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2505) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2514 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2514, [])
       | FStar_Syntax_Syntax.Tm_type uu____2520 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2523) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2529 = encode_const c in (uu____2529, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2544 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2544 with
            | (binders1,res) ->
                let uu____2551 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2551
                then
                  let uu____2554 = encode_binders None binders1 env in
                  (match uu____2554 with
                   | (vars,guards,env',decls,uu____2569) ->
                       let fsym =
                         let uu____2579 = varops.fresh "f" in
                         (uu____2579, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2582 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___138_2586 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___138_2586.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___138_2586.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___138_2586.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___138_2586.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___138_2586.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___138_2586.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___138_2586.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___138_2586.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___138_2586.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___138_2586.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___138_2586.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___138_2586.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___138_2586.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___138_2586.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___138_2586.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___138_2586.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___138_2586.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___138_2586.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___138_2586.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___138_2586.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___138_2586.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___138_2586.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___138_2586.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2582 with
                        | (pre_opt,res_t) ->
                            let uu____2593 =
                              encode_term_pred None res_t env' app in
                            (match uu____2593 with
                             | (res_pred,decls') ->
                                 let uu____2600 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2607 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2607, [])
                                   | Some pre ->
                                       let uu____2610 =
                                         encode_formula pre env' in
                                       (match uu____2610 with
                                        | (guard,decls0) ->
                                            let uu____2618 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2618, decls0)) in
                                 (match uu____2600 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2626 =
                                          let uu____2632 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2632) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2626 in
                                      let cvars =
                                        let uu____2642 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2642
                                          (FStar_List.filter
                                             (fun uu____2648  ->
                                                match uu____2648 with
                                                | (x,uu____2652) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2663 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2663 with
                                       | Some cache_entry ->
                                           let uu____2668 =
                                             let uu____2669 =
                                               let uu____2673 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2673) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2669 in
                                           (uu____2668,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2684 =
                                               let uu____2685 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2685 in
                                             varops.mk_unique uu____2684 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2692 =
                                               FStar_Options.log_queries () in
                                             if uu____2692
                                             then
                                               let uu____2694 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2694
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2700 =
                                               let uu____2704 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2704) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2700 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2712 =
                                               let uu____2716 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2716, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2712 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____2729 =
                                               let uu____2733 =
                                                 let uu____2734 =
                                                   let uu____2740 =
                                                     let uu____2741 =
                                                       let uu____2744 =
                                                         let uu____2745 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2745 in
                                                       (f_has_t, uu____2744) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2741 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2740) in
                                                 mkForall_fuel uu____2734 in
                                               (uu____2733,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2729 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2758 =
                                               let uu____2762 =
                                                 let uu____2763 =
                                                   let uu____2769 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2769) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2763 in
                                               (uu____2762, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2758 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2783 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2783);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____2794 =
                       let uu____2798 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2798, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2794 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2807 =
                       let uu____2811 =
                         let uu____2812 =
                           let uu____2818 =
                             let uu____2819 =
                               let uu____2822 =
                                 let uu____2823 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2823 in
                               (f_has_t, uu____2822) in
                             FStar_SMTEncoding_Util.mkImp uu____2819 in
                           ([[f_has_t]], [fsym], uu____2818) in
                         mkForall_fuel uu____2812 in
                       (uu____2811, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2807 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2837 ->
           let uu____2842 =
             let uu____2845 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2845 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2850;
                 FStar_Syntax_Syntax.pos = uu____2851;
                 FStar_Syntax_Syntax.vars = uu____2852;_} ->
                 let uu____2859 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2859 with
                  | (b,f1) ->
                      let uu____2873 =
                        let uu____2874 = FStar_List.hd b in
                        Prims.fst uu____2874 in
                      (uu____2873, f1))
             | uu____2879 -> failwith "impossible" in
           (match uu____2842 with
            | (x,f) ->
                let uu____2886 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2886 with
                 | (base_t,decls) ->
                     let uu____2893 = gen_term_var env x in
                     (match uu____2893 with
                      | (x1,xtm,env') ->
                          let uu____2902 = encode_formula f env' in
                          (match uu____2902 with
                           | (refinement,decls') ->
                               let uu____2909 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2909 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2920 =
                                        let uu____2922 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2926 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2922
                                          uu____2926 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2920 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2942  ->
                                              match uu____2942 with
                                              | (y,uu____2946) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____2965 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2965 with
                                     | Some cache_entry ->
                                         let uu____2970 =
                                           let uu____2971 =
                                             let uu____2975 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2975) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2971 in
                                         (uu____2970,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2987 =
                                             let uu____2988 =
                                               let uu____2989 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2989 in
                                             Prims.strcat module_name
                                               uu____2988 in
                                           varops.mk_unique uu____2987 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2998 =
                                             let uu____3002 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3002) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2998 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____3013 =
                                             let uu____3017 =
                                               let uu____3018 =
                                                 let uu____3024 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3024) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3018 in
                                             (uu____3017,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3013 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3039 =
                                             let uu____3043 =
                                               let uu____3044 =
                                                 let uu____3050 =
                                                   let uu____3051 =
                                                     let uu____3054 =
                                                       let uu____3055 =
                                                         let uu____3061 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3061) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3055 in
                                                     (uu____3054, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3051 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3050) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3044 in
                                             (uu____3043,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3039 in
                                         let t_kinding =
                                           let uu____3081 =
                                             let uu____3085 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3085,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3081 in
                                         let t_interp =
                                           let uu____3095 =
                                             let uu____3099 =
                                               let uu____3100 =
                                                 let uu____3106 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3106) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3100 in
                                             let uu____3118 =
                                               let uu____3120 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3120 in
                                             (uu____3099, uu____3118,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3095 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3125 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3125);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3142 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3142 in
           let uu____3146 = encode_term_pred None k env ttm in
           (match uu____3146 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3154 =
                    let uu____3158 =
                      let uu____3159 =
                        let uu____3160 =
                          let uu____3161 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3161 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3160 in
                      varops.mk_unique uu____3159 in
                    (t_has_k, (Some "Uvar typing"), uu____3158) in
                  FStar_SMTEncoding_Util.mkAssume uu____3154 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3167 ->
           let uu____3177 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3177 with
            | (head1,args_e) ->
                let uu____3205 =
                  let uu____3213 =
                    let uu____3214 = FStar_Syntax_Subst.compress head1 in
                    uu____3214.FStar_Syntax_Syntax.n in
                  (uu____3213, args_e) in
                (match uu____3205 with
                 | (uu____3224,uu____3225) when head_redex env head1 ->
                     let uu____3236 = whnf env t in
                     encode_term uu____3236 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_),_::(v1,_)::
                    (v2,_)::[])
                   |(FStar_Syntax_Syntax.Tm_fvar fv,_::(v1,_)::(v2,_)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3310 = encode_term v1 env in
                     (match uu____3310 with
                      | (v11,decls1) ->
                          let uu____3317 = encode_term v2 env in
                          (match uu____3317 with
                           | (v21,decls2) ->
                               let uu____3324 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3324,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3326) ->
                     let e0 =
                       let uu____3338 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3338 in
                     ((let uu____3344 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3344
                       then
                         let uu____3345 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3345
                       else ());
                      (let e =
                         let uu____3350 =
                           let uu____3351 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3352 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3351
                             uu____3352 in
                         uu____3350 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3361),(arg,uu____3363)::[]) -> encode_term arg env
                 | uu____3381 ->
                     let uu____3389 = encode_args args_e env in
                     (match uu____3389 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3422 = encode_term head1 env in
                            match uu____3422 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3461 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3461 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3503  ->
                                                 fun uu____3504  ->
                                                   match (uu____3503,
                                                           uu____3504)
                                                   with
                                                   | ((bv,uu____3518),
                                                      (a,uu____3520)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3534 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3534
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3539 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3539 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3549 =
                                                   let uu____3553 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3558 =
                                                     let uu____3559 =
                                                       let uu____3560 =
                                                         let uu____3561 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3561 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3560 in
                                                     varops.mk_unique
                                                       uu____3559 in
                                                   (uu____3553,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3558) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3549 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3578 = lookup_free_var_sym env fv in
                            match uu____3578 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_name x;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____3616 =
                                  let uu____3617 =
                                    let uu____3620 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3620 Prims.fst in
                                  FStar_All.pipe_right uu____3617 Prims.snd in
                                Some uu____3616
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3639,(FStar_Util.Inl t1,uu____3641),uu____3642)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3680,(FStar_Util.Inr c,uu____3682),uu____3683)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3721 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3741 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3741 in
                               let uu____3742 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3742 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                       ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = _;
                                          FStar_Syntax_Syntax.pos = _;
                                          FStar_Syntax_Syntax.vars = _;_},_)
                                       |FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____3767 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3812 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3812 with
            | (bs1,body1,opening) ->
                let fallback uu____3827 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3832 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3832, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3843 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3843
                  | FStar_Util.Inr (eff,uu____3845) ->
                      let uu____3851 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3851 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3896 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___139_3897 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___139_3897.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___139_3897.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___139_3897.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___139_3897.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___139_3897.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___139_3897.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___139_3897.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___139_3897.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___139_3897.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___139_3897.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___139_3897.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___139_3897.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___139_3897.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___139_3897.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___139_3897.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___139_3897.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___139_3897.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___139_3897.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___139_3897.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___139_3897.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___139_3897.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___139_3897.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___139_3897.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3896 FStar_Syntax_Syntax.U_unknown in
                        let uu____3898 =
                          let uu____3899 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3899 in
                        FStar_Util.Inl uu____3898
                    | FStar_Util.Inr (eff_name,uu____3906) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3937 =
                        let uu____3938 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3938 in
                      FStar_All.pipe_right uu____3937
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3950 =
                        let uu____3951 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3951 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3959 =
                          let uu____3960 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____3960 in
                        FStar_All.pipe_right uu____3959
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3964 =
                             let uu____3965 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____3965 in
                           FStar_All.pipe_right uu____3964
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____3976 =
                         let uu____3977 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____3977 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3976);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____3992 =
                       (is_impure lc1) &&
                         (let uu____3993 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____3993) in
                     if uu____3992
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____3998 = encode_binders None bs1 env in
                        match uu____3998 with
                        | (vars,guards,envbody,decls,uu____4013) ->
                            let uu____4020 =
                              let uu____4028 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4028
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4020 with
                             | (lc2,body2) ->
                                 let uu____4053 = encode_term body2 envbody in
                                 (match uu____4053 with
                                  | (body3,decls') ->
                                      let uu____4060 =
                                        let uu____4065 = codomain_eff lc2 in
                                        match uu____4065 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4077 =
                                              encode_term tfun env in
                                            (match uu____4077 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4060 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4096 =
                                               let uu____4102 =
                                                 let uu____4103 =
                                                   let uu____4106 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4106, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4103 in
                                               ([], vars, uu____4102) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4096 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4114 =
                                                   let uu____4116 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4116 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4114 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4127 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4127 with
                                            | Some cache_entry ->
                                                let uu____4132 =
                                                  let uu____4133 =
                                                    let uu____4137 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4137) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4133 in
                                                (uu____4132,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4143 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4143 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4150 =
                                                         let uu____4151 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4151 =
                                                           cache_size in
                                                       if uu____4150
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls decls' in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4162 =
                                                           let uu____4163 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4163 in
                                                         varops.mk_unique
                                                           uu____4162 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____4168 =
                                                         let uu____4172 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4172) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4168 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4184 =
                                                             let uu____4185 =
                                                               let uu____4189
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4189,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4185 in
                                                           [uu____4184] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4197 =
                                                         let uu____4201 =
                                                           let uu____4202 =
                                                             let uu____4208 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4208) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4202 in
                                                         (uu____4201,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4197 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     ((let uu____4218 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4218);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4220,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4221;
                          FStar_Syntax_Syntax.lbunivs = uu____4222;
                          FStar_Syntax_Syntax.lbtyp = uu____4223;
                          FStar_Syntax_Syntax.lbeff = uu____4224;
                          FStar_Syntax_Syntax.lbdef = uu____4225;_}::uu____4226),uu____4227)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4245;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4247;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4263 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4276 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4276, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4318 = encode_term e1 env in
              match uu____4318 with
              | (ee1,decls1) ->
                  let uu____4325 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4325 with
                   | (xs,e21) ->
                       let uu____4339 = FStar_List.hd xs in
                       (match uu____4339 with
                        | (x1,uu____4347) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4349 = encode_body e21 env' in
                            (match uu____4349 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4371 =
              let uu____4375 =
                let uu____4376 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4376 in
              gen_term_var env uu____4375 in
            match uu____4371 with
            | (scrsym,scr',env1) ->
                let uu____4390 = encode_term e env1 in
                (match uu____4390 with
                 | (scr,decls) ->
                     let uu____4397 =
                       let encode_branch b uu____4413 =
                         match uu____4413 with
                         | (else_case,decls1) ->
                             let uu____4424 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4424 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4454  ->
                                       fun uu____4455  ->
                                         match (uu____4454, uu____4455) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr' in
                                             let projections =
                                               pattern.projections scr' in
                                             let env2 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4492  ->
                                                         match uu____4492
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4497 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4512 =
                                                     encode_term w1 env2 in
                                                   (match uu____4512 with
                                                    | (w2,decls21) ->
                                                        let uu____4520 =
                                                          let uu____4521 =
                                                            let uu____4524 =
                                                              let uu____4525
                                                                =
                                                                let uu____4528
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4528) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4525 in
                                                            (guard,
                                                              uu____4524) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4521 in
                                                        (uu____4520, decls21)) in
                                             (match uu____4497 with
                                              | (guard1,decls21) ->
                                                  let uu____4536 =
                                                    encode_br br env2 in
                                                  (match uu____4536 with
                                                   | (br1,decls3) ->
                                                       let uu____4544 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4544,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4397 with
                      | (match_tm,decls1) ->
                          let uu____4556 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4556, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4587 -> let uu____4588 = encode_one_pat env pat in [uu____4588]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4600 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4600
       then
         let uu____4601 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4601
       else ());
      (let uu____4603 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4603 with
       | (vars,pat_term) ->
           let uu____4613 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4636  ->
                     fun v1  ->
                       match uu____4636 with
                       | (env1,vars1) ->
                           let uu____4664 = gen_term_var env1 v1 in
                           (match uu____4664 with
                            | (xx,uu____4676,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4613 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4723 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4731 =
                        let uu____4734 = encode_const c in
                        (scrutinee, uu____4734) in
                      FStar_SMTEncoding_Util.mkEq uu____4731
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4753 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4753 with
                        | (uu____4757,uu____4758::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4760 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4781  ->
                                  match uu____4781 with
                                  | (arg,uu____4787) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4797 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4797)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4816 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4831 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4846 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4868  ->
                                  match uu____4868 with
                                  | (arg,uu____4877) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4887 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4887)) in
                      FStar_All.pipe_right uu____4846 FStar_List.flatten in
                let pat_term1 uu____4903 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____4910 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4925  ->
                fun uu____4926  ->
                  match (uu____4925, uu____4926) with
                  | ((tms,decls),(t,uu____4946)) ->
                      let uu____4957 = encode_term t env in
                      (match uu____4957 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4910 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____4995 = FStar_Syntax_Util.list_elements e in
            match uu____4995 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5013 =
              let uu____5023 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5023 FStar_Syntax_Util.head_and_args in
            match uu____5013 with
            | (head1,args) ->
                let uu____5054 =
                  let uu____5062 =
                    let uu____5063 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5063.FStar_Syntax_Syntax.n in
                  (uu____5062, args) in
                (match uu____5054 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5077,uu____5078)::(e,uu____5080)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5111)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5132 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5165 =
                let uu____5175 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5175
                  FStar_Syntax_Util.head_and_args in
              match uu____5165 with
              | (head1,args) ->
                  let uu____5204 =
                    let uu____5212 =
                      let uu____5213 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5213.FStar_Syntax_Syntax.n in
                    (uu____5212, args) in
                  (match uu____5204 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5226)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5246 -> None) in
            match elts with
            | t1::[] ->
                let uu____5264 = smt_pat_or t1 in
                (match uu____5264 with
                 | Some e ->
                     let uu____5280 = list_elements1 e in
                     FStar_All.pipe_right uu____5280
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5297 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5297
                               (FStar_List.map one_pat)))
                 | uu____5311 ->
                     let uu____5315 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5315])
            | uu____5346 ->
                let uu____5348 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5348] in
          let uu____5379 =
            let uu____5395 =
              let uu____5396 = FStar_Syntax_Subst.compress t in
              uu____5396.FStar_Syntax_Syntax.n in
            match uu____5395 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5426 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5426 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5461;
                            FStar_Syntax_Syntax.effect_name = uu____5462;
                            FStar_Syntax_Syntax.result_typ = uu____5463;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5465)::(post,uu____5467)::(pats,uu____5469)::[];
                            FStar_Syntax_Syntax.flags = uu____5470;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5504 = lemma_pats pats' in
                          (binders1, pre, post, uu____5504)
                      | uu____5523 -> failwith "impos"))
            | uu____5539 -> failwith "Impos" in
          match uu____5379 with
          | (binders,pre,post,patterns) ->
              let uu____5583 = encode_binders None binders env in
              (match uu____5583 with
               | (vars,guards,env1,decls,uu____5598) ->
                   let uu____5605 =
                     let uu____5612 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5643 =
                                 let uu____5648 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5664  ->
                                           match uu____5664 with
                                           | (t1,uu____5671) ->
                                               encode_term t1
                                                 (let uu___140_5674 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___140_5674.bindings);
                                                    depth =
                                                      (uu___140_5674.depth);
                                                    tcenv =
                                                      (uu___140_5674.tcenv);
                                                    warn =
                                                      (uu___140_5674.warn);
                                                    cache =
                                                      (uu___140_5674.cache);
                                                    nolabels =
                                                      (uu___140_5674.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___140_5674.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___140_5674.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5648
                                   FStar_List.unzip in
                               match uu____5643 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5612 FStar_List.unzip in
                   (match uu____5605 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls' in
                        let pats1 =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5738 =
                                             let uu____5739 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5739 e in
                                           uu____5738 :: p))
                               | uu____5740 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5769 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5769 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5777 =
                                           let uu____5778 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5778 tl1 in
                                         aux uu____5777 vars2
                                     | uu____5779 -> pats in
                                   let uu____5783 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5783 vars) in
                        let env2 =
                          let uu___141_5785 = env1 in
                          {
                            bindings = (uu___141_5785.bindings);
                            depth = (uu___141_5785.depth);
                            tcenv = (uu___141_5785.tcenv);
                            warn = (uu___141_5785.warn);
                            cache = (uu___141_5785.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___141_5785.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___141_5785.encode_non_total_function_typ);
                            current_module_name =
                              (uu___141_5785.current_module_name)
                          } in
                        let uu____5786 =
                          let uu____5789 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5789 env2 in
                        (match uu____5786 with
                         | (pre1,decls'') ->
                             let uu____5794 =
                               let uu____5797 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5797 env2 in
                             (match uu____5794 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5804 =
                                    let uu____5805 =
                                      let uu____5811 =
                                        let uu____5812 =
                                          let uu____5815 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5815, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5812 in
                                      (pats1, vars, uu____5811) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5805 in
                                  (uu____5804, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5828 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5828
        then
          let uu____5829 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5830 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5829 uu____5830
        else () in
      let enc f r l =
        let uu____5857 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5870 = encode_term (Prims.fst x) env in
                 match uu____5870 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5857 with
        | (decls,args) ->
            let uu____5887 =
              let uu___142_5888 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___142_5888.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___142_5888.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5887, decls) in
      let const_op f r uu____5907 = let uu____5910 = f r in (uu____5910, []) in
      let un_op f l =
        let uu____5926 = FStar_List.hd l in FStar_All.pipe_left f uu____5926 in
      let bin_op f uu___114_5939 =
        match uu___114_5939 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5947 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5974 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5983  ->
                 match uu____5983 with
                 | (t,uu____5991) ->
                     let uu____5992 = encode_formula t env in
                     (match uu____5992 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5974 with
        | (decls,phis) ->
            let uu____6009 =
              let uu___143_6010 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_6010.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_6010.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6009, decls) in
      let eq_op r uu___115_6026 =
        match uu___115_6026 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6086 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6086 r [e1; e2]
        | l ->
            let uu____6106 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6106 r l in
      let mk_imp1 r uu___116_6125 =
        match uu___116_6125 with
        | (lhs,uu____6129)::(rhs,uu____6131)::[] ->
            let uu____6152 = encode_formula rhs env in
            (match uu____6152 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6161) ->
                      (l1, decls1)
                  | uu____6164 ->
                      let uu____6165 = encode_formula lhs env in
                      (match uu____6165 with
                       | (l2,decls2) ->
                           let uu____6172 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6172, (FStar_List.append decls1 decls2)))))
        | uu____6174 -> failwith "impossible" in
      let mk_ite r uu___117_6189 =
        match uu___117_6189 with
        | (guard,uu____6193)::(_then,uu____6195)::(_else,uu____6197)::[] ->
            let uu____6226 = encode_formula guard env in
            (match uu____6226 with
             | (g,decls1) ->
                 let uu____6233 = encode_formula _then env in
                 (match uu____6233 with
                  | (t,decls2) ->
                      let uu____6240 = encode_formula _else env in
                      (match uu____6240 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6249 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6268 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6268 in
      let connectives =
        let uu____6280 =
          let uu____6289 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6289) in
        let uu____6302 =
          let uu____6312 =
            let uu____6321 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6321) in
          let uu____6334 =
            let uu____6344 =
              let uu____6354 =
                let uu____6363 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6363) in
              let uu____6376 =
                let uu____6386 =
                  let uu____6396 =
                    let uu____6405 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6405) in
                  [uu____6396;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6386 in
              uu____6354 :: uu____6376 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6344 in
          uu____6312 :: uu____6334 in
        uu____6280 :: uu____6302 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6567 = encode_formula phi' env in
            (match uu____6567 with
             | (phi2,decls) ->
                 let uu____6574 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6574, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6575 ->
            let uu____6580 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6580 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6609 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6609 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6617;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6619;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6635 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6635 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6667::(x,uu____6669)::(t,uu____6671)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6705 = encode_term x env in
                 (match uu____6705 with
                  | (x1,decls) ->
                      let uu____6712 = encode_term t env in
                      (match uu____6712 with
                       | (t1,decls') ->
                           let uu____6719 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6719, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6723)::(msg,uu____6725)::(phi2,uu____6727)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6761 =
                   let uu____6764 =
                     let uu____6765 = FStar_Syntax_Subst.compress r in
                     uu____6765.FStar_Syntax_Syntax.n in
                   let uu____6768 =
                     let uu____6769 = FStar_Syntax_Subst.compress msg in
                     uu____6769.FStar_Syntax_Syntax.n in
                   (uu____6764, uu____6768) in
                 (match uu____6761 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6776))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6792 -> fallback phi2)
             | uu____6795 when head_redex env head2 ->
                 let uu____6803 = whnf env phi1 in
                 encode_formula uu____6803 env
             | uu____6804 ->
                 let uu____6812 = encode_term phi1 env in
                 (match uu____6812 with
                  | (tt,decls) ->
                      let uu____6819 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___144_6820 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___144_6820.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___144_6820.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6819, decls)))
        | uu____6823 ->
            let uu____6824 = encode_term phi1 env in
            (match uu____6824 with
             | (tt,decls) ->
                 let uu____6831 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___145_6832 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___145_6832.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___145_6832.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6831, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6859 = encode_binders None bs env1 in
        match uu____6859 with
        | (vars,guards,env2,decls,uu____6881) ->
            let uu____6888 =
              let uu____6895 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6918 =
                          let uu____6923 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6937  ->
                                    match uu____6937 with
                                    | (t,uu____6943) ->
                                        encode_term t
                                          (let uu___146_6944 = env2 in
                                           {
                                             bindings =
                                               (uu___146_6944.bindings);
                                             depth = (uu___146_6944.depth);
                                             tcenv = (uu___146_6944.tcenv);
                                             warn = (uu___146_6944.warn);
                                             cache = (uu___146_6944.cache);
                                             nolabels =
                                               (uu___146_6944.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___146_6944.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___146_6944.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6923 FStar_List.unzip in
                        match uu____6918 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6895 FStar_List.unzip in
            (match uu____6888 with
             | (pats,decls') ->
                 let uu____6996 = encode_formula body env2 in
                 (match uu____6996 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7015;
                             FStar_SMTEncoding_Term.rng = uu____7016;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7024 -> guards in
                      let uu____7027 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7027, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7061  ->
                   match uu____7061 with
                   | (x,uu____7065) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7071 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7077 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7077) uu____7071 tl1 in
             let uu____7079 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7091  ->
                       match uu____7091 with
                       | (b,uu____7095) ->
                           let uu____7096 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7096)) in
             (match uu____7079 with
              | None  -> ()
              | Some (x,uu____7100) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7110 =
                    let uu____7111 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7111 in
                  FStar_Errors.warn pos uu____7110) in
       let uu____7112 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7112 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7118 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7154  ->
                     match uu____7154 with
                     | (l,uu____7164) -> FStar_Ident.lid_equals op l)) in
           (match uu____7118 with
            | None  -> fallback phi1
            | Some (uu____7187,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7216 = encode_q_body env vars pats body in
             match uu____7216 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7242 =
                     let uu____7248 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7248) in
                   FStar_SMTEncoding_Term.mkForall uu____7242
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7260 = encode_q_body env vars pats body in
             match uu____7260 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7285 =
                   let uu____7286 =
                     let uu____7292 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7292) in
                   FStar_SMTEncoding_Term.mkExists uu____7286
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7285, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7341 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7341 with
  | (asym,a) ->
      let uu____7346 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7346 with
       | (xsym,x) ->
           let uu____7351 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7351 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7381 =
                      let uu____7387 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7387, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7381 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7402 =
                      let uu____7406 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7406) in
                    FStar_SMTEncoding_Util.mkApp uu____7402 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7414 =
                    let uu____7416 =
                      let uu____7418 =
                        let uu____7420 =
                          let uu____7421 =
                            let uu____7425 =
                              let uu____7426 =
                                let uu____7432 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7432) in
                              FStar_SMTEncoding_Util.mkForall uu____7426 in
                            (uu____7425, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7421 in
                        let uu____7441 =
                          let uu____7443 =
                            let uu____7444 =
                              let uu____7448 =
                                let uu____7449 =
                                  let uu____7455 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7455) in
                                FStar_SMTEncoding_Util.mkForall uu____7449 in
                              (uu____7448,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7444 in
                          [uu____7443] in
                        uu____7420 :: uu____7441 in
                      xtok_decl :: uu____7418 in
                    xname_decl :: uu____7416 in
                  (xtok1, uu____7414) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7504 =
                    let uu____7512 =
                      let uu____7518 =
                        let uu____7519 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7519 in
                      quant axy uu____7518 in
                    (FStar_Syntax_Const.op_Eq, uu____7512) in
                  let uu____7525 =
                    let uu____7534 =
                      let uu____7542 =
                        let uu____7548 =
                          let uu____7549 =
                            let uu____7550 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7550 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7549 in
                        quant axy uu____7548 in
                      (FStar_Syntax_Const.op_notEq, uu____7542) in
                    let uu____7556 =
                      let uu____7565 =
                        let uu____7573 =
                          let uu____7579 =
                            let uu____7580 =
                              let uu____7581 =
                                let uu____7584 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7585 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7584, uu____7585) in
                              FStar_SMTEncoding_Util.mkLT uu____7581 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7580 in
                          quant xy uu____7579 in
                        (FStar_Syntax_Const.op_LT, uu____7573) in
                      let uu____7591 =
                        let uu____7600 =
                          let uu____7608 =
                            let uu____7614 =
                              let uu____7615 =
                                let uu____7616 =
                                  let uu____7619 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7620 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7619, uu____7620) in
                                FStar_SMTEncoding_Util.mkLTE uu____7616 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7615 in
                            quant xy uu____7614 in
                          (FStar_Syntax_Const.op_LTE, uu____7608) in
                        let uu____7626 =
                          let uu____7635 =
                            let uu____7643 =
                              let uu____7649 =
                                let uu____7650 =
                                  let uu____7651 =
                                    let uu____7654 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7655 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7654, uu____7655) in
                                  FStar_SMTEncoding_Util.mkGT uu____7651 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7650 in
                              quant xy uu____7649 in
                            (FStar_Syntax_Const.op_GT, uu____7643) in
                          let uu____7661 =
                            let uu____7670 =
                              let uu____7678 =
                                let uu____7684 =
                                  let uu____7685 =
                                    let uu____7686 =
                                      let uu____7689 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7690 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7689, uu____7690) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7686 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7685 in
                                quant xy uu____7684 in
                              (FStar_Syntax_Const.op_GTE, uu____7678) in
                            let uu____7696 =
                              let uu____7705 =
                                let uu____7713 =
                                  let uu____7719 =
                                    let uu____7720 =
                                      let uu____7721 =
                                        let uu____7724 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7725 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7724, uu____7725) in
                                      FStar_SMTEncoding_Util.mkSub uu____7721 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7720 in
                                  quant xy uu____7719 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7713) in
                              let uu____7731 =
                                let uu____7740 =
                                  let uu____7748 =
                                    let uu____7754 =
                                      let uu____7755 =
                                        let uu____7756 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7756 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7755 in
                                    quant qx uu____7754 in
                                  (FStar_Syntax_Const.op_Minus, uu____7748) in
                                let uu____7762 =
                                  let uu____7771 =
                                    let uu____7779 =
                                      let uu____7785 =
                                        let uu____7786 =
                                          let uu____7787 =
                                            let uu____7790 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7791 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7790, uu____7791) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7787 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7786 in
                                      quant xy uu____7785 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7779) in
                                  let uu____7797 =
                                    let uu____7806 =
                                      let uu____7814 =
                                        let uu____7820 =
                                          let uu____7821 =
                                            let uu____7822 =
                                              let uu____7825 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7826 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7825, uu____7826) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7822 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7821 in
                                        quant xy uu____7820 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7814) in
                                    let uu____7832 =
                                      let uu____7841 =
                                        let uu____7849 =
                                          let uu____7855 =
                                            let uu____7856 =
                                              let uu____7857 =
                                                let uu____7860 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7861 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7860, uu____7861) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7857 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7856 in
                                          quant xy uu____7855 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7849) in
                                      let uu____7867 =
                                        let uu____7876 =
                                          let uu____7884 =
                                            let uu____7890 =
                                              let uu____7891 =
                                                let uu____7892 =
                                                  let uu____7895 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7896 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7895, uu____7896) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7892 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7891 in
                                            quant xy uu____7890 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7884) in
                                        let uu____7902 =
                                          let uu____7911 =
                                            let uu____7919 =
                                              let uu____7925 =
                                                let uu____7926 =
                                                  let uu____7927 =
                                                    let uu____7930 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7931 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7930, uu____7931) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7927 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7926 in
                                              quant xy uu____7925 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7919) in
                                          let uu____7937 =
                                            let uu____7946 =
                                              let uu____7954 =
                                                let uu____7960 =
                                                  let uu____7961 =
                                                    let uu____7962 =
                                                      let uu____7965 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7966 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7965,
                                                        uu____7966) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7962 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7961 in
                                                quant xy uu____7960 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7954) in
                                            let uu____7972 =
                                              let uu____7981 =
                                                let uu____7989 =
                                                  let uu____7995 =
                                                    let uu____7996 =
                                                      let uu____7997 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7997 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7996 in
                                                  quant qx uu____7995 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7989) in
                                              [uu____7981] in
                                            uu____7946 :: uu____7972 in
                                          uu____7911 :: uu____7937 in
                                        uu____7876 :: uu____7902 in
                                      uu____7841 :: uu____7867 in
                                    uu____7806 :: uu____7832 in
                                  uu____7771 :: uu____7797 in
                                uu____7740 :: uu____7762 in
                              uu____7705 :: uu____7731 in
                            uu____7670 :: uu____7696 in
                          uu____7635 :: uu____7661 in
                        uu____7600 :: uu____7626 in
                      uu____7565 :: uu____7591 in
                    uu____7534 :: uu____7556 in
                  uu____7504 :: uu____7525 in
                let mk1 l v1 =
                  let uu____8125 =
                    let uu____8130 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8162  ->
                              match uu____8162 with
                              | (l',uu____8171) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8130
                      (FStar_Option.map
                         (fun uu____8204  ->
                            match uu____8204 with | (uu____8215,b) -> b v1)) in
                  FStar_All.pipe_right uu____8125 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8256  ->
                          match uu____8256 with
                          | (l',uu____8265) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8291 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8291 with
        | (xxsym,xx) ->
            let uu____8296 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8296 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8304 =
                   let uu____8308 =
                     let uu____8309 =
                       let uu____8315 =
                         let uu____8316 =
                           let uu____8319 =
                             let uu____8320 =
                               let uu____8323 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8323) in
                             FStar_SMTEncoding_Util.mkEq uu____8320 in
                           (xx_has_type, uu____8319) in
                         FStar_SMTEncoding_Util.mkImp uu____8316 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8315) in
                     FStar_SMTEncoding_Util.mkForall uu____8309 in
                   let uu____8336 =
                     let uu____8337 =
                       let uu____8338 =
                         let uu____8339 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8339 in
                       Prims.strcat module_name uu____8338 in
                     varops.mk_unique uu____8337 in
                   (uu____8308, (Some "pretyping"), uu____8336) in
                 FStar_SMTEncoding_Util.mkAssume uu____8304)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____8369 =
      let uu____8370 =
        let uu____8374 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8374, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8370 in
    let uu____8376 =
      let uu____8378 =
        let uu____8379 =
          let uu____8383 =
            let uu____8384 =
              let uu____8390 =
                let uu____8391 =
                  let uu____8394 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8394) in
                FStar_SMTEncoding_Util.mkImp uu____8391 in
              ([[typing_pred]], [xx], uu____8390) in
            mkForall_fuel uu____8384 in
          (uu____8383, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8379 in
      [uu____8378] in
    uu____8369 :: uu____8376 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8422 =
      let uu____8423 =
        let uu____8427 =
          let uu____8428 =
            let uu____8434 =
              let uu____8437 =
                let uu____8439 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8439] in
              [uu____8437] in
            let uu____8442 =
              let uu____8443 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8443 tt in
            (uu____8434, [bb], uu____8442) in
          FStar_SMTEncoding_Util.mkForall uu____8428 in
        (uu____8427, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8423 in
    let uu____8454 =
      let uu____8456 =
        let uu____8457 =
          let uu____8461 =
            let uu____8462 =
              let uu____8468 =
                let uu____8469 =
                  let uu____8472 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8472) in
                FStar_SMTEncoding_Util.mkImp uu____8469 in
              ([[typing_pred]], [xx], uu____8468) in
            mkForall_fuel uu____8462 in
          (uu____8461, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8457 in
      [uu____8456] in
    uu____8422 :: uu____8454 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8506 =
        let uu____8507 =
          let uu____8511 =
            let uu____8513 =
              let uu____8515 =
                let uu____8517 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8518 =
                  let uu____8520 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8520] in
                uu____8517 :: uu____8518 in
              tt :: uu____8515 in
            tt :: uu____8513 in
          ("Prims.Precedes", uu____8511) in
        FStar_SMTEncoding_Util.mkApp uu____8507 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8506 in
    let precedes_y_x =
      let uu____8523 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8523 in
    let uu____8525 =
      let uu____8526 =
        let uu____8530 =
          let uu____8531 =
            let uu____8537 =
              let uu____8540 =
                let uu____8542 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8542] in
              [uu____8540] in
            let uu____8545 =
              let uu____8546 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8546 tt in
            (uu____8537, [bb], uu____8545) in
          FStar_SMTEncoding_Util.mkForall uu____8531 in
        (uu____8530, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8526 in
    let uu____8557 =
      let uu____8559 =
        let uu____8560 =
          let uu____8564 =
            let uu____8565 =
              let uu____8571 =
                let uu____8572 =
                  let uu____8575 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8575) in
                FStar_SMTEncoding_Util.mkImp uu____8572 in
              ([[typing_pred]], [xx], uu____8571) in
            mkForall_fuel uu____8565 in
          (uu____8564, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8560 in
      let uu____8588 =
        let uu____8590 =
          let uu____8591 =
            let uu____8595 =
              let uu____8596 =
                let uu____8602 =
                  let uu____8603 =
                    let uu____8606 =
                      let uu____8607 =
                        let uu____8609 =
                          let uu____8611 =
                            let uu____8613 =
                              let uu____8614 =
                                let uu____8617 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8618 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8617, uu____8618) in
                              FStar_SMTEncoding_Util.mkGT uu____8614 in
                            let uu____8619 =
                              let uu____8621 =
                                let uu____8622 =
                                  let uu____8625 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8626 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8625, uu____8626) in
                                FStar_SMTEncoding_Util.mkGTE uu____8622 in
                              let uu____8627 =
                                let uu____8629 =
                                  let uu____8630 =
                                    let uu____8633 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8634 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8633, uu____8634) in
                                  FStar_SMTEncoding_Util.mkLT uu____8630 in
                                [uu____8629] in
                              uu____8621 :: uu____8627 in
                            uu____8613 :: uu____8619 in
                          typing_pred_y :: uu____8611 in
                        typing_pred :: uu____8609 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8607 in
                    (uu____8606, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8603 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8602) in
              mkForall_fuel uu____8596 in
            (uu____8595, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8591 in
        [uu____8590] in
      uu____8559 :: uu____8588 in
    uu____8525 :: uu____8557 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8664 =
      let uu____8665 =
        let uu____8669 =
          let uu____8670 =
            let uu____8676 =
              let uu____8679 =
                let uu____8681 = FStar_SMTEncoding_Term.boxString b in
                [uu____8681] in
              [uu____8679] in
            let uu____8684 =
              let uu____8685 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8685 tt in
            (uu____8676, [bb], uu____8684) in
          FStar_SMTEncoding_Util.mkForall uu____8670 in
        (uu____8669, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8665 in
    let uu____8696 =
      let uu____8698 =
        let uu____8699 =
          let uu____8703 =
            let uu____8704 =
              let uu____8710 =
                let uu____8711 =
                  let uu____8714 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8714) in
                FStar_SMTEncoding_Util.mkImp uu____8711 in
              ([[typing_pred]], [xx], uu____8710) in
            mkForall_fuel uu____8704 in
          (uu____8703, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8699 in
      [uu____8698] in
    uu____8664 :: uu____8696 in
  let mk_ref1 env reft_name uu____8736 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8747 =
        let uu____8751 =
          let uu____8753 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8753] in
        (reft_name, uu____8751) in
      FStar_SMTEncoding_Util.mkApp uu____8747 in
    let refb =
      let uu____8756 =
        let uu____8760 =
          let uu____8762 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8762] in
        (reft_name, uu____8760) in
      FStar_SMTEncoding_Util.mkApp uu____8756 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8766 =
      let uu____8767 =
        let uu____8771 =
          let uu____8772 =
            let uu____8778 =
              let uu____8779 =
                let uu____8782 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8782) in
              FStar_SMTEncoding_Util.mkImp uu____8779 in
            ([[typing_pred]], [xx; aa], uu____8778) in
          mkForall_fuel uu____8772 in
        (uu____8771, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8767 in
    [uu____8766] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8822 =
      let uu____8823 =
        let uu____8827 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8827, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8823 in
    [uu____8822] in
  let mk_and_interp env conj uu____8838 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8855 =
      let uu____8856 =
        let uu____8860 =
          let uu____8861 =
            let uu____8867 =
              let uu____8868 =
                let uu____8871 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8871, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8868 in
            ([[l_and_a_b]], [aa; bb], uu____8867) in
          FStar_SMTEncoding_Util.mkForall uu____8861 in
        (uu____8860, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8856 in
    [uu____8855] in
  let mk_or_interp env disj uu____8895 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8912 =
      let uu____8913 =
        let uu____8917 =
          let uu____8918 =
            let uu____8924 =
              let uu____8925 =
                let uu____8928 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8928, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8925 in
            ([[l_or_a_b]], [aa; bb], uu____8924) in
          FStar_SMTEncoding_Util.mkForall uu____8918 in
        (uu____8917, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8913 in
    [uu____8912] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8969 =
      let uu____8970 =
        let uu____8974 =
          let uu____8975 =
            let uu____8981 =
              let uu____8982 =
                let uu____8985 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8985, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8982 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8981) in
          FStar_SMTEncoding_Util.mkForall uu____8975 in
        (uu____8974, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8970 in
    [uu____8969] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____9032 =
      let uu____9033 =
        let uu____9037 =
          let uu____9038 =
            let uu____9044 =
              let uu____9045 =
                let uu____9048 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9048, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9045 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9044) in
          FStar_SMTEncoding_Util.mkForall uu____9038 in
        (uu____9037, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9033 in
    [uu____9032] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9093 =
      let uu____9094 =
        let uu____9098 =
          let uu____9099 =
            let uu____9105 =
              let uu____9106 =
                let uu____9109 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9109, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9106 in
            ([[l_imp_a_b]], [aa; bb], uu____9105) in
          FStar_SMTEncoding_Util.mkForall uu____9099 in
        (uu____9098, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9094 in
    [uu____9093] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9150 =
      let uu____9151 =
        let uu____9155 =
          let uu____9156 =
            let uu____9162 =
              let uu____9163 =
                let uu____9166 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9166, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9163 in
            ([[l_iff_a_b]], [aa; bb], uu____9162) in
          FStar_SMTEncoding_Util.mkForall uu____9156 in
        (uu____9155, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9151 in
    [uu____9150] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9200 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9200 in
    let uu____9202 =
      let uu____9203 =
        let uu____9207 =
          let uu____9208 =
            let uu____9214 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9214) in
          FStar_SMTEncoding_Util.mkForall uu____9208 in
        (uu____9207, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9203 in
    [uu____9202] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____9254 =
        let uu____9258 =
          let uu____9260 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9260] in
        ("Valid", uu____9258) in
      FStar_SMTEncoding_Util.mkApp uu____9254 in
    let uu____9262 =
      let uu____9263 =
        let uu____9267 =
          let uu____9268 =
            let uu____9274 =
              let uu____9275 =
                let uu____9278 =
                  let uu____9279 =
                    let uu____9285 =
                      let uu____9288 =
                        let uu____9290 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9290] in
                      [uu____9288] in
                    let uu____9293 =
                      let uu____9294 =
                        let uu____9297 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9297, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9294 in
                    (uu____9285, [xx1], uu____9293) in
                  FStar_SMTEncoding_Util.mkForall uu____9279 in
                (uu____9278, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9275 in
            ([[l_forall_a_b]], [aa; bb], uu____9274) in
          FStar_SMTEncoding_Util.mkForall uu____9268 in
        (uu____9267, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9263 in
    [uu____9262] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____9348 =
        let uu____9352 =
          let uu____9354 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9354] in
        ("Valid", uu____9352) in
      FStar_SMTEncoding_Util.mkApp uu____9348 in
    let uu____9356 =
      let uu____9357 =
        let uu____9361 =
          let uu____9362 =
            let uu____9368 =
              let uu____9369 =
                let uu____9372 =
                  let uu____9373 =
                    let uu____9379 =
                      let uu____9382 =
                        let uu____9384 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9384] in
                      [uu____9382] in
                    let uu____9387 =
                      let uu____9388 =
                        let uu____9391 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9391, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9388 in
                    (uu____9379, [xx1], uu____9387) in
                  FStar_SMTEncoding_Util.mkExists uu____9373 in
                (uu____9372, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9369 in
            ([[l_exists_a_b]], [aa; bb], uu____9368) in
          FStar_SMTEncoding_Util.mkForall uu____9362 in
        (uu____9361, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9357 in
    [uu____9356] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9427 =
      let uu____9428 =
        let uu____9432 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9433 = varops.mk_unique "typing_range_const" in
        (uu____9432, (Some "Range_const typing"), uu____9433) in
      FStar_SMTEncoding_Util.mkAssume uu____9428 in
    [uu____9427] in
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9695 =
            FStar_Util.find_opt
              (fun uu____9713  ->
                 match uu____9713 with
                 | (l,uu____9723) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9695 with
          | None  -> []
          | Some (uu____9745,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9782 = encode_function_type_as_formula None None t env in
        match uu____9782 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____9814 =
              (let uu____9815 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9815) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9814
            then
              let uu____9819 = new_term_constant_and_tok_from_lid env lid in
              match uu____9819 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9831 =
                      let uu____9832 = FStar_Syntax_Subst.compress t_norm in
                      uu____9832.FStar_Syntax_Syntax.n in
                    match uu____9831 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9837) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9854  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9857 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____9866 = prims.is lid in
               if uu____9866
               then
                 let vname = varops.new_fvar lid in
                 let uu____9871 = prims.mk lid vname in
                 match uu____9871 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9886 =
                    let uu____9892 = curried_arrow_formals_comp t_norm in
                    match uu____9892 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9903 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9903
                          then
                            let uu____9904 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___147_9905 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___147_9905.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___147_9905.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___147_9905.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___147_9905.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___147_9905.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___147_9905.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___147_9905.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___147_9905.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___147_9905.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___147_9905.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___147_9905.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___147_9905.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___147_9905.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___147_9905.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___147_9905.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___147_9905.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___147_9905.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___147_9905.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___147_9905.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___147_9905.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___147_9905.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___147_9905.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___147_9905.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9904
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9912 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9912)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9886 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9939 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9939 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9952 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___118_9976  ->
                                     match uu___118_9976 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9979 =
                                           FStar_Util.prefix vars in
                                         (match uu____9979 with
                                          | (uu____9990,(xxsym,uu____9992))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10002 =
                                                let uu____10003 =
                                                  let uu____10007 =
                                                    let uu____10008 =
                                                      let uu____10014 =
                                                        let uu____10015 =
                                                          let uu____10018 =
                                                            let uu____10019 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10019 in
                                                          (vapp, uu____10018) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10015 in
                                                      ([[vapp]], vars,
                                                        uu____10014) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10008 in
                                                  (uu____10007,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10003 in
                                              [uu____10002])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10030 =
                                           FStar_Util.prefix vars in
                                         (match uu____10030 with
                                          | (uu____10041,(xxsym,uu____10043))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____10057 =
                                                let uu____10058 =
                                                  let uu____10062 =
                                                    let uu____10063 =
                                                      let uu____10069 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10069) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10063 in
                                                  (uu____10062,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10058 in
                                              [uu____10057])
                                     | uu____10078 -> [])) in
                           let uu____10079 = encode_binders None formals env1 in
                           (match uu____10079 with
                            | (vars,guards,env',decls1,uu____10095) ->
                                let uu____10102 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10107 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10107, decls1)
                                  | Some p ->
                                      let uu____10109 = encode_formula p env' in
                                      (match uu____10109 with
                                       | (g,ds) ->
                                           let uu____10116 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10116,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10102 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10125 =
                                         let uu____10129 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10129) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10125 in
                                     let uu____10134 =
                                       let vname_decl =
                                         let uu____10139 =
                                           let uu____10145 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10150  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10145,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10139 in
                                       let uu____10155 =
                                         let env2 =
                                           let uu___148_10159 = env1 in
                                           {
                                             bindings =
                                               (uu___148_10159.bindings);
                                             depth = (uu___148_10159.depth);
                                             tcenv = (uu___148_10159.tcenv);
                                             warn = (uu___148_10159.warn);
                                             cache = (uu___148_10159.cache);
                                             nolabels =
                                               (uu___148_10159.nolabels);
                                             use_zfuel_name =
                                               (uu___148_10159.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___148_10159.current_module_name)
                                           } in
                                         let uu____10160 =
                                           let uu____10161 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10161 in
                                         if uu____10160
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10155 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10171::uu____10172 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff] in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)] in
                                                 let guarded_tok_typing =
                                                   let uu____10195 =
                                                     let uu____10201 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10201) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10195 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10215 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10217 =
                                             match formals with
                                             | [] ->
                                                 let uu____10226 =
                                                   let uu____10227 =
                                                     let uu____10229 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10229 in
                                                   push_free_var env1 lid
                                                     vname uu____10227 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10226)
                                             | uu____10232 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10237 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10237 in
                                                 let name_tok_corr =
                                                   let uu____10239 =
                                                     let uu____10243 =
                                                       let uu____10244 =
                                                         let uu____10250 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10250) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10244 in
                                                     (uu____10243,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10239 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10217 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10134 with
                                      | (decls2,env2) ->
                                          let uu____10274 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10279 =
                                              encode_term res_t1 env' in
                                            match uu____10279 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10287 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10287,
                                                  decls) in
                                          (match uu____10274 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10295 =
                                                   let uu____10299 =
                                                     let uu____10300 =
                                                       let uu____10306 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10306) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10300 in
                                                   (uu____10299,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10295 in
                                               let freshness =
                                                 let uu____10315 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10315
                                                 then
                                                   let uu____10318 =
                                                     let uu____10319 =
                                                       let uu____10325 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10331 =
                                                         varops.next_id () in
                                                       (vname, uu____10325,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10331) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10319 in
                                                   let uu____10333 =
                                                     let uu____10335 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10335] in
                                                   uu____10318 :: uu____10333
                                                 else [] in
                                               let g =
                                                 let uu____10339 =
                                                   let uu____10341 =
                                                     let uu____10343 =
                                                       let uu____10345 =
                                                         let uu____10347 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10347 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10345 in
                                                     FStar_List.append decls3
                                                       uu____10343 in
                                                   FStar_List.append decls2
                                                     uu____10341 in
                                                 FStar_List.append decls11
                                                   uu____10339 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term Prims.option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10369 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10369 with
          | None  ->
              let uu____10392 = encode_free_var env x t t_norm [] in
              (match uu____10392 with
               | (decls,env1) ->
                   let uu____10407 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10407 with
                    | (n1,x',uu____10426) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10438) -> ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10471 = encode_free_var env lid t tt quals in
          match uu____10471 with
          | (decls,env1) ->
              let uu____10482 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10482
              then
                let uu____10486 =
                  let uu____10488 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10488 in
                (uu____10486, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10516  ->
                fun lb  ->
                  match uu____10516 with
                  | (decls,env1) ->
                      let uu____10528 =
                        let uu____10532 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10532
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10528 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10546 = FStar_Syntax_Util.head_and_args t in
    match uu____10546 with
    | (hd1,args) ->
        let uu____10572 =
          let uu____10573 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10573.FStar_Syntax_Syntax.n in
        (match uu____10572 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10577,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10590 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10605  ->
      fun quals  ->
        match uu____10605 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10654 = FStar_Util.first_N nbinders formals in
              match uu____10654 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10694  ->
                         fun uu____10695  ->
                           match (uu____10694, uu____10695) with
                           | ((formal,uu____10705),(binder,uu____10707)) ->
                               let uu____10712 =
                                 let uu____10717 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10717) in
                               FStar_Syntax_Syntax.NT uu____10712) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10722 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10736  ->
                              match uu____10736 with
                              | (x,i) ->
                                  let uu____10743 =
                                    let uu___149_10744 = x in
                                    let uu____10745 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___149_10744.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___149_10744.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10745
                                    } in
                                  (uu____10743, i))) in
                    FStar_All.pipe_right uu____10722
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10757 =
                      let uu____10759 =
                        let uu____10760 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10760.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10759 in
                    let uu____10764 =
                      let uu____10765 = FStar_Syntax_Subst.compress body in
                      let uu____10766 =
                        let uu____10767 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10767 in
                      FStar_Syntax_Syntax.extend_app_n uu____10765
                        uu____10766 in
                    uu____10764 uu____10757 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10809 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10809
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___150_10810 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___150_10810.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___150_10810.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___150_10810.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___150_10810.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___150_10810.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___150_10810.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___150_10810.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___150_10810.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___150_10810.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___150_10810.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___150_10810.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___150_10810.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___150_10810.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___150_10810.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___150_10810.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___150_10810.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___150_10810.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___150_10810.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___150_10810.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___150_10810.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___150_10810.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___150_10810.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___150_10810.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10831 = FStar_Syntax_Util.abs_formals e in
                match uu____10831 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10880::uu____10881 ->
                         let uu____10889 =
                           let uu____10890 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10890.FStar_Syntax_Syntax.n in
                         (match uu____10889 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10917 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10917 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10943 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10943
                                   then
                                     let uu____10961 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10961 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11007  ->
                                                   fun uu____11008  ->
                                                     match (uu____11007,
                                                             uu____11008)
                                                     with
                                                     | ((x,uu____11018),
                                                        (b,uu____11020)) ->
                                                         let uu____11025 =
                                                           let uu____11030 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11030) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11025)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11032 =
                                            let uu____11043 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11043) in
                                          (uu____11032, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11078 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11078 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11130) ->
                              let uu____11135 =
                                let uu____11146 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11146 in
                              (uu____11135, true)
                          | uu____11179 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____11181 ->
                              let uu____11182 =
                                let uu____11183 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11184 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11183
                                  uu____11184 in
                              failwith uu____11182)
                     | uu____11197 ->
                         let uu____11198 =
                           let uu____11199 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11199.FStar_Syntax_Syntax.n in
                         (match uu____11198 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11226 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11226 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11244 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11244 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11292 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11320 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11320
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11327 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11368  ->
                            fun lb  ->
                              match uu____11368 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11419 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11419
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11422 =
                                      let uu____11430 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11430
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11422 with
                                    | (tok,decl,env2) ->
                                        let uu____11455 =
                                          let uu____11462 =
                                            let uu____11468 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11468, tok) in
                                          uu____11462 :: toks in
                                        (uu____11455, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11327 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____11570 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11575 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11575 vars)
                            else
                              (let uu____11577 =
                                 let uu____11581 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11581) in
                               FStar_SMTEncoding_Util.mkApp uu____11577) in
                      let uu____11586 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___119_11588  ->
                                 match uu___119_11588 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11589 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11592 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11592))) in
                      if uu____11586
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11612;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11614;
                                FStar_Syntax_Syntax.lbeff = uu____11615;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11656 =
                                 let uu____11660 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11660 with
                                 | (tcenv',uu____11671,e_t) ->
                                     let uu____11675 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11682 -> failwith "Impossible" in
                                     (match uu____11675 with
                                      | (e1,t_norm1) ->
                                          ((let uu___153_11691 = env1 in
                                            {
                                              bindings =
                                                (uu___153_11691.bindings);
                                              depth = (uu___153_11691.depth);
                                              tcenv = tcenv';
                                              warn = (uu___153_11691.warn);
                                              cache = (uu___153_11691.cache);
                                              nolabels =
                                                (uu___153_11691.nolabels);
                                              use_zfuel_name =
                                                (uu___153_11691.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___153_11691.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___153_11691.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11656 with
                                | (env',e1,t_norm1) ->
                                    let uu____11698 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11698 with
                                     | ((binders,body,uu____11710,uu____11711),curry)
                                         ->
                                         ((let uu____11718 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11718
                                           then
                                             let uu____11719 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11720 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11719 uu____11720
                                           else ());
                                          (let uu____11722 =
                                             encode_binders None binders env' in
                                           match uu____11722 with
                                           | (vars,guards,env'1,binder_decls,uu____11738)
                                               ->
                                               let body1 =
                                                 let uu____11746 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11746
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11749 =
                                                 let uu____11754 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11754
                                                 then
                                                   let uu____11760 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11761 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11760, uu____11761)
                                                 else
                                                   (let uu____11767 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11767)) in
                                               (match uu____11749 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11781 =
                                                        let uu____11785 =
                                                          let uu____11786 =
                                                            let uu____11792 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11792) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11786 in
                                                        let uu____11798 =
                                                          let uu____11800 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11800 in
                                                        (uu____11785,
                                                          uu____11798,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11781 in
                                                    let uu____11802 =
                                                      let uu____11804 =
                                                        let uu____11806 =
                                                          let uu____11808 =
                                                            let uu____11810 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11810 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11808 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11806 in
                                                      FStar_List.append
                                                        decls1 uu____11804 in
                                                    (uu____11802, env1))))))
                           | uu____11813 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11832 = varops.fresh "fuel" in
                             (uu____11832, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11835 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11874  ->
                                     fun uu____11875  ->
                                       match (uu____11874, uu____11875) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11957 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11957 in
                                           let gtok =
                                             let uu____11959 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11959 in
                                           let env3 =
                                             let uu____11961 =
                                               let uu____11963 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11963 in
                                             push_free_var env2 flid gtok
                                               uu____11961 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11835 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12049
                                 t_norm uu____12051 =
                                 match (uu____12049, uu____12051) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12078;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12079;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12096 =
                                       let uu____12100 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12100 with
                                       | (tcenv',uu____12115,e_t) ->
                                           let uu____12119 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12126 ->
                                                 failwith "Impossible" in
                                           (match uu____12119 with
                                            | (e1,t_norm1) ->
                                                ((let uu___154_12135 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___154_12135.bindings);
                                                    depth =
                                                      (uu___154_12135.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___154_12135.warn);
                                                    cache =
                                                      (uu___154_12135.cache);
                                                    nolabels =
                                                      (uu___154_12135.nolabels);
                                                    use_zfuel_name =
                                                      (uu___154_12135.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___154_12135.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___154_12135.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12096 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12145 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12145
                                            then
                                              let uu____12146 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12147 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12148 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12146 uu____12147
                                                uu____12148
                                            else ());
                                           (let uu____12150 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12150 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12172 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12172
                                                  then
                                                    let uu____12173 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12174 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12175 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12176 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12173 uu____12174
                                                      uu____12175 uu____12176
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12180 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12180 with
                                                  | (vars,guards,env'1,binder_decls,uu____12198)
                                                      ->
                                                      let decl_g =
                                                        let uu____12206 =
                                                          let uu____12212 =
                                                            let uu____12214 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12214 in
                                                          (g, uu____12212,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12206 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12229 =
                                                          let uu____12233 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12233) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12229 in
                                                      let gsapp =
                                                        let uu____12239 =
                                                          let uu____12243 =
                                                            let uu____12245 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12245 ::
                                                              vars_tm in
                                                          (g, uu____12243) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12239 in
                                                      let gmax =
                                                        let uu____12249 =
                                                          let uu____12253 =
                                                            let uu____12255 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12255 ::
                                                              vars_tm in
                                                          (g, uu____12253) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12249 in
                                                      let body1 =
                                                        let uu____12259 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12259
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12261 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12261 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12272
                                                               =
                                                               let uu____12276
                                                                 =
                                                                 let uu____12277
                                                                   =
                                                                   let uu____12285
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12285) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12277 in
                                                               let uu____12296
                                                                 =
                                                                 let uu____12298
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12298 in
                                                               (uu____12276,
                                                                 uu____12296,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12272 in
                                                           let eqn_f =
                                                             let uu____12301
                                                               =
                                                               let uu____12305
                                                                 =
                                                                 let uu____12306
                                                                   =
                                                                   let uu____12312
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12312) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12306 in
                                                               (uu____12305,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12301 in
                                                           let eqn_g' =
                                                             let uu____12320
                                                               =
                                                               let uu____12324
                                                                 =
                                                                 let uu____12325
                                                                   =
                                                                   let uu____12331
                                                                    =
                                                                    let uu____12332
                                                                    =
                                                                    let uu____12335
                                                                    =
                                                                    let uu____12336
                                                                    =
                                                                    let uu____12340
                                                                    =
                                                                    let uu____12342
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12342
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12340) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12336 in
                                                                    (gsapp,
                                                                    uu____12335) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12332 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12331) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12325 in
                                                               (uu____12324,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12320 in
                                                           let uu____12354 =
                                                             let uu____12359
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12359
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12376)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____12391
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12391
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12394
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    let uu____12399
                                                                    =
                                                                    let uu____12405
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12405) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12399 in
                                                                    (uu____12398,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12394 in
                                                                 let uu____12416
                                                                   =
                                                                   let uu____12420
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12420
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12428
                                                                    =
                                                                    let uu____12430
                                                                    =
                                                                    let uu____12431
                                                                    =
                                                                    let uu____12435
                                                                    =
                                                                    let uu____12436
                                                                    =
                                                                    let uu____12442
                                                                    =
                                                                    let uu____12443
                                                                    =
                                                                    let uu____12446
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12446,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12443 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12442) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12436 in
                                                                    (uu____12435,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12431 in
                                                                    [uu____12430] in
                                                                    (d3,
                                                                    uu____12428) in
                                                                 (match uu____12416
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12354
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____12481 =
                                 let uu____12488 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12524  ->
                                      fun uu____12525  ->
                                        match (uu____12524, uu____12525) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12611 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12611 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12488 in
                               (match uu____12481 with
                                | (decls2,eqns,env01) ->
                                    let uu____12651 =
                                      let isDeclFun uu___120_12659 =
                                        match uu___120_12659 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12660 -> true
                                        | uu____12666 -> false in
                                      let uu____12667 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12667
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12651 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12694 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12694
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12727 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12727 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12730 = encode_sigelt' env se in
      match uu____12730 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12740 =
                  let uu____12741 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12741 in
                [uu____12740]
            | uu____12742 ->
                let uu____12743 =
                  let uu____12745 =
                    let uu____12746 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12746 in
                  uu____12745 :: g in
                let uu____12747 =
                  let uu____12749 =
                    let uu____12750 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12750 in
                  [uu____12749] in
                FStar_List.append uu____12743 uu____12747 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12758 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12767 =
            let uu____12768 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12768 Prims.op_Negation in
          if uu____12767
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12788 ->
                   let uu____12789 =
                     let uu____12792 =
                       let uu____12793 =
                         let uu____12808 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12808) in
                       FStar_Syntax_Syntax.Tm_abs uu____12793 in
                     FStar_Syntax_Syntax.mk uu____12792 in
                   uu____12789 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12861 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12861 with
               | (aname,atok,env2) ->
                   let uu____12871 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12871 with
                    | (formals,uu____12881) ->
                        let uu____12888 =
                          let uu____12891 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12891 env2 in
                        (match uu____12888 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12899 =
                                 let uu____12900 =
                                   let uu____12906 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12914  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12906,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12900 in
                               [uu____12899;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12921 =
                               let aux uu____12950 uu____12951 =
                                 match (uu____12950, uu____12951) with
                                 | ((bv,uu____12978),(env3,acc_sorts,acc)) ->
                                     let uu____12999 = gen_term_var env3 bv in
                                     (match uu____12999 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12921 with
                              | (uu____13037,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13051 =
                                      let uu____13055 =
                                        let uu____13056 =
                                          let uu____13062 =
                                            let uu____13063 =
                                              let uu____13066 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13066) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13063 in
                                          ([[app]], xs_sorts, uu____13062) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13056 in
                                      (uu____13055, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13051 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13078 =
                                      let uu____13082 =
                                        let uu____13083 =
                                          let uu____13089 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13089) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13083 in
                                      (uu____13082,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13078 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13099 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13099 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13115,uu____13116)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13117 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13117 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13128,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13133 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___121_13135  ->
                      match uu___121_13135 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13138 -> false)) in
            Prims.op_Negation uu____13133 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13144 = encode_top_level_val env fv t quals in
             match uu____13144 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13156 =
                   let uu____13158 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13158 in
                 (uu____13156, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13163 = encode_formula f env in
          (match uu____13163 with
           | (f1,decls) ->
               let g =
                 let uu____13172 =
                   let uu____13173 =
                     let uu____13177 =
                       let uu____13179 =
                         let uu____13180 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13180 in
                       Some uu____13179 in
                     let uu____13181 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13177, uu____13181) in
                   FStar_SMTEncoding_Util.mkAssume uu____13173 in
                 [uu____13172] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13185,uu____13186) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13192 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13199 =
                       let uu____13204 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13204.FStar_Syntax_Syntax.fv_name in
                     uu____13199.FStar_Syntax_Syntax.v in
                   let uu____13208 =
                     let uu____13209 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13209 in
                   if uu____13208
                   then
                     let val_decl =
                       let uu___155_13224 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___155_13224.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___155_13224.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___155_13224.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13228 = encode_sigelt' env1 val_decl in
                     match uu____13228 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13192 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13245,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13247;
                          FStar_Syntax_Syntax.lbtyp = uu____13248;
                          FStar_Syntax_Syntax.lbeff = uu____13249;
                          FStar_Syntax_Syntax.lbdef = uu____13250;_}::[]),uu____13251,uu____13252)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13266 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13266 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13289 =
                   let uu____13291 =
                     let uu____13292 =
                       let uu____13296 =
                         let uu____13297 =
                           let uu____13303 =
                             let uu____13304 =
                               let uu____13307 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13307) in
                             FStar_SMTEncoding_Util.mkEq uu____13304 in
                           ([[b2t_x]], [xx], uu____13303) in
                         FStar_SMTEncoding_Util.mkForall uu____13297 in
                       (uu____13296, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13292 in
                   [uu____13291] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13289 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13324,uu____13325,uu____13326)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13332  ->
                  match uu___122_13332 with
                  | FStar_Syntax_Syntax.Discriminator uu____13333 -> true
                  | uu____13334 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13336,lids,uu____13338) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13345 =
                     let uu____13346 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13346.FStar_Ident.idText in
                   uu____13345 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___123_13348  ->
                     match uu___123_13348 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13349 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13352,uu____13353)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___124_13363  ->
                  match uu___124_13363 with
                  | FStar_Syntax_Syntax.Projector uu____13364 -> true
                  | uu____13367 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13374 = try_lookup_free_var env l in
          (match uu____13374 with
           | Some uu____13378 -> ([], env)
           | None  ->
               let se1 =
                 let uu___156_13381 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___156_13381.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___156_13381.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13387,uu____13388) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13400) ->
          let uu____13405 = encode_sigelts env ses in
          (match uu____13405 with
           | (g,env1) ->
               let uu____13415 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___125_13425  ->
                         match uu___125_13425 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13426;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13427;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13428;_}
                             -> false
                         | uu____13430 -> true)) in
               (match uu____13415 with
                | (g',inversions) ->
                    let uu____13439 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___126_13449  ->
                              match uu___126_13449 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13450 ->
                                  true
                              | uu____13456 -> false)) in
                    (match uu____13439 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13467,tps,k,uu____13470,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___127_13480  ->
                    match uu___127_13480 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13481 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13488 = c in
              match uu____13488 with
              | (name,args,uu____13492,uu____13493,uu____13494) ->
                  let uu____13497 =
                    let uu____13498 =
                      let uu____13504 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13511  ->
                                match uu____13511 with
                                | (uu____13515,sort,uu____13517) -> sort)) in
                      (name, uu____13504, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13498 in
                  [uu____13497]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13535 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13538 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13538 FStar_Option.isNone)) in
            if uu____13535
            then []
            else
              (let uu____13555 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13555 with
               | (xxsym,xx) ->
                   let uu____13561 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13572  ->
                             fun l  ->
                               match uu____13572 with
                               | (out,decls) ->
                                   let uu____13584 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13584 with
                                    | (uu____13590,data_t) ->
                                        let uu____13592 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13592 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13621 =
                                                 let uu____13622 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13622.FStar_Syntax_Syntax.n in
                                               match uu____13621 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13630,indices) ->
                                                   indices
                                               | uu____13646 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13658  ->
                                                         match uu____13658
                                                         with
                                                         | (x,uu____13662) ->
                                                             let uu____13663
                                                               =
                                                               let uu____13664
                                                                 =
                                                                 let uu____13668
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13668,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13664 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13663)
                                                    env) in
                                             let uu____13670 =
                                               encode_args indices env1 in
                                             (match uu____13670 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____13690 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13698
                                                                 =
                                                                 let uu____13701
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13701,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13698)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13690
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13703 =
                                                      let uu____13704 =
                                                        let uu____13707 =
                                                          let uu____13708 =
                                                            let uu____13711 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13711,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13708 in
                                                        (out, uu____13707) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13704 in
                                                    (uu____13703,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13561 with
                    | (data_ax,decls) ->
                        let uu____13719 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13719 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13730 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13730 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13733 =
                                 let uu____13737 =
                                   let uu____13738 =
                                     let uu____13744 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13752 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13744,
                                       uu____13752) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13738 in
                                 let uu____13760 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13737, (Some "inversion axiom"),
                                   uu____13760) in
                               FStar_SMTEncoding_Util.mkAssume uu____13733 in
                             let pattern_guarded_inversion =
                               let uu____13764 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13764
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13772 =
                                   let uu____13773 =
                                     let uu____13777 =
                                       let uu____13778 =
                                         let uu____13784 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13792 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13784, uu____13792) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13778 in
                                     let uu____13800 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13777, (Some "inversion axiom"),
                                       uu____13800) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13773 in
                                 [uu____13772]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13803 =
            let uu____13811 =
              let uu____13812 = FStar_Syntax_Subst.compress k in
              uu____13812.FStar_Syntax_Syntax.n in
            match uu____13811 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13841 -> (tps, k) in
          (match uu____13803 with
           | (formals,res) ->
               let uu____13856 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13856 with
                | (formals1,res1) ->
                    let uu____13863 = encode_binders None formals1 env in
                    (match uu____13863 with
                     | (vars,guards,env',binder_decls,uu____13878) ->
                         let uu____13885 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13885 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13898 =
                                  let uu____13902 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13902) in
                                FStar_SMTEncoding_Util.mkApp uu____13898 in
                              let uu____13907 =
                                let tname_decl =
                                  let uu____13913 =
                                    let uu____13914 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13929  ->
                                              match uu____13929 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13937 = varops.next_id () in
                                    (tname, uu____13914,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13937, false) in
                                  constructor_or_logic_type_decl uu____13913 in
                                let uu____13942 =
                                  match vars with
                                  | [] ->
                                      let uu____13949 =
                                        let uu____13950 =
                                          let uu____13952 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13952 in
                                        push_free_var env1 t tname
                                          uu____13950 in
                                      ([], uu____13949)
                                  | uu____13956 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13962 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13962 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13971 =
                                          let uu____13975 =
                                            let uu____13976 =
                                              let uu____13984 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13984) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13976 in
                                          (uu____13975,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13971 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13942 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13907 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14007 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14007 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14021 =
                                               let uu____14022 =
                                                 let uu____14026 =
                                                   let uu____14027 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14027 in
                                                 (uu____14026,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14022 in
                                             [uu____14021]
                                           else [] in
                                         let uu____14030 =
                                           let uu____14032 =
                                             let uu____14034 =
                                               let uu____14035 =
                                                 let uu____14039 =
                                                   let uu____14040 =
                                                     let uu____14046 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14046) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14040 in
                                                 (uu____14039, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14035 in
                                             [uu____14034] in
                                           FStar_List.append karr uu____14032 in
                                         FStar_List.append decls1 uu____14030 in
                                   let aux =
                                     let uu____14055 =
                                       let uu____14057 =
                                         inversion_axioms tapp vars in
                                       let uu____14059 =
                                         let uu____14061 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14061] in
                                       FStar_List.append uu____14057
                                         uu____14059 in
                                     FStar_List.append kindingAx uu____14055 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14066,uu____14067,uu____14068,uu____14069,uu____14070)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14075,t,uu____14077,n_tps,uu____14079) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14084 = new_term_constant_and_tok_from_lid env d in
          (match uu____14084 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14095 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14095 with
                | (formals,t_res) ->
                    let uu____14117 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14117 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14126 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14126 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14164 =
                                            mk_term_projector_name d x in
                                          (uu____14164,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14166 =
                                  let uu____14176 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14176, true) in
                                FStar_All.pipe_right uu____14166
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____14198 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14198 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14206::uu____14207 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____14232 =
                                           let uu____14238 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14238) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14232
                                     | uu____14251 -> tok_typing in
                                   let uu____14256 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14256 with
                                    | (vars',guards',env'',decls_formals,uu____14271)
                                        ->
                                        let uu____14278 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14278 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14297 ->
                                                   let uu____14301 =
                                                     let uu____14302 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14302 in
                                                   [uu____14301] in
                                             let encode_elim uu____14309 =
                                               let uu____14310 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14310 with
                                               | (head1,args) ->
                                                   let uu____14339 =
                                                     let uu____14340 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14340.FStar_Syntax_Syntax.n in
                                                   (match uu____14339 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.tk
                                                           = _;
                                                         FStar_Syntax_Syntax.pos
                                                           = _;
                                                         FStar_Syntax_Syntax.vars
                                                           = _;_},_)
                                                      |FStar_Syntax_Syntax.Tm_fvar
                                                      fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14358 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14358
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14384
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14392
                                                                    =
                                                                    let uu____14393
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14393 in
                                                                    if
                                                                    uu____14392
                                                                    then
                                                                    let uu____14400
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14400]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14402
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14415
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14415
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14437
                                                                    =
                                                                    let uu____14441
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14441 in
                                                                    (match uu____14437
                                                                    with
                                                                    | 
                                                                    (uu____14448,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14454
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14454
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14456
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14456
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 encoded_args in
                                                             (match uu____14402
                                                              with
                                                              | (uu____14464,arg_vars,elim_eqns_or_guards,uu____14467)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    let uu____14490
                                                                    =
                                                                    let uu____14491
                                                                    =
                                                                    let uu____14497
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14503
                                                                    =
                                                                    let uu____14504
                                                                    =
                                                                    let uu____14507
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14507) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14504 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14497,
                                                                    uu____14503) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14491 in
                                                                    (uu____14490,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14486 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14520
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14520,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14522
                                                                    =
                                                                    let uu____14526
                                                                    =
                                                                    let uu____14527
                                                                    =
                                                                    let uu____14533
                                                                    =
                                                                    let uu____14536
                                                                    =
                                                                    let uu____14538
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14538] in
                                                                    [uu____14536] in
                                                                    let uu____14541
                                                                    =
                                                                    let uu____14542
                                                                    =
                                                                    let uu____14545
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14546
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14545,
                                                                    uu____14546) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14542 in
                                                                    (uu____14533,
                                                                    [x],
                                                                    uu____14541) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14527 in
                                                                    let uu____14556
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14526,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14556) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14522
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14561
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____14576
                                                                    =
                                                                    let uu____14577
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14577
                                                                    dapp1 in
                                                                    [uu____14576]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14561
                                                                    FStar_List.flatten in
                                                                    let uu____14581
                                                                    =
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14592
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14598
                                                                    =
                                                                    let uu____14599
                                                                    =
                                                                    let uu____14602
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14602) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14599 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14592,
                                                                    uu____14598) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14586 in
                                                                    (uu____14585,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14581) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14612 ->
                                                        ((let uu____14614 =
                                                            let uu____14615 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14616 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14615
                                                              uu____14616 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14614);
                                                         ([], []))) in
                                             let uu____14619 = encode_elim () in
                                             (match uu____14619 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14631 =
                                                      let uu____14633 =
                                                        let uu____14635 =
                                                          let uu____14637 =
                                                            let uu____14639 =
                                                              let uu____14640
                                                                =
                                                                let uu____14646
                                                                  =
                                                                  let uu____14648
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14649 in
                                                                  Some
                                                                    uu____14648 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14646) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14640 in
                                                            [uu____14639] in
                                                          let uu____14652 =
                                                            let uu____14654 =
                                                              let uu____14656
                                                                =
                                                                let uu____14658
                                                                  =
                                                                  let uu____14660
                                                                    =
                                                                    let uu____14662
                                                                    =
                                                                    let uu____14664
                                                                    =
                                                                    let uu____14665
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    let uu____14670
                                                                    =
                                                                    let uu____14676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14676) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14670 in
                                                                    (uu____14669,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14665 in
                                                                    let uu____14683
                                                                    =
                                                                    let uu____14685
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14690
                                                                    =
                                                                    let uu____14691
                                                                    =
                                                                    let uu____14697
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14697,
                                                                    uu____14703) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14691 in
                                                                    (uu____14690,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14686 in
                                                                    [uu____14685] in
                                                                    uu____14664
                                                                    ::
                                                                    uu____14683 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14662 in
                                                                  FStar_List.append
                                                                    uu____14660
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14658 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14656 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14654 in
                                                          FStar_List.append
                                                            uu____14637
                                                            uu____14652 in
                                                        FStar_List.append
                                                          decls3 uu____14635 in
                                                      FStar_List.append
                                                        decls2 uu____14633 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14631 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14724  ->
              fun se  ->
                match uu____14724 with
                | (g,env1) ->
                    let uu____14736 = encode_sigelt env1 se in
                    (match uu____14736 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14772 =
        match uu____14772 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14790 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14795 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14795
                   then
                     let uu____14796 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14797 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14798 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14796 uu____14797 uu____14798
                   else ());
                  (let uu____14800 = encode_term t1 env1 in
                   match uu____14800 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14810 =
                         let uu____14814 =
                           let uu____14815 =
                             let uu____14816 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14816
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14815 in
                         new_term_constant_from_string env1 x uu____14814 in
                       (match uu____14810 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14827 = FStar_Options.log_queries () in
                              if uu____14827
                              then
                                let uu____14829 =
                                  let uu____14830 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14831 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14832 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14830 uu____14831 uu____14832 in
                                Some uu____14829
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14843,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14852 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14852 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14871 = encode_sigelt env1 se in
                 (match uu____14871 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14881 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14881 with | (uu____14893,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14938  ->
            match uu____14938 with
            | (l,uu____14945,uu____14946) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14967  ->
            match uu____14967 with
            | (l,uu____14975,uu____14976) ->
                let uu____14981 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14982 =
                  let uu____14984 =
                    let uu____14985 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14985 in
                  [uu____14984] in
                uu____14981 :: uu____14982)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14996 =
      let uu____14998 =
        let uu____14999 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15001 =
          let uu____15002 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15002 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14999;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15001
        } in
      [uu____14998] in
    FStar_ST.write last_env uu____14996
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15012 = FStar_ST.read last_env in
      match uu____15012 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15018 ->
          let uu___157_15020 = e in
          let uu____15021 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___157_15020.bindings);
            depth = (uu___157_15020.depth);
            tcenv;
            warn = (uu___157_15020.warn);
            cache = (uu___157_15020.cache);
            nolabels = (uu___157_15020.nolabels);
            use_zfuel_name = (uu___157_15020.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___157_15020.encode_non_total_function_typ);
            current_module_name = uu____15021
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15025 = FStar_ST.read last_env in
    match uu____15025 with
    | [] -> failwith "Empty env stack"
    | uu____15030::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15038  ->
    let uu____15039 = FStar_ST.read last_env in
    match uu____15039 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___158_15050 = hd1 in
          {
            bindings = (uu___158_15050.bindings);
            depth = (uu___158_15050.depth);
            tcenv = (uu___158_15050.tcenv);
            warn = (uu___158_15050.warn);
            cache = refs;
            nolabels = (uu___158_15050.nolabels);
            use_zfuel_name = (uu___158_15050.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_15050.encode_non_total_function_typ);
            current_module_name = (uu___158_15050.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15056  ->
    let uu____15057 = FStar_ST.read last_env in
    match uu____15057 with
    | [] -> failwith "Popping an empty stack"
    | uu____15062::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15070  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15073  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15076  ->
    let uu____15077 = FStar_ST.read last_env in
    match uu____15077 with
    | hd1::uu____15083::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15089 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____15138::uu____15139,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___159_15143 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___159_15143.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___159_15143.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___159_15143.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15144 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15155 =
        let uu____15157 =
          let uu____15158 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15158 in
        let uu____15159 = open_fact_db_tags env in uu____15157 :: uu____15159 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15155
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____15174 = encode_sigelt env se in
      match uu____15174 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15199 = FStar_Options.log_queries () in
        if uu____15199
        then
          let uu____15201 =
            let uu____15202 =
              let uu____15203 =
                let uu____15204 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15204 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15203 in
            FStar_SMTEncoding_Term.Caption uu____15202 in
          uu____15201 :: decls
        else decls in
      let env =
        let uu____15211 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15211 tcenv in
      let uu____15212 = encode_top_level_facts env se in
      match uu____15212 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15221 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15221))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15232 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15232
       then
         let uu____15233 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15233
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15254  ->
                 fun se  ->
                   match uu____15254 with
                   | (g,env2) ->
                       let uu____15266 = encode_top_level_facts env2 se in
                       (match uu____15266 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15279 =
         encode_signature
           (let uu___160_15283 = env in
            {
              bindings = (uu___160_15283.bindings);
              depth = (uu___160_15283.depth);
              tcenv = (uu___160_15283.tcenv);
              warn = false;
              cache = (uu___160_15283.cache);
              nolabels = (uu___160_15283.nolabels);
              use_zfuel_name = (uu___160_15283.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_15283.encode_non_total_function_typ);
              current_module_name = (uu___160_15283.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15279 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15295 = FStar_Options.log_queries () in
             if uu____15295
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___161_15300 = env1 in
               {
                 bindings = (uu___161_15300.bindings);
                 depth = (uu___161_15300.depth);
                 tcenv = (uu___161_15300.tcenv);
                 warn = true;
                 cache = (uu___161_15300.cache);
                 nolabels = (uu___161_15300.nolabels);
                 use_zfuel_name = (uu___161_15300.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_15300.encode_non_total_function_typ);
                 current_module_name = (uu___161_15300.current_module_name)
               });
            (let uu____15302 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15302
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15337 =
           let uu____15338 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15338.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15337);
        (let env =
           let uu____15340 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15340 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15347 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15368 = aux rest in
                 (match uu____15368 with
                  | (out,rest1) ->
                      let t =
                        let uu____15386 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15386 with
                        | Some uu____15390 ->
                            let uu____15391 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15391
                              x.FStar_Syntax_Syntax.sort
                        | uu____15392 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15395 =
                        let uu____15397 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_15398 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_15398.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_15398.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15397 :: out in
                      (uu____15395, rest1))
             | uu____15401 -> ([], bindings1) in
           let uu____15405 = aux bindings in
           match uu____15405 with
           | (closing,bindings1) ->
               let uu____15419 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15419, bindings1) in
         match uu____15347 with
         | (q1,bindings1) ->
             let uu____15432 =
               let uu____15435 =
                 FStar_List.filter
                   (fun uu___128_15437  ->
                      match uu___128_15437 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15438 ->
                          false
                      | uu____15442 -> true) bindings1 in
               encode_env_bindings env uu____15435 in
             (match uu____15432 with
              | (env_decls,env1) ->
                  ((let uu____15453 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15453
                    then
                      let uu____15454 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15454
                    else ());
                   (let uu____15456 = encode_formula q1 env1 in
                    match uu____15456 with
                    | (phi,qdecls) ->
                        let uu____15468 =
                          let uu____15471 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15471 phi in
                        (match uu____15468 with
                         | (labels,phi1) ->
                             let uu____15481 = encode_labels labels in
                             (match uu____15481 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15502 =
                                      let uu____15506 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15507 =
                                        varops.mk_unique "@query" in
                                      (uu____15506, (Some "query"),
                                        uu____15507) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15502 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15520 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15520 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15522 = encode_formula q env in
       match uu____15522 with
       | (f,uu____15526) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15528) -> true
             | uu____15531 -> false)))