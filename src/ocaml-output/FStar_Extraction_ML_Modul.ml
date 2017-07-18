open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let uu____33 =
          let uu____35 = FStar_Syntax_Syntax.iarg t in
          let uu____36 =
            let uu____38 =
              let uu____39 =
                let uu____40 =
                  let uu____43 =
                    let uu____44 =
                      let uu____45 =
                        let uu____49 =
                          let uu____50 =
                            let uu____51 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____51 in
                          FStar_Bytes.string_as_unicode_bytes uu____50 in
                        (uu____49, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____45 in
                    FStar_Syntax_Syntax.Tm_constant uu____44 in
                  FStar_Syntax_Syntax.mk uu____43 in
                uu____40 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
            [uu____38] in
          uu____35 :: uu____36 in
        (uu____32, uu____33) in
      FStar_Syntax_Syntax.Tm_app uu____22 in
    FStar_Syntax_Syntax.mk uu____21 in
  uu____18 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___147_88 =
  match uu___147_88 with
  | a::b::[] -> (a, b)
  | uu____92 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.tyattr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____101 = FStar_Syntax_Subst.compress x in
    match uu____101 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.tk = uu____104;
        FStar_Syntax_Syntax.pos = uu____105;
        FStar_Syntax_Syntax.vars = uu____106;_} when
        let uu____109 =
          let uu____110 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____110 in
        uu____109 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____112;
             FStar_Syntax_Syntax.pos = uu____113;
             FStar_Syntax_Syntax.vars = uu____114;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____116));
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____117;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____118;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____119;_},uu____120)::[]);
        FStar_Syntax_Syntax.tk = uu____121;
        FStar_Syntax_Syntax.pos = uu____122;
        FStar_Syntax_Syntax.vars = uu____123;_} when
        let uu____149 =
          let uu____150 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____150 in
        uu____149 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____152);
        FStar_Syntax_Syntax.tk = uu____153;
        FStar_Syntax_Syntax.pos = uu____154;
        FStar_Syntax_Syntax.vars = uu____155;_} -> extract_attr x1
    | a -> FStar_Pervasives_Native.None
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____203  ->
         match uu____203 with
         | (bv,uu____209) ->
             let uu____210 =
               let uu____211 =
                 let uu____213 =
                   let uu____214 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____214 in
                 FStar_Pervasives_Native.Some uu____213 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____211 in
             let uu____215 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____210, uu____215)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let def1 =
              let uu____245 =
                let uu____246 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____246 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____245 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____248 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____258 -> def1 in
            let uu____259 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____266) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____279 -> ([], def2) in
            match uu____259 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___148_292  ->
                       match uu___148_292 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____293 -> false) quals in
                let uu____294 = binders_as_mlty_binders env bs in
                (match uu____294 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____306 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____306
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____309 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___149_313  ->
                                 match uu___149_313 with
                                 | FStar_Syntax_Syntax.Projector uu____314 ->
                                     true
                                 | uu____317 -> false)) in
                       if uu____309
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____335 =
                         let uu____346 = lident_as_mlsymbol lid in
                         (assumed, uu____346, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____335] in
                     let def3 =
                       let uu____373 =
                         let uu____374 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____374 in
                       [uu____373; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____376 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_379  ->
                                 match uu___150_379 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____380 -> false)) in
                       if uu____376
                       then env1
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
let __proj__Mkdata_constructor__item__dname:
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
let __proj__Mkdata_constructor__item__dtyp:
  data_constructor -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;
  iattrs: FStar_Extraction_ML_Syntax.tyattrs;}
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iquals
let __proj__Mkinductive_family__item__iattrs:
  inductive_family -> FStar_Extraction_ML_Syntax.tyattrs =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iattrs
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____509 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____510 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____511 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____512 =
      let uu____513 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____521 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____522 =
                  let uu____523 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____523 in
                Prims.strcat uu____521 uu____522)) in
      FStar_All.pipe_right uu____513 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____509 uu____510 uu____511
      uu____512
let bundle_as_inductive_families env ses quals attrs =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____586 = FStar_Syntax_Subst.open_term bs t in
              (match uu____586 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____614,t2,l',nparams,uu____618) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____621 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____621 with
                                  | (bs',body) ->
                                      let uu____642 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____642 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____687  ->
                                                  fun uu____688  ->
                                                    match (uu____687,
                                                            uu____688)
                                                    with
                                                    | ((b',uu____698),
                                                       (b,uu____700)) ->
                                                        let uu____705 =
                                                          let uu____710 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____710) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____705)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____712 =
                                               let uu____715 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____715 in
                                             FStar_All.pipe_right uu____712
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____720 -> [])) in
                   let attrs1 =
                     extract_attrs
                       (FStar_List.append se.FStar_Syntax_Syntax.sigattrs
                          attrs) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals);
                      iattrs = attrs1
                    }])
          | uu____723 -> []))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____762 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____762 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____767 =
            let uu____768 =
              let uu____771 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____771 in
            uu____768.FStar_Syntax_Syntax.n in
          match uu____767 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____774) ->
              FStar_List.map
                (fun uu____792  ->
                   match uu____792 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____796;
                        FStar_Syntax_Syntax.sort = uu____797;_},uu____798)
                       -> ppname.FStar_Ident.idText) bs
          | uu____801 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____808 =
          let uu____809 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____809 in
        let uu____812 =
          let uu____818 = lident_as_mlsymbol ctor.dname in
          let uu____819 =
            let uu____823 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____823 in
          (uu____818, uu____819) in
        (uu____808, uu____812) in
      let extract_one_family env1 ind =
        let uu____851 = binders_as_mlty_binders env1 ind.iparams in
        match uu____851 with
        | (env2,vars) ->
            let uu____870 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____870 with
             | (env3,ctors) ->
                 let uu____918 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____918 with
                  | (indices,uu____938) ->
                      let ml_params =
                        let uu____951 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____963  ->
                                    let uu____966 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____966)) in
                        FStar_List.append vars uu____951 in
                      let tbody =
                        let uu____968 =
                          FStar_Util.find_opt
                            (fun uu___151_972  ->
                               match uu___151_972 with
                               | FStar_Syntax_Syntax.RecordType uu____973 ->
                                   true
                               | uu____978 -> false) ind.iquals in
                        match uu____968 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____985 = FStar_List.hd ctors in
                            (match uu____985 with
                             | (uu____996,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1021  ->
                                          match uu____1021 with
                                          | (uu____1026,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1029 =
                                                lident_as_mlsymbol lid in
                                              (uu____1029, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1030 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1032 =
                        let uu____1042 = lident_as_mlsymbol ind.iname in
                        (false, uu____1042, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1032))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1060,t,uu____1062,uu____1063,uu____1064);
            FStar_Syntax_Syntax.sigrng = uu____1065;
            FStar_Syntax_Syntax.sigquals = uu____1066;
            FStar_Syntax_Syntax.sigmeta = uu____1067;
            FStar_Syntax_Syntax.sigattrs = uu____1068;_}::[],uu____1069),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1078 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1078 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1103),quals) ->
          let ifams =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          let uu____1114 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1114 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1162 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1187 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1187);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1191 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1196 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1205 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1233 =
               let uu____1236 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1236 ml_name tysc
                 false false in
             match uu____1233 with
             | (g2,mangled_name) ->
                 ((let uu____1242 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1242
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____1254 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1254
              then
                let uu____1255 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1255
              else ());
             (let uu____1257 =
                let uu____1258 = FStar_Syntax_Subst.compress tm in
                uu____1258.FStar_Syntax_Syntax.n in
              match uu____1257 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1264) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1271 =
                    let uu____1276 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1276 in
                  (match uu____1271 with
                   | (uu____1305,uu____1306,tysc,uu____1308) ->
                       let uu____1309 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1309, tysc))
              | uu____1310 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1332 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1332
              then
                let uu____1333 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1334 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1333
                  uu____1334
              else ());
             (let uu____1336 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1336 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1346 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1346 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1367 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1367 with
                   | (a_let,uu____1374,ty) ->
                       ((let uu____1377 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1377
                         then
                           let uu____1378 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1378
                         else ());
                        (let uu____1380 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1385,uu____1386,mllb::[]),uu____1388)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1399 -> failwith "Impossible" in
                         match uu____1380 with
                         | (exp,tysc) ->
                             ((let uu____1407 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1407
                               then
                                 ((let uu____1409 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1409);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1413 =
             let uu____1416 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1416 with
             | (return_tm,ty_sc) ->
                 let uu____1424 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1424 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1413 with
            | (g1,return_decl) ->
                let uu____1436 =
                  let uu____1439 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1439 with
                  | (bind_tm,ty_sc) ->
                      let uu____1447 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1447 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1436 with
                 | (g2,bind_decl) ->
                     let uu____1459 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1459 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1471 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1474,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____1480 =
             let uu____1481 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1484  ->
                       match uu___152_1484 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1485 -> false)) in
             Prims.op_Negation uu____1481 in
           if uu____1480
           then (g, [])
           else
             (let uu____1491 = FStar_Syntax_Util.arrow_formals t in
              match uu____1491 with
              | (bs,uu____1503) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1515 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____1515)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1517) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1526 =
             let uu____1531 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1531 with
             | (tcenv,uu____1547,def_typ) ->
                 let uu____1551 = as_pair def_typ in (tcenv, uu____1551) in
           (match uu____1526 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1566 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1566 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1568) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1594) ->
                   let uu____1599 =
                     let uu____1600 = FStar_Syntax_Subst.compress h' in
                     uu____1600.FStar_Syntax_Syntax.n in
                   (match uu____1599 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____1604 =
                          let uu____1605 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1605 "FStar.Tactics" in
                        Prims.op_Negation uu____1604
                    | uu____1606 -> false)
               | uu____1607 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1628 =
                   let uu____1629 =
                     let uu____1630 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1630 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1629 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1628 in
               let lid_arg =
                 let uu____1632 =
                   let uu____1633 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1633 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1632 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1640 =
                   let uu____1641 =
                     let uu____1642 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1642 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1641 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1640 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1651 =
                   let uu____1652 =
                     let uu____1656 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1656) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1652 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1651 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____1662 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1662 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1680 =
                        let uu____1681 = FStar_Syntax_Subst.compress t in
                        uu____1681.FStar_Syntax_Syntax.n in
                      (match uu____1680 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1703 =
                               let uu____1705 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1705.FStar_Syntax_Syntax.fv_name in
                             uu____1703.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1707 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1707 in
                           let uu____1708 = is_tactic_decl assm_lid h1 in
                           if uu____1708
                           then
                             let uu____1710 =
                               let uu____1711 =
                                 let uu____1712 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____1712 in
                               mk_registration tac_lid assm_lid uu____1711 bs in
                             [uu____1710]
                           else []
                       | uu____1724 -> []))
             | uu____1725 -> [] in
           let uu____1727 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1727 with
            | (ml_let,uu____1735,uu____1736) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1741,bindings),uu____1743) ->
                     let uu____1750 =
                       FStar_List.fold_left2
                         (fun uu____1771  ->
                            fun ml_lb  ->
                              fun uu____1773  ->
                                match (uu____1771, uu____1773) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1786;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1788;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1789;_})
                                    ->
                                    let lb_lid =
                                      let uu____1803 =
                                        let uu____1805 =
                                          FStar_Util.right lbname in
                                        uu____1805.FStar_Syntax_Syntax.fv_name in
                                      uu____1803.FStar_Syntax_Syntax.v in
                                    let uu____1806 =
                                      let uu____1809 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1813  ->
                                                match uu___153_1813 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1814 -> true
                                                | uu____1817 -> false)) in
                                      if uu____1809
                                      then
                                        let mname =
                                          let uu____1821 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1821
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1822 =
                                          let uu____1825 =
                                            FStar_Util.right lbname in
                                          let uu____1826 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1825 mname uu____1826
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1822 with
                                        | (env1,uu____1830) ->
                                            (env1,
                                              (let uu___158_1832 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1832.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1835 =
                                           let uu____1836 =
                                             let uu____1839 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1839
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1836 in
                                         (uu____1835, ml_lb)) in
                                    (match uu____1806 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1750 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1860  ->
                                 match uu___154_1860 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1862 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1873  ->
                                 match uu___155_1873 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1878));
                                     FStar_Syntax_Syntax.tk = uu____1879;
                                     FStar_Syntax_Syntax.pos = uu____1880;
                                     FStar_Syntax_Syntax.vars = uu____1881;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1886 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1890 =
                            let uu____1892 =
                              let uu____1894 =
                                let uu____1895 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1895 in
                              [uu____1894;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1892
                              tactic_registration_decl in
                          (g1, uu____1890))
                 | uu____1899 ->
                     let uu____1900 =
                       let uu____1901 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1901 in
                     failwith uu____1900))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1906,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1910 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1910
           then
             let always_fail =
               let imp =
                 let uu____1917 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1917 with
                 | ([],t1) ->
                     let b =
                       let uu____1936 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1936 in
                     let uu____1937 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1937
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____1950 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1950
                       FStar_Pervasives_Native.None in
               let uu___159_1951 = se in
               let uu____1952 =
                 let uu____1953 =
                   let uu____1957 =
                     let uu____1961 =
                       let uu____1963 =
                         let uu____1964 =
                           let uu____1967 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____1967 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1964;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1963] in
                     (false, uu____1961) in
                   (uu____1957, []) in
                 FStar_Syntax_Syntax.Sig_let uu____1953 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1952;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1951.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1951.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1951.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_1951.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____1973 = extract_sig g always_fail in
             (match uu____1973 with
              | (g1,mlm) ->
                  let uu____1984 =
                    FStar_Util.find_map quals
                      (fun uu___156_1988  ->
                         match uu___156_1988 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____1991 -> FStar_Pervasives_Native.None) in
                  (match uu____1984 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____1996 =
                         let uu____1998 =
                           let uu____1999 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1999 in
                         let uu____2000 =
                           let uu____2002 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2002] in
                         uu____1998 :: uu____2000 in
                       (g1, uu____1996)
                   | uu____2004 ->
                       let uu____2006 =
                         FStar_Util.find_map quals
                           (fun uu___157_2011  ->
                              match uu___157_2011 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2014)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2015 -> FStar_Pervasives_Native.None) in
                       (match uu____2006 with
                        | FStar_Pervasives_Native.Some uu____2019 -> (g1, [])
                        | uu____2021 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2027 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2027 with
            | (ml_main,uu____2035,uu____2036) ->
                let uu____2037 =
                  let uu____2039 =
                    let uu____2040 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2040 in
                  [uu____2039; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2037))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2042 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2046 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2051 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2053 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2073 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2073 FStar_Pervasives_Native.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____2101 = FStar_Options.debug_any () in
       if uu____2101
       then
         let uu____2102 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____2102
       else ());
      (let uu____2104 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_2107 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2107.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2107.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2107.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____2108 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____2108 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____2125 = FStar_Options.codegen () in
             match uu____2125 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____2127 -> false in
           let uu____2129 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2129
           then
             ((let uu____2134 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2134);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))