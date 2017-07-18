open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____5 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | IRight  -> true | uu____10 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____15 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____20 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____25 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____34 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____39 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____45 -> false
let __proj__Infix__item___0: fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2
let t_prio_fun: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10"), (Infix Right))
let t_prio_tpl: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix NonAssoc))
let t_prio_name: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), Postfix)
let e_bin_prio_lambda: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "5"), Prefix)
let e_bin_prio_if: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "15"), Prefix)
let e_bin_prio_letin: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "19"), Prefix)
let e_bin_prio_or: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix Left))
let e_bin_prio_and: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "25"), (Infix Left))
let e_bin_prio_eq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "27"), (Infix NonAssoc))
let e_bin_prio_order: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "29"), (Infix NonAssoc))
let e_bin_prio_op1: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), (Infix Left))
let e_bin_prio_op2: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "40"), (Infix Left))
let e_bin_prio_op3: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "50"), (Infix Left))
let e_bin_prio_op4: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "60"), (Infix Left))
let e_bin_prio_comb: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "70"), (Infix Left))
let e_bin_prio_seq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "100"), (Infix Left))
let e_app_prio: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10000"), (Infix Left))
let min_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let max_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc))
let rec in_ns x =
  match x with
  | ([],uu____113) -> true
  | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
  | (uu____127,uu____128) -> false
let path_of_ns:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs () in
         let ns_len = FStar_List.length ns in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path  ->
                let cg_len = FStar_List.length cg_path in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu____181 = FStar_Util.first_N cg_len ns in
                  match uu____181 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____201 =
                           let uu____203 =
                             let uu____205 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____205] in
                           FStar_List.append pfx uu____203 in
                         FStar_Pervasives_Native.Some uu____201
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____224 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____224 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____227 ->
          let uu____228 = x in
          (match uu____228 with
           | (ns,x1) ->
               let uu____233 = path_of_ns currentModule ns in (uu____233, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____240 =
      let uu____241 =
        let uu____242 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____242 in
      let uu____243 = FStar_String.get s (Prims.parse_int "0") in
      uu____241 <> uu____243 in
    if uu____240 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____256 = mlpath_of_mlpath currentModule mlp in
         match uu____256 with
         | (p,s) ->
             let uu____261 =
               let uu____263 =
                 let uu____265 = ptsym_of_symbol s in [uu____265] in
               FStar_List.append p uu____263 in
             FStar_String.concat "." uu____261)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____274 = mlpath_of_mlpath currentModule mlp in
      match uu____274 with
      | (p,s) ->
          let s1 =
            let uu____280 =
              let uu____281 =
                let uu____282 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____282 in
              let uu____283 = FStar_String.get s (Prims.parse_int "0") in
              uu____281 <> uu____283 in
            if uu____280 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let infix_prim_ops:
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list
  =
  [("op_Addition", e_bin_prio_op1, "+");
  ("op_Subtraction", e_bin_prio_op1, "-");
  ("op_Multiply", e_bin_prio_op1, "*");
  ("op_Division", e_bin_prio_op1, "/");
  ("op_Equality", e_bin_prio_eq, "=");
  ("op_Colon_Equals", e_bin_prio_eq, ":=");
  ("op_disEquality", e_bin_prio_eq, "<>");
  ("op_AmpAmp", e_bin_prio_and, "&&");
  ("op_BarBar", e_bin_prio_or, "||");
  ("op_LessThanOrEqual", e_bin_prio_order, "<=");
  ("op_GreaterThanOrEqual", e_bin_prio_order, ">=");
  ("op_LessThan", e_bin_prio_order, "<");
  ("op_GreaterThan", e_bin_prio_order, ">");
  ("op_Modulus", e_bin_prio_order, "mod")]
let prim_uni_ops:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("op_Negation", "not");
  ("op_Minus", "~-");
  ("op_Bang", "Support.ST.read")]
let prim_types uu____409 = []
let prim_constructors:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
  =
  fun uu____439  ->
    match uu____439 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____465  ->
               match uu____465 with | (y,uu____472,uu____473) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____488 = as_bin_op p in uu____488 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____512  ->
    match uu____512 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____528  -> match uu____528 with | (y,uu____532) -> x = y)
            prim_uni_ops
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____540 = as_uni_op p in uu____540 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____559  ->
    match uu____559 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____575  -> match uu____575 with | (y,uu____579) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____587 = as_standard_constructor p in
    uu____587 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____611  ->
    fun inner  ->
      fun doc1  ->
        match uu____611 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____644 = _inner in
              match uu____644 with
              | (pi,fi) ->
                  let uu____649 = _outer in
                  (match uu____649 with
                   | (po,fo) ->
                       (pi > po) ||
                         ((match (fi, side1) with
                           | (Postfix ,Left ) -> true
                           | (Prefix ,Right ) -> true
                           | (Infix (Left ),Left ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),Right ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (Infix (Left ),ILeft ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),IRight ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (uu____654,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____655,uu____656) -> false))) in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
let escape_byte_hex: FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let escape_char_hex: FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___118_676  ->
      match uu___118_676 with
      | c when c = '\\' -> "\\\\"
      | c when c = ' ' -> " "
      | c when c = '\b' -> "\\b"
      | c when c = '\t' -> "\\t"
      | c when c = '\r' -> "\\r"
      | c when c = '\n' -> "\\n"
      | c when c = '\'' -> "\\'"
      | c when c = '"' -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let string_of_mlconstant:
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let uu____696 =
          let uu____697 = escape_or escape_char_hex c in
          Prims.strcat uu____697 "'" in
        Prims.strcat "'" uu____696
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____711,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____718,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____733 =
          let uu____734 = FStar_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____734 "\"" in
        Prims.strcat "\"" uu____733
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____736 =
          let uu____737 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____737 "\"" in
        Prims.strcat "\"" uu____736
    | uu____738 ->
        failwith "TODO: extract integer constants properly into OCaml"
let rec doc_of_mltype':
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s '_' 'u'
              else s in
            let uu____760 =
              let uu____761 = FStar_Extraction_ML_Syntax.idsym x in
              FStar_All.pipe_left escape_tyvar uu____761 in
            FStar_Format.text uu____760
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____769 =
                let uu____770 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____770 in
              FStar_Format.parens uu____769 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____779 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____785 =
                    let uu____786 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____786 in
                  FStar_Format.parens uu____785 in
            let name1 = ptsym currentModule name in
            let uu____788 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____788
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____790,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____798 =
              let uu____799 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____799 in
            maybe_paren outer t_prio_fun uu____798
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____800 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____800
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____805 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____805
let rec doc_of_expr:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu____853 = FStar_Extraction_ML_Util.codegen_fsharp () in
            if uu____853
            then
              let uu____854 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.checked_cast"; doc1] in
              FStar_Format.parens uu____854
            else
              (let uu____856 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____856)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs2 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs1 in
            let uu____867 = FStar_Format.reduce docs2 in
            FStar_Format.parens uu____867
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____869 = string_of_mlconstant c in
            FStar_Format.text uu____869
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____872 = ptsym currentModule path in
            FStar_Format.text uu____872
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____888 =
              match uu____888 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____896 =
                    let uu____898 =
                      let uu____899 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____899 in
                    [uu____898; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____896 in
            let uu____901 =
              let uu____902 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____902 in
            FStar_Format.cbrackets uu____901
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____909 = is_standard_constructor ctor in
              if uu____909
              then
                let uu____910 =
                  let uu____913 = as_standard_constructor ctor in
                  FStar_Option.get uu____913 in
                FStar_Pervasives_Native.snd uu____910
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____925 = is_standard_constructor ctor in
              if uu____925
              then
                let uu____926 =
                  let uu____929 = as_standard_constructor ctor in
                  FStar_Option.get uu____929 in
                FStar_Pervasives_Native.snd uu____926
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____945,uu____946) ->
                  let uu____949 =
                    let uu____951 =
                      let uu____953 =
                        let uu____954 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____954 in
                      [uu____953] in
                    (FStar_Format.text name) :: uu____951 in
                  FStar_Format.reduce1 uu____949 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs1 =
              FStar_List.map
                (fun x  ->
                   let uu____962 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____962) es in
            let docs2 =
              let uu____966 =
                FStar_Format.combine (FStar_Format.text ", ") docs1 in
              FStar_Format.parens uu____966 in
            docs2
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____968,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____978 =
                  let uu____980 =
                    let uu____982 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____982] in
                  FStar_Format.hardline :: uu____980 in
                FStar_Format.reduce uu____978
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____989 =
              let uu____990 =
                let uu____992 =
                  let uu____994 =
                    let uu____996 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____996] in
                  doc1 :: uu____994 in
                pre :: uu____992 in
              FStar_Format.combine FStar_Format.hardline uu____990 in
            FStar_Format.parens uu____989
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1003::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1005;
                    FStar_Extraction_ML_Syntax.loc = uu____1006;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1008)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1010;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1011;_}::[])
                 when
                 let uu____1029 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1029 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1042;
                            FStar_Extraction_ML_Syntax.loc = uu____1043;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1045;
                       FStar_Extraction_ML_Syntax.loc = uu____1046;_} when
                       let uu____1057 = FStar_Extraction_ML_Syntax.idsym arg in
                       let uu____1058 = FStar_Extraction_ML_Syntax.idsym arg' in
                       uu____1057 = uu____1058 -> branches
                   | e2 ->
                       [(FStar_Extraction_ML_Syntax.MLP_Wild,
                          FStar_Pervasives_Native.None, e2)] in
                 doc_of_expr currentModule outer
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_Try
                          (scrutinee, branches));
                     FStar_Extraction_ML_Syntax.mlty =
                       (possible_match.FStar_Extraction_ML_Syntax.mlty);
                     FStar_Extraction_ML_Syntax.loc =
                       (possible_match.FStar_Extraction_ML_Syntax.loc)
                   }
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::e2::[]) when
                 is_bin_op p -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____1079;
                   FStar_Extraction_ML_Syntax.loc = uu____1080;_},unitVal::[]),e11::e2::[])
                 when
                 (is_bin_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::[]) when
                 is_uni_op p -> doc_of_uniop currentModule p e11
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____1090;
                   FStar_Extraction_ML_Syntax.loc = uu____1091;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1096 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1107 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1107)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1114 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1114
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1117 =
                   let uu____1119 =
                     let uu____1121 =
                       let uu____1123 =
                         let uu____1124 = ptsym currentModule f in
                         FStar_Format.text uu____1124 in
                       [uu____1123] in
                     (FStar_Format.text ".") :: uu____1121 in
                   e2 :: uu____1119 in
                 FStar_Format.reduce uu____1117) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1142 = FStar_Extraction_ML_Util.codegen_fsharp () in
              if uu____1142
              then
                let uu____1143 =
                  let uu____1145 =
                    let uu____1147 =
                      let uu____1149 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1151 =
                              let uu____1153 =
                                let uu____1155 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1155] in
                              (FStar_Format.text " : ") :: uu____1153 in
                            FStar_Format.reduce1 uu____1151
                        | uu____1156 -> FStar_Format.text "" in
                      [uu____1149; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1147 in
                  (FStar_Format.text "(") :: uu____1145 in
                FStar_Format.reduce1 uu____1143
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1166  ->
                   match uu____1166 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1175 =
                let uu____1177 =
                  let uu____1179 = FStar_Format.reduce1 ids1 in
                  [uu____1179; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1177 in
              FStar_Format.reduce1 uu____1175 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1187 =
                let uu____1189 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1190 =
                  let uu____1192 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1192; FStar_Format.text "end"] in
                uu____1189 :: uu____1190 in
              FStar_Format.combine FStar_Format.hardline uu____1187 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1203 =
                let uu____1205 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1206 =
                  let uu____1208 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1211 =
                    let uu____1213 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1214 =
                      let uu____1216 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1216; FStar_Format.text "end"] in
                    uu____1213 :: uu____1214 in
                  uu____1208 :: uu____1211 in
                uu____1205 :: uu____1206 in
              FStar_Format.combine FStar_Format.hardline uu____1203 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1238 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1238 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1242 =
              let uu____1244 =
                let uu____1246 =
                  let uu____1247 = ptctor currentModule exn in
                  FStar_Format.text uu____1247 in
                [uu____1246] in
              (FStar_Format.text "raise") :: uu____1244 in
            FStar_Format.reduce1 uu____1242
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1256 =
              let uu____1258 =
                let uu____1260 =
                  let uu____1261 = ptctor currentModule exn in
                  FStar_Format.text uu____1261 in
                let uu____1262 =
                  let uu____1264 =
                    let uu____1265 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1265 in
                  [uu____1264] in
                uu____1260 :: uu____1262 in
              (FStar_Format.text "raise") :: uu____1258 in
            FStar_Format.reduce1 uu____1256
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1278 =
              let uu____1280 =
                let uu____1282 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1285 =
                  let uu____1287 =
                    let uu____1289 =
                      let uu____1290 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1290 in
                    [uu____1289] in
                  (FStar_Format.text "with") :: uu____1287 in
                uu____1282 :: uu____1285 in
              (FStar_Format.text "try") :: uu____1280 in
            FStar_Format.combine FStar_Format.hardline uu____1278
and doc_of_binop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1296 =
            let uu____1302 = as_bin_op p in FStar_Option.get uu____1302 in
          match uu____1296 with
          | (uu____1314,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21] in
              FStar_Format.parens doc1
and doc_of_uniop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____1331 =
          let uu____1334 = as_uni_op p in FStar_Option.get uu____1334 in
        match uu____1331 with
        | (uu____1340,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11] in
            FStar_Format.parens doc1
and doc_of_pattern:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____1349 = string_of_mlconstant c in
          FStar_Format.text uu____1349
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____1366 =
            match uu____1366 with
            | (name,p) ->
                let uu____1371 =
                  let uu____1373 =
                    let uu____1374 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____1374 in
                  let uu____1376 =
                    let uu____1378 =
                      let uu____1380 = doc_of_pattern currentModule p in
                      [uu____1380] in
                    (FStar_Format.text "=") :: uu____1378 in
                  uu____1373 :: uu____1376 in
                FStar_Format.reduce1 uu____1371 in
          let uu____1381 =
            let uu____1382 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____1382 in
          FStar_Format.cbrackets uu____1381
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____1389 = is_standard_constructor ctor in
            if uu____1389
            then
              let uu____1390 =
                let uu____1393 = as_standard_constructor ctor in
                FStar_Option.get uu____1393 in
              FStar_Pervasives_Native.snd uu____1390
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____1405 = is_standard_constructor ctor in
            if uu____1405
            then
              let uu____1406 =
                let uu____1409 = as_standard_constructor ctor in
                FStar_Option.get uu____1409 in
              FStar_Pervasives_Native.snd uu____1406
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____1421 =
                  let uu____1423 =
                    let uu____1424 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____1424 in
                  let uu____1425 =
                    let uu____1427 =
                      let uu____1429 = doc_of_pattern currentModule xs in
                      [uu____1429] in
                    (FStar_Format.text "::") :: uu____1427 in
                  uu____1423 :: uu____1425 in
                FStar_Format.reduce uu____1421
            | (uu____1430,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____1431)::[]) ->
                let uu____1434 =
                  let uu____1436 =
                    let uu____1438 =
                      let uu____1439 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____1439 in
                    [uu____1438] in
                  (FStar_Format.text name) :: uu____1436 in
                FStar_Format.reduce1 uu____1434
            | uu____1440 ->
                let uu____1444 =
                  let uu____1446 =
                    let uu____1448 =
                      let uu____1449 =
                        let uu____1450 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____1450 in
                      FStar_Format.parens uu____1449 in
                    [uu____1448] in
                  (FStar_Format.text name) :: uu____1446 in
                FStar_Format.reduce1 uu____1444 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____1458 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____1458
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1466  ->
      match uu____1466 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____1473 =
                  let uu____1475 =
                    let uu____1477 = doc_of_pattern currentModule p in
                    [uu____1477] in
                  (FStar_Format.text "|") :: uu____1475 in
                FStar_Format.reduce1 uu____1473
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____1482 =
                  let uu____1484 =
                    let uu____1486 = doc_of_pattern currentModule p in
                    [uu____1486; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____1484 in
                FStar_Format.reduce1 uu____1482 in
          let uu____1487 =
            let uu____1489 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____1490 =
              let uu____1492 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____1492; FStar_Format.text "end"] in
            uu____1489 :: uu____1490 in
          FStar_Format.combine FStar_Format.hardline uu____1487
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____1496  ->
      match uu____1496 with
      | (rec_,top_level,lets) ->
          let for1 uu____1509 =
            match uu____1509 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1512;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____1523 =
                       (FStar_Extraction_ML_Util.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____1523
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____1524::uu____1525,uu____1526) ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.None  ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some
                              (uu____1541::uu____1542,uu____1543) ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1])
                       else FStar_Format.text "") in
                let uu____1558 =
                  let uu____1560 =
                    let uu____1561 = FStar_Extraction_ML_Syntax.idsym name in
                    FStar_Format.text uu____1561 in
                  let uu____1562 =
                    let uu____1564 = FStar_Format.reduce1 ids in
                    [uu____1564; ty_annot; FStar_Format.text "="; e1] in
                  uu____1560 :: uu____1562 in
                FStar_Format.reduce1 uu____1558 in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let" in
          let lets1 = FStar_List.map for1 lets in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1 in
          FStar_Format.combine FStar_Format.hardline lets2
and doc_of_loc: FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____1576  ->
    match uu____1576 with
    | (lineno,file) ->
        let uu____1579 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Extraction_ML_Util.codegen_fsharp ()) in
        if uu____1579
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
let doc_of_mltydecl:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____1602 =
        match uu____1602 with
        | (uu____1612,x,mangle_opt,tparams,uu____1616,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] ->
                  let uu____1628 = FStar_Extraction_ML_Syntax.idsym x2 in
                  FStar_Format.text uu____1628
              | uu____1629 ->
                  let doc1 =
                    FStar_List.map
                      (fun x2  ->
                         let uu____1636 = FStar_Extraction_ML_Syntax.idsym x2 in
                         FStar_Format.text uu____1636) tparams in
                  let uu____1637 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____1637 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____1654 =
                    match uu____1654 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____1663 =
                    let uu____1664 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____1664 in
                  FStar_Format.cbrackets uu____1663
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____1683 =
                    match uu____1683 with
                    | (name,tys) ->
                        let uu____1697 = FStar_List.split tys in
                        (match uu____1697 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____1708 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1 in
                                  let tys3 =
                                    FStar_Format.combine
                                      (FStar_Format.text " * ") tys2 in
                                  FStar_Format.reduce1
                                    [FStar_Format.text name;
                                    FStar_Format.text "of";
                                    tys3])) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1 in
                  FStar_Format.combine FStar_Format.hardline ctors2 in
            let doc1 =
              let uu____1727 =
                let uu____1729 =
                  let uu____1731 =
                    let uu____1732 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____1732 in
                  [uu____1731] in
                tparams1 :: uu____1729 in
              FStar_Format.reduce1 uu____1727 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____1736 =
                   let uu____1738 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____1738; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____1736) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____1757 =
            let uu____1759 =
              let uu____1761 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____1761] in
            (FStar_Format.text "type") :: uu____1759 in
          FStar_Format.reduce1 uu____1757
        else FStar_Format.text "" in
      doc2
let rec doc_of_sig1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____1777 =
            let uu____1779 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____1780 =
              let uu____1782 = doc_of_sig currentModule subsig in
              let uu____1783 =
                let uu____1785 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____1785] in
              uu____1782 :: uu____1783 in
            uu____1779 :: uu____1780 in
          FStar_Format.combine FStar_Format.hardline uu____1777
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____1797 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____1797 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____1799,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and doc_of_sig:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs1 = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs2 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs1 in
      FStar_Format.reduce docs2
let doc_of_mod1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 =
            let uu____1846 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____1846 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____1849,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____1855 =
            let uu____1857 =
              let uu____1859 =
                let uu____1861 =
                  let uu____1863 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____1863] in
                (FStar_Format.text "=") :: uu____1861 in
              (FStar_Format.text "_") :: uu____1859 in
            (FStar_Format.text "let") :: uu____1857 in
          FStar_Format.reduce1 uu____1855
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs1 =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____1884 ->
                  FStar_Format.empty
              | uu____1885 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs1)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1892  ->
    match uu____1892 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____1930 =
          match uu____1930 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head1 =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"] in
              let tail1 = FStar_Format.reduce1 [FStar_Format.text "end"] in
              let doc1 =
                FStar_Option.map
                  (fun uu____1972  ->
                     match uu____1972 with
                     | (s,uu____1976) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____1992 =
                let uu____1994 =
                  let uu____1996 =
                    let uu____1998 = FStar_Format.reduce sub3 in
                    [uu____1998;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____1996 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____1994 in
              FStar_Format.reduce uu____1992
        and for1_mod istop uu____2001 =
          match uu____2001 with
          | (mod_name,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name in
              let maybe_open_pervasives =
                match mod_name with
                | ("FStar"::[],"Pervasives") -> []
                | uu____2038 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____2045 =
                  let uu____2047 = FStar_Extraction_ML_Util.codegen_fsharp () in
                  if uu____2047
                  then
                    [FStar_Format.text "module";
                    FStar_Format.text target_mod_name]
                  else
                    if Prims.op_Negation istop
                    then
                      [FStar_Format.text "module";
                      FStar_Format.text target_mod_name;
                      FStar_Format.text "=";
                      FStar_Format.text "struct"]
                    else [] in
                FStar_Format.reduce1 uu____2045 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____2061  ->
                     match uu____2061 with
                     | (uu____2064,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____2083 = FStar_Extraction_ML_Util.codegen_fsharp () in
                if uu____2083
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____2086 =
                let uu____2088 =
                  let uu____2090 =
                    let uu____2092 =
                      let uu____2094 =
                        let uu____2096 =
                          let uu____2098 = FStar_Format.reduce sub3 in
                          [uu____2098;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____2096 in
                      FStar_Format.hardline :: uu____2094 in
                    FStar_List.append maybe_open_pervasives uu____2092 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____2090 in
                FStar_List.append prefix1 uu____2088 in
              FStar_All.pipe_left FStar_Format.reduce uu____2086 in
        let docs1 =
          FStar_List.map
            (fun uu____2122  ->
               match uu____2122 with
               | (x,s,m) ->
                   let uu____2149 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____2150 = for1_mod true (x, s, m) in
                   (uu____2149, uu____2150)) mllib in
        docs1
let doc_of_mllib:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib
let string_of_mlexpr:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2173 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____2173 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____2185 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____2185 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1