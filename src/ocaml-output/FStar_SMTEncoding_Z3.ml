
open Prims
open FStar_Pervasives
type z3version =
| Z3V_Unknown of Prims.string
| Z3V of (Prims.int * Prims.int * Prims.int)


let uu___is_Z3V_Unknown : z3version  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_0) -> begin
true
end
| uu____16 -> begin
false
end))


let __proj__Z3V_Unknown__item___0 : z3version  ->  Prims.string = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_0) -> begin
_0
end))


let uu___is_Z3V : z3version  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Z3V (_0) -> begin
true
end
| uu____31 -> begin
false
end))


let __proj__Z3V__item___0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_0) -> begin
_0
end))


let z3version_as_string : z3version  ->  Prims.string = (fun uu___94_50 -> (match (uu___94_50) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(

let uu____55 = (FStar_Util.string_of_int i)
in (

let uu____56 = (FStar_Util.string_of_int j)
in (

let uu____57 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" uu____55 uu____56 uu____57))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int FStar_Pervasives_Native.option = (fun known uu____67 -> (match (uu____67) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (uu____76) -> begin
FStar_Pervasives_Native.None
end
| Z3V (k1, k2, k3) -> begin
FStar_Pervasives_Native.Some ((match ((k1 <> w1)) with
| true -> begin
(w1 - k1)
end
| uu____80 -> begin
(match ((k2 <> w2)) with
| true -> begin
(w2 - k2)
end
| uu____81 -> begin
(w3 - k3)
end)
end))
end)
end))


let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (i) -> begin
(i >= (Prims.parse_int "0"))
end))


let _z3version : z3version FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let get_z3version : Prims.unit  ->  z3version = (fun uu____102 -> (

let prefix1 = "Z3 version "
in (

let uu____104 = (FStar_ST.read _z3version)
in (match (uu____104) with
| FStar_Pervasives_Native.Some (version) -> begin
version
end
| FStar_Pervasives_Native.None -> begin
(

let uu____110 = (

let uu____114 = (FStar_Options.solver_exe ())
in (FStar_Util.run_proc uu____114 "-version" ""))
in (match (uu____110) with
| (uu____115, out, uu____117) -> begin
(

let out1 = (match ((FStar_Util.splitlines out)) with
| (x)::uu____120 when (FStar_Util.starts_with x prefix1) -> begin
(

let x1 = (

let uu____123 = (FStar_Util.substring_from x (FStar_String.length prefix1))
in (FStar_Util.trim_string uu____123))
in (

let x2 = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x1 "."))
end)
with
| uu____133 -> begin
[]
end
in (match (x2) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| uu____137 -> begin
Z3V_Unknown (out)
end)))
end
| uu____139 -> begin
Z3V_Unknown (out)
end)
in ((FStar_ST.write _z3version (FStar_Pervasives_Native.Some (out1)));
out1;
))
end))
end))))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____147 -> (

let uu____148 = (FStar_Options.smt_solver ())
in (match (uu____148) with
| FStar_Options.Z3 -> begin
(

let z3_v = (get_z3version ())
in ((

let uu____151 = (

let uu____152 = (get_z3version ())
in (z3v_le uu____152 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0")))))
in (match (uu____151) with
| true -> begin
(

let uu____153 = (

let uu____154 = (

let uu____155 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" uu____155))
in FStar_Util.Failure (uu____154))
in (FStar_All.pipe_left FStar_Pervasives.raise uu____153))
end
| uu____156 -> begin
()
end));
(

let uu____157 = (

let uu____159 = (

let uu____161 = (

let uu____163 = (

let uu____165 = (

let uu____167 = (

let uu____169 = (

let uu____171 = (

let uu____173 = (

let uu____174 = (

let uu____175 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____175))
in (FStar_Util.format1 "smt.random_seed=%s" uu____174))
in (uu____173)::[])
in ("smtlib2_compliant=true")::uu____171)
in ("smt.relevancy=2")::uu____169)
in ("model=true")::uu____167)
in ("auto_config=false")::uu____165)
in ("-in")::uu____163)
in ("-smt2")::uu____161)
in (

let uu____176 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____159 uu____176)))
in (FStar_All.pipe_right uu____157 (FStar_String.concat " ")));
))
end
| FStar_Options.CVC4 -> begin
(

let uu____179 = (

let uu____181 = (FStar_Options.z3_cliopt ())
in (FStar_List.append (("--incremental")::("--mbqi=none")::("--lang smt2")::("--incremental")::[]) uu____181))
in (FStar_All.pipe_right uu____179 (FStar_String.concat " ")))
end)))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list FStar_Pervasives_Native.option

type z3status =
| UNSAT of unsat_core
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list
| KILLED


let uu___is_UNSAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
true
end
| uu____209 -> begin
false
end))


let __proj__UNSAT__item___0 : z3status  ->  unsat_core = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
_0
end))


let uu___is_SAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
true
end
| uu____222 -> begin
false
end))


let __proj__SAT__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
_0
end))


let uu___is_UNKNOWN : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
true
end
| uu____238 -> begin
false
end))


let __proj__UNKNOWN__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
_0
end))


let uu___is_TIMEOUT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
true
end
| uu____254 -> begin
false
end))


let __proj__TIMEOUT__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
_0
end))


let uu___is_KILLED : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| KILLED -> begin
true
end
| uu____268 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_to_string : z3status  ->  Prims.string = (fun uu___95_272 -> (match (uu___95_272) with
| SAT (uu____273) -> begin
"sat"
end
| UNSAT (uu____275) -> begin
"unsat"
end
| UNKNOWN (uu____276) -> begin
"unknown"
end
| TIMEOUT (uu____278) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____282 -> (

let uu____283 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____283 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let uu____295 = (FStar_Options.solver_exe ())
in (

let uu____296 = (ini_params ())
in (FStar_Util.start_process id uu____295 uu____296 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit; restart : Prims.unit  ->  Prims.unit}

type query_log =
{get_module_name : Prims.unit  ->  Prims.string; set_module_name : Prims.string  ->  Prims.unit; write_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let query_logging : query_log = (

let query_number = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let log_file_opt = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let current_file_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_module_name = (fun n1 -> (FStar_ST.write current_module_name (FStar_Pervasives_Native.Some (n1))))
in (

let get_module_name = (fun uu____480 -> (

let uu____481 = (FStar_ST.read current_module_name)
in (match (uu____481) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____490 -> (

let uu____491 = (FStar_ST.read current_module_name)
in (match (uu____491) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____498 = (

let uu____502 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun uu____513 -> (match (uu____513) with
| (m, uu____517) -> begin
(n1 = m)
end)) uu____502))
in (match (uu____498) with
| FStar_Pervasives_Native.None -> begin
((

let uu____521 = (

let uu____525 = (FStar_ST.read used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____525)
in (FStar_ST.write used_file_names uu____521));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____541, k) -> begin
((

let uu____546 = (

let uu____550 = (FStar_ST.read used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____550)
in (FStar_ST.write used_file_names uu____546));
(

let uu____566 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____566));
)
end))
in (

let file_name1 = (FStar_Util.format1 "queries-%s.smt2" file_name)
in ((FStar_ST.write current_file_name (FStar_Pervasives_Native.Some (file_name1)));
(

let fh = (FStar_Util.open_file_for_writing file_name1)
in ((FStar_ST.write log_file_opt (FStar_Pervasives_Native.Some (fh)));
fh;
));
)))
end)))
in (

let get_log_file = (fun uu____580 -> (

let uu____581 = (FStar_ST.read log_file_opt)
in (match (uu____581) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____591 = (get_log_file ())
in (FStar_Util.append_to_file uu____591 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____597 = (FStar_ST.read current_file_name)
in (match (uu____597) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____603 = (FStar_ST.read current_module_name)
in (match (uu____603) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_Util.format1 "queries-%s" n1)
end))
in ((FStar_Util.mkdir true dir_name);
(FStar_ST.write current_file_name (FStar_Pervasives_Native.Some (dir_name)));
dir_name;
))
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end))
in (

let qnum = (FStar_ST.read query_number)
in ((

let uu____619 = (

let uu____620 = (FStar_ST.read query_number)
in (uu____620 + (Prims.parse_int "1")))
in (FStar_ST.write query_number uu____619));
(

let file_name = (

let uu____626 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____626))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____632 = (

let uu____633 = (FStar_Options.n_cores ())
in (uu____633 > (Prims.parse_int "1")))
in (match (uu____632) with
| true -> begin
(write_to_new_log str)
end
| uu____634 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____638 -> (

let uu____639 = (FStar_ST.read log_file_opt)
in (match (uu____639) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.write log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____652 -> (

let uu____653 = (FStar_ST.read current_file_name)
in (match (uu____653) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____670 -> (

let uu____671 = (

let uu____672 = ((FStar_Util.incr ctr);
(

let uu____677 = (FStar_ST.read ctr)
in (FStar_All.pipe_right uu____677 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____672))
in (new_z3proc uu____671))))
in (

let z3proc = (fun uu____683 -> ((

let uu____685 = (

let uu____686 = (FStar_ST.read the_z3proc)
in (uu____686 = FStar_Pervasives_Native.None))
in (match (uu____685) with
| true -> begin
(

let uu____692 = (

let uu____694 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____694))
in (FStar_ST.write the_z3proc uu____692))
end
| uu____698 -> begin
()
end));
(

let uu____699 = (FStar_ST.read the_z3proc)
in (FStar_Util.must uu____699));
))
in (

let x = []
in (

let grab = (fun uu____709 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____715 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____720 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____724 = (

let uu____726 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____726))
in (FStar_ST.write the_z3proc uu____724));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____734 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.write the_z3proc FStar_Pervasives_Native.None);
(

let uu____742 = (

let uu____744 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____744))
in (FStar_ST.write the_z3proc uu____742));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____750 -> (

let uu____751 = (FStar_Options.log_queries ())
in (match (uu____751) with
| true -> begin
(

let uu____752 = (query_logging.log_file_name ())
in (Prims.strcat "__" uu____752))
end
| uu____753 -> begin
""
end)))


let doZ3Exe' : Prims.bool  ->  Prims.string  ->  (z3status * z3statistics) = (fun fresh1 input -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let get_data = (fun lines1 -> (

let parse_core = (fun s -> (

let s1 = (FStar_Util.trim_string s)
in (

let s2 = (FStar_Util.substring s1 (Prims.parse_int "1") ((FStar_String.length s1) - (Prims.parse_int "2")))
in (match ((FStar_Util.starts_with s2 "error")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____795 -> begin
(

let uu____796 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right uu____796 (fun _0_28 -> FStar_Pervasives_Native.Some (_0_28))))
end))))
in (

let core = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let statistics = (FStar_Util.smap_create (Prims.parse_int "0"))
in (

let reason_unknown = (FStar_Util.mk_ref "")
in (

let in_core = (FStar_Util.mk_ref false)
in (

let in_statistics = (FStar_Util.mk_ref false)
in (

let in_reason_unknown = (FStar_Util.mk_ref false)
in (

let parse = (fun line -> (match (line) with
| "<unsat-core>" -> begin
(FStar_ST.write in_core true)
end
| "<statistics>" -> begin
(FStar_ST.write in_statistics true)
end
| "<reason-unknown>" -> begin
(FStar_ST.write in_reason_unknown true)
end
| "</unsat-core>" -> begin
(FStar_ST.write in_core false)
end
| "</statistics>" -> begin
(FStar_ST.write in_statistics false)
end
| "</reason-unknown>" -> begin
(FStar_ST.write in_reason_unknown false)
end
| uu____841 -> begin
(

let uu____842 = (FStar_ST.read in_core)
in (match (uu____842) with
| true -> begin
(

let uu____845 = (parse_core line)
in (FStar_ST.write core uu____845))
end
| uu____852 -> begin
(

let uu____853 = (FStar_ST.read in_statistics)
in (match (uu____853) with
| true -> begin
(

let pline = (FStar_Util.split (FStar_Util.trim_string line) ":")
in (match (pline) with
| ("(")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____870 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| ("")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____883 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____884 -> begin
()
end))
end
| uu____886 -> begin
(

let uu____887 = (FStar_ST.read in_reason_unknown)
in (match (uu____887) with
| true -> begin
(

let tkns = (FStar_Util.split line "\"")
in (

let rsn = (match (tkns) with
| (uu____893)::(txt)::(uu____895)::[] -> begin
txt
end
| uu____896 -> begin
line
end)
in (match ((rsn <> "unknown")) with
| true -> begin
(FStar_Util.smap_add statistics "reason-unknown" (Prims.strcat "\"" (Prims.strcat rsn "\"")))
end
| uu____898 -> begin
()
end)))
end
| uu____899 -> begin
()
end))
end))
end))
end))
in ((FStar_List.iter (fun line -> (parse line)) lines1);
(

let uu____902 = (FStar_ST.read core)
in (

let uu____909 = (FStar_ST.read reason_unknown)
in ((uu____902), (statistics), (uu____909))));
))))))))))
in (

let rec lblnegs = (fun lines1 -> (match (lines1) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____925 = (lblnegs rest)
in (lname)::uu____925)
end
| (lname)::(uu____928)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____931 -> begin
[]
end))
in (

let rec result = (fun lines1 core -> (match (lines1) with
| ("timeout")::tl1 -> begin
TIMEOUT ([])
end
| ("unknown")::tl1 -> begin
(

let uu____946 = (lblnegs tl1)
in UNKNOWN (uu____946))
end
| ("sat")::tl1 -> begin
(

let uu____950 = (lblnegs tl1)
in SAT (uu____950))
end
| ("unsat")::tl1 -> begin
UNSAT (core)
end
| ("killed")::tl1 -> begin
((bg_z3_proc.restart ());
KILLED;
)
end
| ("success")::tl1 -> begin
(result tl1 core)
end
| (hd1)::tl1 -> begin
((

let uu____963 = (

let uu____964 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____964 hd1))
in (FStar_Errors.warn FStar_Range.dummyRange uu____963));
(result tl1 core);
)
end
| uu____965 -> begin
(

let uu____967 = (

let uu____968 = (

let uu____969 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines1)
in (FStar_String.concat "\n" uu____969))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" uu____968))
in (FStar_All.pipe_left failwith uu____967))
end))
in (

let uu____972 = (get_data lines)
in (match (uu____972) with
| (core, statistics, reason_unknown) -> begin
(

let uu____987 = (result lines core)
in ((uu____987), (statistics)))
end)))))))
in (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let stdout1 = (match (fresh1) with
| true -> begin
(

let uu____997 = (tid ())
in (

let uu____998 = (FStar_Options.solver_exe ())
in (

let uu____999 = (ini_params ())
in (FStar_Util.launch_process uu____997 uu____998 uu____999 input cond))))
end
| uu____1000 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * z3statistics) = (fun fresh1 input -> (doZ3Exe' fresh1 input))

type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

type error_kind =
| Timeout
| Kill
| Default


let uu___is_Timeout : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Timeout -> begin
true
end
| uu____1066 -> begin
false
end))


let uu___is_Kill : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kill -> begin
true
end
| uu____1070 -> begin
false
end))


let uu___is_Default : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Default -> begin
true
end
| uu____1074 -> begin
false
end))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) = (fun fresh1 label_messages input uu____1131 -> (

let ekind = (fun uu___96_1142 -> (match (uu___96_1142) with
| TIMEOUT (uu____1143) -> begin
Timeout
end
| SAT (uu____1145) -> begin
Default
end
| UNKNOWN (uu____1147) -> begin
Default
end
| KILLED -> begin
Kill
end
| uu____1149 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let uu____1151 = (doZ3Exe fresh1 input)
in (match (uu____1151) with
| (status, statistics) -> begin
(

let uu____1163 = (

let uu____1166 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____1166))
in (match (uu____1163) with
| (uu____1174, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time), (statistics))
end
| KILLED -> begin
((FStar_Util.Inr ((([]), (Kill)))), (elapsed_time), (statistics))
end
| TIMEOUT (lblnegs) -> begin
((

let uu____1254 = (FStar_Options.debug_any ())
in (match (uu____1254) with
| true -> begin
(

let uu____1255 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____1255))
end
| uu____1256 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____1277 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____1295 -> (match (uu____1295) with
| (m, uu____1302, uu____1303) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____1277) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____1348 = (

let uu____1359 = (

let uu____1368 = (ekind status)
in ((failing_assertions), (uu____1368)))
in FStar_Util.Inr (uu____1359))
in ((uu____1348), (elapsed_time), (statistics))));
)
end
| SAT (lblnegs) -> begin
((

let uu____1396 = (FStar_Options.debug_any ())
in (match (uu____1396) with
| true -> begin
(

let uu____1397 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____1397))
end
| uu____1398 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____1419 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____1437 -> (match (uu____1437) with
| (m, uu____1444, uu____1445) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____1419) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____1490 = (

let uu____1501 = (

let uu____1510 = (ekind status)
in ((failing_assertions), (uu____1510)))
in FStar_Util.Inr (uu____1501))
in ((uu____1490), (elapsed_time), (statistics))));
)
end
| UNKNOWN (lblnegs) -> begin
((

let uu____1538 = (FStar_Options.debug_any ())
in (match (uu____1538) with
| true -> begin
(

let uu____1539 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____1539))
end
| uu____1540 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____1561 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____1579 -> (match (uu____1579) with
| (m, uu____1586, uu____1587) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____1561) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____1632 = (

let uu____1643 = (

let uu____1652 = (ekind status)
in ((failing_assertions), (uu____1652)))
in FStar_Util.Inr (uu____1643))
in ((uu____1632), (elapsed_time), (statistics))));
)
end)
in result)
end))
end)))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____1686 -> (

let j = (

let uu____1688 = (FStar_ST.read job_queue)
in (match (uu____1688) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::tl1 -> begin
((FStar_ST.write job_queue tl1);
hd1;
)
end))
in ((FStar_Util.incr pending_jobs);
(FStar_Util.monitor_exit job_queue);
(run_job j);
(with_monitor job_queue (fun uu____1715 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____1720 -> (

let uu____1721 = (FStar_ST.read running)
in if uu____1721 then begin
(

let rec aux = (fun uu____1727 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____1733 = (FStar_ST.read job_queue)
in (match (uu____1733) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____1744 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____1747 = (j.job ())
in (FStar_All.pipe_left j.callback uu____1747)))


let init : Prims.unit  ->  Prims.unit = (fun uu____1778 -> ((FStar_ST.write running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____1787 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____1789 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____1799 = (

let uu____1801 = (FStar_ST.read job_queue)
in (FStar_List.append uu____1801 ((j)::[])))
in (FStar_ST.write job_queue uu____1799));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____1820 -> (

let rec aux = (fun uu____1824 -> (

let uu____1825 = (with_monitor job_queue (fun uu____1834 -> (

let uu____1835 = (FStar_ST.read pending_jobs)
in (

let uu____1838 = (

let uu____1839 = (FStar_ST.read job_queue)
in (FStar_List.length uu____1839))
in ((uu____1835), (uu____1838))))))
in (match (uu____1825) with
| (n1, m) -> begin
(match (((n1 + m) = (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.write running false)
end
| uu____1853 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____1868 -> (FStar_ST.read fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____1882 = (

let uu____1885 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____1885)
in (FStar_ST.write fresh_scope uu____1882));
(

let uu____1897 = (

let uu____1899 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____1899 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.write bg_scope uu____1897));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____1911 = (

let uu____1914 = (FStar_ST.read fresh_scope)
in (FStar_List.tl uu____1914))
in (FStar_ST.write fresh_scope uu____1911));
(

let uu____1926 = (

let uu____1928 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____1928 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.write bg_scope uu____1926));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___97_1943 -> (match (uu___97_1943) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____1944 -> begin
()
end))));
(

let uu____1946 = (FStar_ST.read fresh_scope)
in (match (uu____1946) with
| (hd1)::tl1 -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____1964 -> begin
(failwith "Impossible")
end));
(

let uu____1967 = (

let uu____1969 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____1969 decls))
in (FStar_ST.write bg_scope uu____1967));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____1979 -> ((

let uu____1981 = (

let uu____1982 = (FStar_Options.n_cores ())
in (uu____1982 < (Prims.parse_int "2")))
in (match (uu____1981) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____1983 -> begin
()
end));
(

let uu____1984 = (

let uu____1986 = (

let uu____1989 = (FStar_ST.read fresh_scope)
in (FStar_List.rev uu____1989))
in (FStar_List.flatten uu____1986))
in (FStar_ST.write bg_scope uu____1984));
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((pop msg);
(refresh ());
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let uu____2010 = (FStar_ST.read fresh_scope)
in (match (uu____2010) with
| (hd1)::(s)::tl1 -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd1 s))::tl1))
end
| uu____2031 -> begin
(failwith "Impossible")
end)))


let mk_cb = (fun used_unsat_core cb uu____2079 -> (match (uu____2079) with
| (uc_errs, time, statistics) -> begin
(match (used_unsat_core) with
| true -> begin
(match (uc_errs) with
| FStar_Util.Inl (uu____2111) -> begin
(cb ((uc_errs), (time), (statistics)))
end
| FStar_Util.Inr (uu____2120, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time), (statistics)))
end)
end
| uu____2136 -> begin
(cb ((uc_errs), (time), (statistics)))
end)
end))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string = (fun theory -> (

let r = (

let uu____2148 = (FStar_List.map FStar_SMTEncoding_Term.declToSmt theory)
in (FStar_All.pipe_right uu____2148 (FStar_String.concat "\n")))
in ((

let uu____2152 = (FStar_Options.log_queries ())
in (match (uu____2152) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____2153 -> begin
()
end));
r;
)))


type z3result =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics)


type cb =
z3result  ->  Prims.unit


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry cb -> (

let theory = (

let uu____2188 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____2188 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____2193 = (filter_theory theory)
in (match (uu____2193) with
| (theory1, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory1)
in ((FStar_ST.write bg_scope []);
(run_job {job = (z3_job false label_messages input); callback = cb1});
)))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry scope cb -> (

let theory = (

let uu____2253 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.write bg_scope []);
(

let uu____2264 = (FStar_ST.read fresh_scope)
in (FStar_List.rev uu____2264));
)
end)
in (FStar_List.flatten uu____2253))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____2274 = (filter_theory theory1)
in (match (uu____2274) with
| (theory2, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory2)
in (enqueue {job = (z3_job true label_messages input); callback = cb1})))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 label_messages qry scope cb -> (

let uu____2329 = (

let uu____2330 = (FStar_Options.n_cores ())
in (uu____2330 = (Prims.parse_int "1")))
in (match (uu____2329) with
| true -> begin
(ask_1_core filter1 label_messages qry cb)
end
| uu____2333 -> begin
(ask_n_cores filter1 label_messages qry scope cb)
end)))




