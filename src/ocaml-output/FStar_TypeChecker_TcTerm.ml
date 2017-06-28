
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___89_5 = env
in {FStar_TypeChecker_Env.solver = uu___89_5.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___89_5.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___89_5.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___89_5.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___89_5.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___89_5.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___89_5.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___89_5.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___89_5.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___89_5.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___89_5.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___89_5.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___89_5.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___89_5.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___89_5.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___89_5.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___89_5.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___89_5.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___89_5.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___89_5.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___89_5.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___89_5.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___89_5.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___89_5.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___89_5.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___89_5.FStar_TypeChecker_Env.is_native_tactic}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___90_10 = env
in {FStar_TypeChecker_Env.solver = uu___90_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___90_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___90_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___90_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___90_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___90_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___90_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___90_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___90_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___90_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___90_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___90_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___90_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___90_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___90_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___90_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___90_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___90_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___90_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___90_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___90_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___90_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___90_10.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___90_10.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___90_10.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___90_10.FStar_TypeChecker_Env.is_native_tactic}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____40 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____41 = (

let uu____42 = (

let uu____43 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____44 = (

let uu____46 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____46)::[])
in (uu____43)::uu____44))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____42))
in (uu____41 (FStar_Pervasives_Native.Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___84_55 -> (match (uu___84_55) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____57 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| uu____112 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____115 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____118 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____118) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____123 -> begin
(

let fail = (fun uu____127 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____129 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____129))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____131 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____132 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____131 uu____132)))
end)
in (

let uu____133 = (

let uu____134 = (

let uu____137 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____137)))
in FStar_Errors.Error (uu____134))
in (FStar_Pervasives.raise uu____133))))
in (

let s = (

let uu____139 = (

let uu____140 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____140))
in (FStar_TypeChecker_Util.new_uvar env uu____139))
in (

let uu____145 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____145) with
| FStar_Pervasives_Native.Some (g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
s;
)
end
| uu____149 -> begin
(fail ())
end))))
end)
end))))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____186 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____186) with
| true -> begin
s
end
| uu____187 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let uu___91_202 = lc
in {FStar_Syntax_Syntax.eff_name = uu___91_202.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___91_202.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____205 -> (

let uu____206 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ uu____206 t)))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> ((FStar_ST.write e.FStar_Syntax_Syntax.tk (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)));
e;
))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (

let uu____251 = (

let uu____252 = (FStar_Syntax_Subst.compress t)
in uu____252.FStar_Syntax_Syntax.n)
in (match (uu____251) with
| FStar_Syntax_Syntax.Tm_arrow (uu____255, c) -> begin
(

let uu____267 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c))
in (match (uu____267) with
| true -> begin
(

let t1 = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (

let uu____269 = (

let uu____270 = (FStar_Syntax_Subst.compress t1)
in uu____270.FStar_Syntax_Syntax.n)
in (match (uu____269) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____274) -> begin
false
end
| uu____275 -> begin
true
end)))
end
| uu____276 -> begin
false
end))
end
| uu____277 -> begin
true
end)))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____280 = (

let uu____283 = ((

let uu____286 = (should_return t)
in (not (uu____286))) || (

let uu____288 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____288))))
in (match (uu____283) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____291 -> begin
(FStar_TypeChecker_Util.return_value env t e)
end))
in (FStar_Syntax_Util.lcomp_of_comp uu____280))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____296 = (

let uu____300 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____300) with
| FStar_Pervasives_Native.None -> begin
(

let uu____305 = (memo_tk e t)
in ((uu____305), (lc), (guard)))
end
| FStar_Pervasives_Native.Some (t') -> begin
((

let uu____308 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____308) with
| true -> begin
(

let uu____309 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____310 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" uu____309 uu____310)))
end
| uu____311 -> begin
()
end));
(

let uu____312 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____312) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____323 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____323) with
| (e2, g) -> begin
((

let uu____332 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____332) with
| true -> begin
(

let uu____333 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____334 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____335 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____336 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____333 uu____334 uu____335 uu____336)))))
end
| uu____337 -> begin
()
end));
(

let msg = (

let uu____342 = (FStar_TypeChecker_Rel.is_trivial g)
in (match (uu____342) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____348 -> begin
(FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let uu____357 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc1 g1)
in (match (uu____357) with
| (lc2, g2) -> begin
(

let uu____365 = (memo_tk e2 t')
in ((uu____365), ((set_lcomp_result lc2 t')), (g2)))
end))));
)
end)))
end));
)
end))
in (match (uu____296) with
| (e1, lc1, g) -> begin
((

let uu____373 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____373) with
| true -> begin
(

let uu____374 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (FStar_Util.print1 "Return comp type is %s\n" uu____374))
end
| uu____375 -> begin
()
end));
((e1), (lc1), (g));
)
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____394 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____394) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____400 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____400) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt uu____425 -> (match (uu____425) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____445 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____445) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____446 -> begin
(

let uu____447 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____447) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____448 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____449 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____456) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____458 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____460 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____460)))))
in (match (uu____458) with
| true -> begin
(

let uu____464 = (

let uu____466 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____466))
in ((uu____464), (c)))
end
| uu____468 -> begin
(

let uu____469 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____469) with
| true -> begin
(

let uu____473 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____473)))
end
| uu____475 -> begin
(

let uu____476 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____476) with
| true -> begin
(

let uu____480 = (

let uu____482 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____482))
in ((uu____480), (c)))
end
| uu____484 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____449) with
| (expected_c_opt, c1) -> begin
(

let c2 = (norm_c env c1)
in (match (expected_c_opt) with
| FStar_Pervasives_Native.None -> begin
((e), (c2), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (expected_c) -> begin
(

let uu____498 = (FStar_TypeChecker_Util.check_comp env e c2 expected_c)
in (match (uu____498) with
| (e1, uu____506, g) -> begin
(

let g1 = (

let uu____509 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____509 "could not prove post-condition" g))
in ((

let uu____511 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____511) with
| true -> begin
(

let uu____512 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____513 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" uu____512 uu____513)))
end
| uu____514 -> begin
()
end));
(

let e2 = (FStar_TypeChecker_Util.maybe_lift env e1 (FStar_Syntax_Util.comp_effect_name c2) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c2))
in ((e2), (expected_c), (g1)));
))
end))
end))
end)))
end))


let no_logical_guard = (fun env uu____539 -> (match (uu____539) with
| (te, kt, f) -> begin
(

let uu____546 = (FStar_TypeChecker_Rel.guard_form f)
in (match (uu____546) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____551 = (

let uu____552 = (

let uu____555 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____556 = (FStar_TypeChecker_Env.get_range env)
in ((uu____555), (uu____556))))
in FStar_Errors.Error (uu____552))
in (FStar_Pervasives.raise uu____551))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (

let uu____564 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____564) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____567 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____567))
end)))


let check_smt_pat = (fun env t bs c -> (

let uu____608 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____608) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____609; FStar_Syntax_Syntax.effect_name = uu____610; FStar_Syntax_Syntax.result_typ = uu____611; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____615))::[]; FStar_Syntax_Syntax.flags = uu____616}) -> begin
(

let pat_vars = (

let uu____650 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names uu____650))
in (

let uu____651 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____667 -> (match (uu____667) with
| (b, uu____671) -> begin
(

let uu____672 = (FStar_Util.set_mem b pat_vars)
in (not (uu____672)))
end))))
in (match (uu____651) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____676) -> begin
(

let uu____679 = (

let uu____680 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____680))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____679))
end)))
end
| uu____681 -> begin
(failwith "Impossible")
end)
end
| uu____682 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (

let uu____705 = (

let uu____706 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____706)))
in (match (uu____705) with
| true -> begin
env.FStar_TypeChecker_Env.letrecs
end
| uu____710 -> begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___92_724 = env
in {FStar_TypeChecker_Env.solver = uu___92_724.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___92_724.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___92_724.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___92_724.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___92_724.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___92_724.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___92_724.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___92_724.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___92_724.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___92_724.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___92_724.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___92_724.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___92_724.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___92_724.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___92_724.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___92_724.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___92_724.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___92_724.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___92_724.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___92_724.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___92_724.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___92_724.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___92_724.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___92_724.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___92_724.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___92_724.FStar_TypeChecker_Env.is_native_tactic})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____752 -> (match (uu____752) with
| (b, uu____757) -> begin
(

let t = (

let uu____759 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____759))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____761) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____762) -> begin
[]
end
| uu____770 -> begin
(

let uu____771 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____771)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____776 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____776) with
| (head1, uu____787) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____803 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____806 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___85_812 -> (match (uu___85_812) with
| FStar_Syntax_Syntax.DECREASES (uu____813) -> begin
true
end
| uu____816 -> begin
false
end))))
in (match (uu____806) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____820 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____826 -> begin
(mk_lex_list xs)
end))
end))))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____838 -> (match (uu____838) with
| (l, t) -> begin
(

let uu____847 = (

let uu____848 = (FStar_Syntax_Subst.compress t)
in uu____848.FStar_Syntax_Syntax.n)
in (match (uu____847) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____886 -> (match (uu____886) with
| (x, imp) -> begin
(

let uu____893 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____893) with
| true -> begin
(

let uu____896 = (

let uu____897 = (

let uu____899 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____899))
in (FStar_Syntax_Syntax.new_bv uu____897 x.FStar_Syntax_Syntax.sort))
in ((uu____896), (imp)))
end
| uu____900 -> begin
((x), (imp))
end))
end))))
in (

let uu____901 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____901) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____914 = (

let uu____915 = (

let uu____916 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____917 = (

let uu____919 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____919)::[])
in (uu____916)::uu____917))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____915))
in (uu____914 FStar_Pervasives_Native.None r))
in (

let uu____924 = (FStar_Util.prefix formals2)
in (match (uu____924) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___93_950 = last1
in (

let uu____951 = (FStar_Syntax_Util.refine last1 precedes1)
in {FStar_Syntax_Syntax.ppname = uu___93_950.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___93_950.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____951}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____968 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____968) with
| true -> begin
(

let uu____969 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____970 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____971 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____969 uu____970 uu____971))))
end
| uu____972 -> begin
()
end));
((l), (t'));
))))
end))))
end)))
end
| uu____975 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let uu___94_1259 = env
in {FStar_TypeChecker_Env.solver = uu___94_1259.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___94_1259.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___94_1259.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___94_1259.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___94_1259.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___94_1259.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___94_1259.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___94_1259.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___94_1259.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___94_1259.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___94_1259.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___94_1259.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___94_1259.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___94_1259.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___94_1259.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___94_1259.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___94_1259.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___94_1259.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___94_1259.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___94_1259.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___94_1259.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___94_1259.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___94_1259.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___94_1259.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___94_1259.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___94_1259.FStar_TypeChecker_Env.is_native_tactic}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____1266 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in ((

let uu____1268 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1268) with
| true -> begin
(

let uu____1269 = (

let uu____1270 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1270))
in (

let uu____1271 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" uu____1269 uu____1271)))
end
| uu____1272 -> begin
()
end));
(

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1277) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1295) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1300) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1311) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____1312) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1313) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____1314) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1315) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1325) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____1333) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____1338) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____1344 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____1344) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___95_1355 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___95_1355.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___95_1355.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___95_1355.FStar_TypeChecker_Env.implicits})
in ((e2), (c), (g1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____1368 = (FStar_Syntax_Util.type_u ())
in (match (uu____1368) with
| (t, u) -> begin
(

let uu____1376 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____1376) with
| (e2, c, g) -> begin
(

let uu____1386 = (

let uu____1395 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1395) with
| (env2, uu____1408) -> begin
(tc_pats env2 pats)
end))
in (match (uu____1386) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___96_1429 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___96_1429.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___96_1429.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___96_1429.FStar_TypeChecker_Env.implicits})
in (

let uu____1430 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1437 = (FStar_TypeChecker_Rel.conj_guard g g'1)
in ((uu____1430), (c), (uu____1437)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____1445 = (

let uu____1446 = (FStar_Syntax_Subst.compress e1)
in uu____1446.FStar_Syntax_Syntax.n)
in (match (uu____1445) with
| FStar_Syntax_Syntax.Tm_let ((uu____1452, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____1454; FStar_Syntax_Syntax.lbtyp = uu____1455; FStar_Syntax_Syntax.lbeff = uu____1456; FStar_Syntax_Syntax.lbdef = e11})::[]), e2) -> begin
(

let uu____1474 = (

let uu____1478 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_TypeChecker_Common.t_unit)
in (tc_term uu____1478 e11))
in (match (uu____1474) with
| (e12, c1, g1) -> begin
(

let uu____1485 = (tc_term env1 e2)
in (match (uu____1485) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____1502 = (

let uu____1505 = (

let uu____1506 = (

let uu____1514 = (

let uu____1518 = (

let uu____1520 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e13)))
in (uu____1520)::[])
in ((false), (uu____1518)))
in ((uu____1514), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____1506))
in (FStar_Syntax_Syntax.mk uu____1505))
in (uu____1502 (FStar_Pervasives_Native.Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (FStar_Pervasives_Native.Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____1546 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e5), (c), (uu____1546)))))))))
end))
end))
end
| uu____1549 -> begin
(

let uu____1550 = (tc_term env1 e1)
in (match (uu____1550) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (FStar_Pervasives_Native.Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____1570)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____1585 = (tc_term env1 e1)
in (match (uu____1585) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) (FStar_Pervasives_Native.Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____1607) -> begin
(

let uu____1643 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____1643) with
| (env0, uu____1651) -> begin
(

let uu____1654 = (tc_comp env0 expected_c)
in (match (uu____1654) with
| (expected_c1, uu____1662, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c1)
in (

let uu____1667 = (

let uu____1671 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term uu____1671 e1))
in (match (uu____1667) with
| (e2, c', g') -> begin
(

let uu____1678 = (

let uu____1682 = (

let uu____1685 = (c'.FStar_Syntax_Syntax.comp ())
in ((e2), (uu____1685)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____1682))
in (match (uu____1678) with
| (e3, expected_c2, g'') -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (t_res)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) (FStar_Pervasives_Native.Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____1732 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g uu____1732))
in (

let topt1 = (tc_tactic_opt env0 topt)
in (

let f1 = (match (topt1) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Rel.map_guard f (FStar_TypeChecker_Common.mk_by_tactic tactic))
end)
in (

let uu____1737 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____1737) with
| (e5, c, f2) -> begin
(

let uu____1747 = (FStar_TypeChecker_Rel.conj_guard f1 f2)
in ((e5), (c), (uu____1747)))
end)))))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____1751) -> begin
(

let uu____1787 = (FStar_Syntax_Util.type_u ())
in (match (uu____1787) with
| (k, u) -> begin
(

let uu____1795 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____1795) with
| (t1, uu____1803, f) -> begin
(

let uu____1805 = (

let uu____1809 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____1809 e1))
in (match (uu____1805) with
| (e2, c, g) -> begin
(

let uu____1816 = (

let uu____1819 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____1823 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____1819 e2 c f))
in (match (uu____1816) with
| (c1, f1) -> begin
(

let uu____1829 = (

let uu____1833 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) (FStar_Pervasives_Native.Some (t1.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____1833 c1))
in (match (uu____1829) with
| (e3, c2, f2) -> begin
(

let uu____1865 = (

let uu____1866 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____1866))
in ((e3), (c2), (uu____1865)))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____1867; FStar_Syntax_Syntax.pos = uu____1868; FStar_Syntax_Syntax.vars = uu____1869}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____1913 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____1913) with
| (unary_op, uu____1927) -> begin
(

let head1 = (

let uu____1945 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____1945))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____1981)); FStar_Syntax_Syntax.tk = uu____1982; FStar_Syntax_Syntax.pos = uu____1983; FStar_Syntax_Syntax.vars = uu____1984}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____2028 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2028) with
| (unary_op, uu____2042) -> begin
(

let head1 = (

let uu____2060 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) FStar_Pervasives_Native.None uu____2060))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____2096; FStar_Syntax_Syntax.pos = uu____2097; FStar_Syntax_Syntax.vars = uu____2098}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end
| uu____2123 -> begin
()
end);
(

let uu____2124 = (

let uu____2128 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2128) with
| (env0, uu____2136) -> begin
(tc_term env0 e1)
end))
in (match (uu____2124) with
| (e2, c, g) -> begin
(

let uu____2145 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2145) with
| (reify_op, uu____2159) -> begin
(

let u_c = (

let uu____2175 = (tc_term env1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____2175) with
| (uu____2179, c', uu____2181) -> begin
(

let uu____2182 = (

let uu____2183 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____2183.FStar_Syntax_Syntax.n)
in (match (uu____2182) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____2187 -> begin
(

let uu____2188 = (FStar_Syntax_Util.type_u ())
in (match (uu____2188) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2197 = (

let uu____2198 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____2199 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____2200 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____2198 uu____2199 uu____2200))))
in (failwith uu____2197))
end);
u;
))
end))
end))
end))
in (

let repr = (

let uu____2202 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Env.reify_comp env1 uu____2202 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) (FStar_Pervasives_Native.Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____2220 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____2220 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____2221 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____2221) with
| (e4, c2, g') -> begin
(

let uu____2231 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e4), (c2), (uu____2231)))
end))))))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = uu____2233; FStar_Syntax_Syntax.pos = uu____2234; FStar_Syntax_Syntax.vars = uu____2235}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.warn e1.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end
| uu____2260 -> begin
()
end);
(

let no_reflect = (fun uu____2267 -> (

let uu____2268 = (

let uu____2269 = (

let uu____2272 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((uu____2272), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2269))
in (FStar_Pervasives.raise uu____2268)))
in (

let uu____2276 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____2276) with
| (reflect_op, uu____2290) -> begin
(

let uu____2305 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____2305) with
| FStar_Pervasives_Native.None -> begin
(no_reflect ())
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____2323 = (

let uu____2324 = (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable)
in (not (uu____2324)))
in (match (uu____2323) with
| true -> begin
(no_reflect ())
end
| uu____2329 -> begin
(

let uu____2330 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2330) with
| (env_no_ex, topt) -> begin
(

let uu____2341 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____2356 = (

let uu____2359 = (

let uu____2360 = (

let uu____2370 = (

let uu____2372 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____2373 = (

let uu____2375 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____2375)::[])
in (uu____2372)::uu____2373))
in ((repr), (uu____2370)))
in FStar_Syntax_Syntax.Tm_app (uu____2360))
in (FStar_Syntax_Syntax.mk uu____2359))
in (uu____2356 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____2385 = (

let uu____2389 = (

let uu____2390 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____2390 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____2389 t))
in (match (uu____2385) with
| (t1, uu____2407, g) -> begin
(

let uu____2409 = (

let uu____2410 = (FStar_Syntax_Subst.compress t1)
in uu____2410.FStar_Syntax_Syntax.n)
in (match (uu____2409) with
| FStar_Syntax_Syntax.Tm_app (uu____2421, ((res, uu____2423))::((wp, uu____2425))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____2459 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____2341) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____2483 = (

let uu____2486 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____2486) with
| (e2, c, g) -> begin
((

let uu____2496 = (

let uu____2497 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____2497))
in (match (uu____2496) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 (((("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____2502 -> begin
()
end));
(

let uu____2503 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____2503) with
| FStar_Pervasives_Native.None -> begin
((

let uu____2508 = (

let uu____2512 = (

let uu____2515 = (

let uu____2516 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2517 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____2516 uu____2517)))
in ((uu____2515), (e2.FStar_Syntax_Syntax.pos)))
in (uu____2512)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____2508));
(

let uu____2522 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e2), (uu____2522)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____2524 = (

let uu____2525 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' uu____2525))
in ((e2), (uu____2524)))
end));
)
end))
in (match (uu____2483) with
| (e2, g) -> begin
(

let c = (

let uu____2532 = (

let uu____2533 = (

let uu____2534 = (

let uu____2535 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____2535)::[])
in (

let uu____2536 = (

let uu____2542 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2542)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2534; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____2536; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2533))
in (FStar_All.pipe_right uu____2532 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) (FStar_Pervasives_Native.Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let uu____2559 = (comp_check_expected_typ env1 e3 c)
in (match (uu____2559) with
| (e4, c1, g') -> begin
(

let uu____2569 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e4), (c1), (uu____2569)))
end))))
end))
end))
end))
end))
end))
end)));
)
end
| FStar_Syntax_Syntax.Tm_app (head1, ((tau, uu____2572))::[]) when (FStar_Syntax_Util.is_synth_by_tactic head1) -> begin
(match (env1.FStar_TypeChecker_Env.expected_typ) with
| FStar_Pervasives_Native.Some (typ) -> begin
(tc_synth env1 typ tau)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2598 = (

let uu____2599 = (

let uu____2602 = (FStar_TypeChecker_Env.get_range env1)
in (("synth_by_tactic: need a type annotation when no expected type is present"), (uu____2602)))
in FStar_Errors.Error (uu____2599))
in (FStar_Pervasives.raise uu____2598))
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, ((a, uu____2608))::((tau, uu____2610))::[]) when (FStar_Syntax_Util.is_synth_by_tactic head1) -> begin
(tc_synth env1 a tau)
end
| FStar_Syntax_Syntax.Tm_app (head1, ((a, uu____2642))::(uu____2643)::((tau, uu____2645))::[]) when (FStar_Syntax_Util.is_synth_by_tactic head1) -> begin
(tc_synth env1 a tau)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let env0 = env1
in (

let env2 = (

let uu____2701 = (

let uu____2702 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____2702 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____2701 instantiate_both))
in ((

let uu____2711 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____2711) with
| true -> begin
(

let uu____2712 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____2713 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" uu____2712 uu____2713)))
end
| uu____2714 -> begin
()
end));
(

let isquote = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid) -> begin
true
end
| uu____2717 -> begin
false
end)
in (

let uu____2718 = (tc_term (no_inst env2) head1)
in (match (uu____2718) with
| (head2, chead, g_head) -> begin
(

let uu____2728 = (

let uu____2732 = ((not (env2.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____2732) with
| true -> begin
(

let uu____2736 = (

let uu____2740 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____2740))
in (match (uu____2736) with
| (e1, c, g) -> begin
(

let c1 = (

let uu____2749 = (((FStar_TypeChecker_Env.should_verify env2) && (

let uu____2751 = (FStar_Syntax_Util.is_lcomp_partial_return c)
in (not (uu____2751)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c))
in (match (uu____2749) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e1 c)
end
| uu____2752 -> begin
c
end))
in ((e1), (c1), (g)))
end))
end
| uu____2753 -> begin
(

let env3 = (match (isquote) with
| true -> begin
(no_inst env2)
end
| uu____2755 -> begin
env2
end)
in (

let uu____2756 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env3 head2 chead g_head args uu____2756)))
end))
in (match (uu____2728) with
| (e1, c, g) -> begin
((

let uu____2765 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____2765) with
| true -> begin
(

let uu____2766 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____2766))
end
| uu____2767 -> begin
()
end));
(

let uu____2768 = (comp_check_expected_typ env0 e1 c)
in (match (uu____2768) with
| (e2, c1, g') -> begin
(

let gimp = (

let uu____2779 = (

let uu____2780 = (FStar_Syntax_Subst.compress head2)
in uu____2780.FStar_Syntax_Syntax.n)
in (match (uu____2779) with
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2784) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e2), (c1.FStar_Syntax_Syntax.res_typ), (head2.FStar_Syntax_Syntax.pos))
in (

let uu___97_2824 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___97_2824.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___97_2824.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___97_2824.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| uu____2853 -> begin
FStar_TypeChecker_Rel.trivial_guard
end))
in (

let gres = (

let uu____2855 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g uu____2855))
in ((

let uu____2857 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____2857) with
| true -> begin
(

let uu____2858 = (FStar_Syntax_Print.term_to_string e2)
in (

let uu____2859 = (FStar_TypeChecker_Rel.guard_to_string env2 gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____2858 uu____2859)))
end
| uu____2860 -> begin
()
end));
((e2), (c1), (gres));
)))
end));
)
end))
end)));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____2887 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____2887) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____2899 = (tc_term env12 e1)
in (match (uu____2899) with
| (e11, c1, g1) -> begin
(

let uu____2909 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2915 = (FStar_Syntax_Util.type_u ())
in (match (uu____2915) with
| (k, uu____2921) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env1 k)
in (

let uu____2923 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in ((uu____2923), (res_t))))
end))
end)
in (match (uu____2909) with
| (env_branches, res_t) -> begin
((

let uu____2930 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____2930) with
| true -> begin
(

let uu____2931 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____2931))
end
| uu____2932 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____2980 = (

let uu____2983 = (FStar_List.fold_right (fun uu____3011 uu____3012 -> (match (((uu____3011), (uu____3012))) with
| ((uu____3044, f, c, g), (caccum, gaccum)) -> begin
(

let uu____3077 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (uu____3077)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2983) with
| (cases, g) -> begin
(

let uu____3098 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____3098), (g)))
end))
in (match (uu____2980) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____3159 -> (match (uu____3159) with
| ((pat, wopt, br), uu____3175, lc, uu____3177) -> begin
(

let uu____3184 = (FStar_TypeChecker_Util.maybe_lift env1 br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (uu____3184)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____3232 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____3232) with
| true -> begin
(mk_match e11)
end
| uu____3235 -> begin
(

let e_match = (

let uu____3239 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____3239))
in (

let lb = (

let uu____3243 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = uu____3243; FStar_Syntax_Syntax.lbdef = e11})
in (

let e2 = (

let uu____3247 = (

let uu____3250 = (

let uu____3251 = (

let uu____3259 = (

let uu____3260 = (

let uu____3261 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____3261)::[])
in (FStar_Syntax_Subst.close uu____3260 e_match))
in ((((false), ((lb)::[]))), (uu____3259)))
in FStar_Syntax_Syntax.Tm_let (uu____3251))
in (FStar_Syntax_Syntax.mk uu____3250))
in (uu____3247 (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____3275 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____3275) with
| true -> begin
(

let uu____3276 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3277 = (

let uu____3278 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3278))
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____3276 uu____3277)))
end
| uu____3279 -> begin
()
end));
(

let uu____3280 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e2), (cres), (uu____3280)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____3283); FStar_Syntax_Syntax.lbunivs = uu____3284; FStar_Syntax_Syntax.lbtyp = uu____3285; FStar_Syntax_Syntax.lbeff = uu____3286; FStar_Syntax_Syntax.lbdef = uu____3287})::[]), uu____3288) -> begin
((

let uu____3303 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____3303) with
| true -> begin
(

let uu____3304 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____3304))
end
| uu____3305 -> begin
()
end));
(check_top_level_let env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____3306), uu____3307) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____3317); FStar_Syntax_Syntax.lbunivs = uu____3318; FStar_Syntax_Syntax.lbtyp = uu____3319; FStar_Syntax_Syntax.lbeff = uu____3320; FStar_Syntax_Syntax.lbdef = uu____3321})::uu____3322), uu____3323) -> begin
((

let uu____3339 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____3339) with
| true -> begin
(

let uu____3340 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" uu____3340))
end
| uu____3341 -> begin
()
end));
(check_top_level_let_rec env1 top);
)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____3342), uu____3343) -> begin
(check_inner_let_rec env1 top)
end));
)))
and tc_synth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env typ tau -> (

let uu____3358 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3358) with
| (env', uu____3366) -> begin
(

let uu____3369 = (tc_term env' typ)
in (match (uu____3369) with
| (typ1, uu____3377, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g1);
(

let uu____3380 = (tc_term env' tau)
in (match (uu____3380) with
| (tau1, c, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env' g2);
(

let uu____3392 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____3392) with
| true -> begin
(

let uu____3393 = (FStar_Syntax_Print.term_to_string tau1)
in (

let uu____3394 = (FStar_Syntax_Print.term_to_string typ1)
in (FStar_Util.print2 "Running tactic %s at return type %s\n" uu____3393 uu____3394)))
end
| uu____3395 -> begin
()
end));
(

let t = (env.FStar_TypeChecker_Env.synth env' typ1 tau1)
in ((

let uu____3398 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____3398) with
| true -> begin
(

let uu____3399 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____3399))
end
| uu____3400 -> begin
()
end));
(FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(tc_term env t);
));
)
end));
)
end))
end)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____3415 = (tc_check_tot_or_gtot_term env tactic FStar_TypeChecker_Common.t_tactic_unit)
in (match (uu____3415) with
| (tactic1, uu____3421, uu____3422) -> begin
FStar_Pervasives_Native.Some (tactic1)
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t -> (

let uu____3451 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____3451) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____3464 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____3464) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____3467 -> begin
(

let uu____3468 = (

let uu____3469 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3469))
in FStar_Util.Inr (uu____3468))
end))
in (

let is_data_ctor = (fun uu___86_3478 -> (match (uu___86_3478) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____3480)) -> begin
true
end
| uu____3484 -> begin
false
end))
in (

let uu____3486 = ((is_data_ctor dc) && (

let uu____3488 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____3488))))
in (match (uu____3486) with
| true -> begin
(

let uu____3492 = (

let uu____3493 = (

let uu____3496 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (

let uu____3497 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____3496), (uu____3497))))
in FStar_Errors.Error (uu____3493))
in (FStar_Pervasives.raise uu____3492))
end
| uu____3501 -> begin
(value_check_expected_typ env1 e2 tc implicits)
end))))
end)))
in (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____3508 = (

let uu____3509 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____3509))
in (failwith uu____3508))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (

let uu____3532 = (

let uu____3533 = (FStar_Syntax_Subst.compress t1)
in uu____3533.FStar_Syntax_Syntax.n)
in (match (uu____3532) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3536) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____3544 -> begin
(

let imp = (("uvar in term"), (env1), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let uu___98_3568 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___98_3568.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___98_3568.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___98_3568.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end))
in (value_check_expected_typ env1 e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____3600 = (

let uu____3607 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____3607) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3615 = (FStar_Syntax_Util.type_u ())
in (match (uu____3615) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (match (uu____3600) with
| (t, uu____3636, g0) -> begin
(

let uu____3644 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____3644) with
| (e1, uu____3655, g1) -> begin
(

let uu____3663 = (

let uu____3664 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____3664 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____3665 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e1), (uu____3663), (uu____3665))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____3667 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____3676 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____3676)))
end
| uu____3679 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____3667) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___99_3692 = x
in {FStar_Syntax_Syntax.ppname = uu___99_3692.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___99_3692.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Common.insert_bv x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____3695 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____3695) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____3708 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____3708) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____3711 -> begin
(

let uu____3712 = (

let uu____3713 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3713))
in FStar_Util.Inr (uu____3712))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3719; FStar_Syntax_Syntax.pos = uu____3720; FStar_Syntax_Syntax.vars = uu____3721}, uu____3722) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____3727 = (

let uu____3728 = (

let uu____3731 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____3731)))
in FStar_Errors.Error (uu____3728))
in (FStar_Pervasives.raise uu____3727))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) -> begin
(

let uu____3736 = (

let uu____3737 = (

let uu____3740 = (FStar_TypeChecker_Env.get_range env1)
in (("Badly instantiated synth_by_tactic"), (uu____3740)))
in FStar_Errors.Error (uu____3737))
in (FStar_Pervasives.raise uu____3736))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____3745; FStar_Syntax_Syntax.pos = uu____3746; FStar_Syntax_Syntax.vars = uu____3747}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____3755 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3755) with
| ((us', t), range) -> begin
((match (((FStar_List.length us1) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____3777 = (

let uu____3778 = (

let uu____3781 = (

let uu____3782 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____3783 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____3790 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____3782 uu____3783 uu____3790))))
in (

let uu____3797 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____3781), (uu____3797))))
in FStar_Errors.Error (uu____3778))
in (FStar_Pervasives.raise uu____3777))
end
| uu____3798 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3809 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Common.insert_fv fv' t);
(

let e1 = (

let uu____3813 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3813 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3819 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3819) with
| ((us, t), range) -> begin
((

let uu____3833 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____3833) with
| true -> begin
(

let uu____3834 = (

let uu____3835 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____3835))
in (

let uu____3836 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____3837 = (FStar_Range.string_of_range range)
in (

let uu____3838 = (FStar_Range.string_of_use_range range)
in (

let uu____3839 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____3834 uu____3836 uu____3837 uu____3838 uu____3839))))))
end
| uu____3840 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Common.insert_fv fv' t);
(

let e1 = (

let uu____3844 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3844 us))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3870 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3870) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____3879 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3879) with
| (env2, uu____3887) -> begin
(

let uu____3890 = (tc_binders env2 bs1)
in (match (uu____3890) with
| (bs2, env3, g, us) -> begin
(

let uu____3902 = (tc_comp env3 c1)
in (match (uu____3902) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___100_3915 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___100_3915.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___100_3915.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___100_3915.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____3932 = (FStar_TypeChecker_Rel.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Rel.conj_guard g uu____3932))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g1))));
))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (tc_universe env1 u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u1))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1)) (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____3959 = (

let uu____3962 = (

let uu____3963 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3963)::[])
in (FStar_Syntax_Subst.open_term uu____3962 phi))
in (match (uu____3959) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____3970 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3970) with
| (env2, uu____3978) -> begin
(

let uu____3981 = (

let uu____3988 = (FStar_List.hd x1)
in (tc_binder env2 uu____3988))
in (match (uu____3981) with
| (x2, env3, f1, u) -> begin
((

let uu____4005 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____4005) with
| true -> begin
(

let uu____4006 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____4007 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____4008 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____4006 uu____4007 uu____4008))))
end
| uu____4009 -> begin
()
end));
(

let uu____4010 = (FStar_Syntax_Util.type_u ())
in (match (uu____4010) with
| (t_phi, uu____4017) -> begin
(

let uu____4018 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____4018) with
| (phi2, uu____4026, f2) -> begin
(

let e1 = (

let uu___101_4031 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___101_4031.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___101_4031.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___101_4031.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____4046 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 uu____4046))
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____4055) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____4070 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4070) with
| true -> begin
(

let uu____4071 = (FStar_Syntax_Print.term_to_string (

let uu___102_4074 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.tk = uu___102_4074.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___102_4074.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___102_4074.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____4071))
end
| uu____4082 -> begin
()
end));
(

let uu____4083 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____4083) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____4091 -> begin
(

let uu____4092 = (

let uu____4093 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____4094 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____4093 uu____4094)))
in (failwith uu____4092))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (uu____4100) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (uu____4101, FStar_Pervasives_Native.None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (uu____4107, FStar_Pervasives_Native.Some (uu____4108)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (uu____4116) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (uu____4120) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (uu____4121) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____4122) -> begin
FStar_TypeChecker_Common.t_range
end
| uu____4123 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____4134) -> begin
(

let uu____4141 = (FStar_Syntax_Util.type_u ())
in (match (uu____4141) with
| (k, u) -> begin
(

let uu____4149 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____4149) with
| (t1, uu____4157, g) -> begin
(

let uu____4159 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____4159), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____4161) -> begin
(

let uu____4168 = (FStar_Syntax_Util.type_u ())
in (match (uu____4168) with
| (k, u) -> begin
(

let uu____4176 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____4176) with
| (t1, uu____4184, g) -> begin
(

let uu____4186 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____4186), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let head1 = (FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let head2 = (match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head1
end
| us -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head1), (us)))) FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (

let uu____4198 = (

let uu____4199 = (

let uu____4200 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____4200)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____4199))
in (uu____4198 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____4205 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____4205) with
| (tc1, uu____4213, f) -> begin
(

let uu____4215 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____4215) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____4245 = (

let uu____4246 = (FStar_Syntax_Subst.compress head3)
in uu____4246.FStar_Syntax_Syntax.n)
in (match (uu____4245) with
| FStar_Syntax_Syntax.Tm_uinst (uu____4249, us) -> begin
us
end
| uu____4255 -> begin
[]
end))
in (

let uu____4256 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____4256) with
| (uu____4269, args1) -> begin
(

let uu____4285 = (

let uu____4297 = (FStar_List.hd args1)
in (

let uu____4306 = (FStar_List.tl args1)
in ((uu____4297), (uu____4306))))
in (match (uu____4285) with
| (res, args2) -> begin
(

let uu____4348 = (

let uu____4353 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___87_4372 -> (match (uu___87_4372) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____4378 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____4378) with
| (env1, uu____4385) -> begin
(

let uu____4388 = (tc_tot_or_gtot_term env1 e)
in (match (uu____4388) with
| (e1, uu____4395, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right uu____4353 FStar_List.unzip))
in (match (uu____4348) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___103_4420 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___103_4420.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___103_4420.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____4424 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____4424) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____4427 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c2), (u_c), (uu____4427))))))
end))
end))
end)))
end))
end)))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (uu____4435) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____4436) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____4442 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____4442))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____4445 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____4445))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u2
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____4448 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____4449 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____4449 FStar_Pervasives_Native.snd))
end
| uu____4454 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (

let uu____4475 = (

let uu____4476 = (

let uu____4479 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((uu____4479), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4476))
in (FStar_Pervasives.raise uu____4475)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____4533 bs2 bs_expected1 -> (match (uu____4533) with
| (env2, out, g, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.None), (g), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((match (((imp), (imp'))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4624))) -> begin
(

let uu____4627 = (

let uu____4628 = (

let uu____4631 = (

let uu____4632 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4632))
in (

let uu____4633 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____4631), (uu____4633))))
in FStar_Errors.Error (uu____4628))
in (FStar_Pervasives.raise uu____4627))
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4634)), FStar_Pervasives_Native.None) -> begin
(

let uu____4637 = (

let uu____4638 = (

let uu____4641 = (

let uu____4642 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____4642))
in (

let uu____4643 = (FStar_Syntax_Syntax.range_of_bv hd1)
in ((uu____4641), (uu____4643))))
in FStar_Errors.Error (uu____4638))
in (FStar_Pervasives.raise uu____4637))
end
| uu____4644 -> begin
()
end);
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____4648 = (

let uu____4651 = (

let uu____4652 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____4652.FStar_Syntax_Syntax.n)
in (match (uu____4651) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| uu____4657 -> begin
((

let uu____4659 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____4659) with
| true -> begin
(

let uu____4660 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____4660))
end
| uu____4661 -> begin
()
end));
(

let uu____4662 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____4662) with
| (t, uu____4669, g1) -> begin
(

let g2 = (

let uu____4672 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____4673 = (FStar_TypeChecker_Rel.teq env2 t expected_t)
in (FStar_TypeChecker_Util.label_guard uu____4672 "Type annotation on parameter incompatible with the expected type" uu____4673)))
in (

let g3 = (

let uu____4675 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g uu____4675))
in ((t), (g3))))
end));
)
end))
in (match (uu____4648) with
| (t, g1) -> begin
(

let hd2 = (

let uu___104_4691 = hd1
in {FStar_Syntax_Syntax.ppname = uu___104_4691.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_4691.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env3 = (push_binding env2 b)
in (

let subst2 = (

let uu____4700 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____4700))
in (aux ((env3), ((b)::out), (g1), (subst2)) bs3 bs_expected2))))))
end)));
)
end
| (rest, []) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.Some (FStar_Util.Inl (rest))), (g), (subst1))
end
| ([], rest) -> begin
((env2), ((FStar_List.rev out)), (FStar_Pervasives_Native.Some (FStar_Util.Inr (rest))), (g), (subst1))
end)
end))
in (aux ((env1), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 bs_expected)))
in (

let rec expected_function_typ1 = (fun env1 t0 body1 -> (match (t0) with
| FStar_Pervasives_Native.None -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4789 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____4793 = (tc_binders env1 bs)
in (match (uu____4793) with
| (bs1, envbody, g, uu____4814) -> begin
(

let uu____4815 = (

let uu____4822 = (

let uu____4823 = (FStar_Syntax_Subst.compress body1)
in uu____4823.FStar_Syntax_Syntax.n)
in (match (uu____4822) with
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), tacopt), uu____4835) -> begin
(

let uu____4871 = (tc_comp envbody c)
in (match (uu____4871) with
| (c1, uu____4882, g') -> begin
(

let uu____4884 = (tc_tactic_opt envbody tacopt)
in (

let uu____4886 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((FStar_Pervasives_Native.Some (c1)), (uu____4884), (body1), (uu____4886))))
end))
end
| uu____4889 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (body1), (g))
end))
in (match (uu____4815) with
| (copt, tacopt, body2, g1) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (copt), (tacopt), (envbody), (body2), (g1))
end))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____4948 = (

let uu____4949 = (FStar_Syntax_Subst.compress t2)
in uu____4949.FStar_Syntax_Syntax.n)
in (match (uu____4948) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4966) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____4980 -> begin
(failwith "Impossible")
end);
(

let uu____4984 = (tc_binders env1 bs)
in (match (uu____4984) with
| (bs1, envbody, g, uu____5006) -> begin
(

let uu____5007 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____5007) with
| (envbody1, uu____5026) -> begin
((FStar_Pervasives_Native.Some (((t2), (true)))), (bs1), ([]), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____5037); FStar_Syntax_Syntax.tk = uu____5038; FStar_Syntax_Syntax.pos = uu____5039; FStar_Syntax_Syntax.vars = uu____5040}, uu____5041) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____5069 -> begin
(failwith "Impossible")
end);
(

let uu____5073 = (tc_binders env1 bs)
in (match (uu____5073) with
| (bs1, envbody, g, uu____5095) -> begin
(

let uu____5096 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____5096) with
| (envbody1, uu____5115) -> begin
((FStar_Pervasives_Native.Some (((t2), (true)))), (bs1), ([]), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (envbody1), (body1), (g))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____5127) -> begin
(

let uu____5132 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____5132) with
| (uu____5161, bs1, bs', copt, tacopt, env2, body2, g) -> begin
((FStar_Pervasives_Native.Some (((t2), (false)))), (bs1), (bs'), (copt), (tacopt), (env2), (body2), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____5201 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____5201) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 -> (

let rec handle_more = (fun uu____5264 c_expected2 -> (match (uu____5264) with
| (env3, bs2, more, guard, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5325 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env3), (bs2), (guard), (uu____5325)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____5342 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____5342))
in (

let uu____5343 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env3), (bs2), (guard), (uu____5343))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (match ((FStar_Syntax_Util.is_named_tot c)) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env3 (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____5384 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____5384) with
| (bs_expected4, c_expected4) -> begin
(

let uu____5396 = (check_binders env3 more_bs bs_expected4)
in (match (uu____5396) with
| (env4, bs', more1, guard', subst2) -> begin
(

let uu____5423 = (

let uu____5439 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env4), ((FStar_List.append bs2 bs')), (more1), (uu____5439), (subst2)))
in (handle_more uu____5423 c_expected4))
end))
end))
end
| uu____5448 -> begin
(

let uu____5449 = (

let uu____5450 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format1 "More arguments than annotated type (%s)" uu____5450))
in (fail uu____5449 t3))
end))
end
| uu____5458 -> begin
(fail "Function definition takes more arguments than expected from its annotated type" t2)
end))
end)
end))
in (

let uu____5466 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____5466 c_expected1))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___105_5504 = envbody
in {FStar_TypeChecker_Env.solver = uu___105_5504.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_5504.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_5504.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_5504.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_5504.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_5504.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_5504.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_5504.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_5504.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_5504.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_5504.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_5504.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___105_5504.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_5504.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___105_5504.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___105_5504.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_5504.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_5504.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_5504.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___105_5504.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_5504.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_5504.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___105_5504.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___105_5504.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___105_5504.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___105_5504.FStar_TypeChecker_Env.is_native_tactic})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____5530 uu____5531 -> (match (((uu____5530), (uu____5531))) with
| ((env2, letrec_binders), (l, t3)) -> begin
(

let uu____5556 = (

let uu____5560 = (

let uu____5561 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____5561 FStar_Pervasives_Native.fst))
in (tc_term uu____5560 t3))
in (match (uu____5556) with
| (t4, uu____5573, uu____5574) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l (([]), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____5581 = (FStar_Syntax_Syntax.mk_binder (

let uu___106_5584 = x
in {FStar_Syntax_Syntax.ppname = uu___106_5584.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_5584.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____5581)::letrec_binders)
end
| uu____5585 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____5588 = (check_actuals_against_formals env1 bs bs_expected1)
in (match (uu____5588) with
| (envbody, bs1, g, c) -> begin
(

let uu____5620 = (

let uu____5624 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____5624) with
| true -> begin
(mk_letrec_env envbody bs1 c)
end
| uu____5628 -> begin
((envbody), ([]))
end))
in (match (uu____5620) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (((t2), (false)))), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (FStar_Pervasives_Native.None), (envbody2), (body1), (g)))
end))
end))))
end))
end
| uu____5660 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____5675 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____5675))
end
| uu____5676 -> begin
(

let uu____5677 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____5677) with
| (uu____5705, bs1, uu____5707, c_opt, tacopt, envbody, body2, g) -> begin
((FStar_Pervasives_Native.Some (((t2), (false)))), (bs1), ([]), (c_opt), (tacopt), (envbody), (body2), (g))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____5732 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____5732) with
| (env1, topt) -> begin
((

let uu____5744 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____5744) with
| true -> begin
(

let uu____5745 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____5745 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____5747 -> begin
"false"
end)))
end
| uu____5748 -> begin
()
end));
(

let uu____5749 = (expected_function_typ1 env1 topt body)
in (match (uu____5749) with
| (tfun_opt, bs1, letrec_binders, c_opt, tacopt, envbody, body1, g) -> begin
(

let uu____5784 = (tc_term (

let uu___107_5790 = envbody
in {FStar_TypeChecker_Env.solver = uu___107_5790.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___107_5790.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___107_5790.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___107_5790.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___107_5790.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___107_5790.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___107_5790.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___107_5790.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___107_5790.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___107_5790.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___107_5790.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___107_5790.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___107_5790.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___107_5790.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___107_5790.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___107_5790.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___107_5790.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___107_5790.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___107_5790.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___107_5790.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___107_5790.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___107_5790.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___107_5790.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___107_5790.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___107_5790.FStar_TypeChecker_Env.is_native_tactic}) body1)
in (match (uu____5784) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in ((

let uu____5799 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Implicits")))
in (match (uu____5799) with
| true -> begin
(

let uu____5800 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body1.FStar_TypeChecker_Env.implicits))
in (

let uu____5811 = (

let uu____5812 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____5812))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" uu____5800 uu____5811)))
end
| uu____5813 -> begin
()
end));
(

let uu____5814 = (

let uu____5818 = (

let uu____5821 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body2), (uu____5821)))
in (check_expected_effect (

let uu___108_5828 = envbody
in {FStar_TypeChecker_Env.solver = uu___108_5828.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_5828.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_5828.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_5828.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_5828.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_5828.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_5828.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_5828.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_5828.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_5828.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_5828.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_5828.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_5828.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_5828.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_5828.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___108_5828.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_5828.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___108_5828.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___108_5828.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_5828.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_5828.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_5828.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_5828.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___108_5828.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___108_5828.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___108_5828.FStar_TypeChecker_Env.is_native_tactic}) c_opt uu____5818))
in (match (uu____5814) with
| (body3, cbody1, guard) -> begin
(

let guard1 = (FStar_TypeChecker_Rel.conj_guard guard_body1 guard)
in (

let guard2 = (

let uu____5837 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____5839 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____5839))))
in (match (uu____5837) with
| true -> begin
(

let uu____5840 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.discharge_guard envbody uu____5840))
end
| uu____5841 -> begin
(

let guard2 = (

let uu____5843 = (FStar_TypeChecker_Rel.conj_guard g guard1)
in (FStar_TypeChecker_Rel.close_guard env1 (FStar_List.append bs1 letrec_binders) uu____5843))
in guard2)
end))
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody1)
in (

let e = (FStar_Syntax_Util.abs bs1 body3 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody1 c_opt)))))
in (

let uu____5850 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t, use_teq) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5865) -> begin
((e), (t1), (guard2))
end
| uu____5873 -> begin
(

let uu____5874 = (match (use_teq) with
| true -> begin
(

let uu____5879 = (FStar_TypeChecker_Rel.teq env1 t1 tfun_computed)
in ((e), (uu____5879)))
end
| uu____5880 -> begin
(FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
end)
in (match (uu____5874) with
| (e1, guard') -> begin
(

let uu____5886 = (FStar_TypeChecker_Rel.conj_guard guard2 guard')
in ((e1), (t1), (uu____5886)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard2))
end)
in (match (uu____5850) with
| (e1, tfun, guard3) -> begin
(

let c = (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total tfun)
end
| uu____5898 -> begin
(FStar_TypeChecker_Util.return_value env1 tfun e1)
end)
in (

let uu____5899 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 (FStar_Syntax_Util.lcomp_of_comp c) guard3)
in (match (uu____5899) with
| (c1, g1) -> begin
((e1), (c1), (g1))
end)))
end))))))
end));
))
end))
end));
)
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in ((

let uu____5936 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____5936) with
| true -> begin
(

let uu____5937 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____5938 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____5937 uu____5938)))
end
| uu____5939 -> begin
()
end));
(

let monadic_application = (fun uu____5976 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____5976) with
| (head2, chead1, ghead1, cres) -> begin
(

let rt = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres1 = (

let uu___109_6013 = cres
in {FStar_Syntax_Syntax.eff_name = uu___109_6013.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___109_6013.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___109_6013.FStar_Syntax_Syntax.comp})
in (

let uu____6014 = (match (bs) with
| [] -> begin
(

let cres2 = (FStar_TypeChecker_Util.subst_lcomp subst1 cres1)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in ((cres2), (g))))
end
| uu____6023 -> begin
(

let g = (

let uu____6028 = (FStar_TypeChecker_Rel.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____6028 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (

let uu____6029 = (

let uu____6030 = (

let uu____6033 = (

let uu____6034 = (

let uu____6035 = (cres1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs uu____6035))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst1) uu____6034))
in (FStar_Syntax_Syntax.mk_Total uu____6033))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6030))
in ((uu____6029), (g))))
end)
in (match (uu____6014) with
| (cres2, guard1) -> begin
((

let uu____6046 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6046) with
| true -> begin
(

let uu____6047 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____6047))
end
| uu____6048 -> begin
()
end));
(

let cres3 = (

let uu____6050 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
in (match (uu____6050) with
| true -> begin
(

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2))
end
| uu____6060 -> begin
cres2
end))
in (

let comp = (FStar_List.fold_left (fun out_c uu____6078 -> (match (uu____6078) with
| ((e, q), x, c) -> begin
(

let uu____6101 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____6101) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____6105 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end))
end)) cres3 arg_comps_rev)
in (

let comp1 = (FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
in (

let shortcuts_evaluation_order = (

let uu____6110 = (

let uu____6111 = (FStar_Syntax_Subst.compress head2)
in uu____6111.FStar_Syntax_Syntax.n)
in (match (uu____6110) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____6115 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____6130 -> (match (uu____6130) with
| (arg, uu____6138, uu____6139) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 (FStar_Pervasives_Native.Some (comp1.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ))))
end
| uu____6148 -> begin
(

let uu____6149 = (

let map_fun = (fun uu____6184 -> (match (uu____6184) with
| ((e, q), uu____6204, c) -> begin
(

let uu____6210 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____6210) with
| true -> begin
((FStar_Pervasives_Native.None), (((e), (q))))
end
| uu____6237 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____6240 = (

let uu____6243 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____6243), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____6240)))))
end))
end))
in (

let uu____6261 = (

let uu____6275 = (

let uu____6288 = (

let uu____6296 = (

let uu____6301 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____6301), (FStar_Pervasives_Native.None), (chead1)))
in (uu____6296)::arg_comps_rev)
in (FStar_List.map map_fun uu____6288))
in (FStar_All.pipe_left FStar_List.split uu____6275))
in (match (uu____6261) with
| (lifted_args, reverse_args) -> begin
(

let uu____6396 = (

let uu____6397 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____6397))
in (

let uu____6402 = (

let uu____6406 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____6406))
in ((lifted_args), (uu____6396), (uu____6402))))
end)))
in (match (uu____6149) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 (FStar_Pervasives_Native.Some (comp1.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp1.FStar_Syntax_Syntax.eff_name comp1.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___88_6472 -> (match (uu___88_6472) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1)
in (

let letbinding = (

let uu____6514 = (

let uu____6517 = (

let uu____6518 = (

let uu____6526 = (

let uu____6527 = (

let uu____6528 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6528)::[])
in (FStar_Syntax_Subst.close uu____6527 e))
in ((((false), ((lb)::[]))), (uu____6526)))
in FStar_Syntax_Syntax.Tm_let (uu____6518))
in (FStar_Syntax_Syntax.mk uu____6517))
in (uu____6514 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____6558 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp1 guard1)
in (match (uu____6558) with
| (comp2, g) -> begin
((app), (comp2), (g))
end)))))));
)
end))))
end))
in (

let rec tc_args = (fun head_info uu____6612 bs args1 -> (match (uu____6612) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6692))))::rest, ((uu____6694, FStar_Pervasives_Native.None))::uu____6695) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let t1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (

let uu____6732 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____6732) with
| (varg, uu____6743, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____6756 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____6756)))
in (

let uu____6757 = (

let uu____6775 = (

let uu____6783 = (

let uu____6790 = (

let uu____6791 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____6791 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____6790)))
in (uu____6783)::outargs)
in (

let uu____6801 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst2), (uu____6775), ((arg)::arg_rets), (uu____6801), (fvs))))
in (tc_args head_info uu____6757 rest args1))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6861)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6862))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____6869 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let x1 = (

let uu___110_6876 = x
in {FStar_Syntax_Syntax.ppname = uu___110_6876.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_6876.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____6878 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____6878) with
| true -> begin
(

let uu____6879 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" uu____6879))
end
| uu____6880 -> begin
()
end));
(

let targ1 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___111_6884 = env1
in {FStar_TypeChecker_Env.solver = uu___111_6884.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_6884.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_6884.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_6884.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_6884.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_6884.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_6884.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_6884.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_6884.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_6884.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_6884.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_6884.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_6884.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_6884.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_6884.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = uu___111_6884.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_6884.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___111_6884.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___111_6884.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_6884.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_6884.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_6884.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_6884.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___111_6884.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___111_6884.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___111_6884.FStar_TypeChecker_Env.is_native_tactic})
in ((

let uu____6886 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6886) with
| true -> begin
(

let uu____6887 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____6888 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6889 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____6887 uu____6888 uu____6889))))
end
| uu____6890 -> begin
()
end));
(

let uu____6891 = (tc_term env2 e)
in (match (uu____6891) with
| (e1, c, g_e) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____6908 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____6908))
in (

let uu____6909 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____6909) with
| true -> begin
(

let subst2 = (

let uu____6914 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____6914 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____6939 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
))));
)));
)
end
| (uu____6962, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____6983) -> begin
(

let uu____7013 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____7013) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 tres -> (

let tres1 = (

let uu____7036 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____7036 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____7052 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____7052) with
| (bs2, cres'1) -> begin
(

let head_info1 = ((head2), (chead1), (ghead1), ((FStar_Syntax_Util.lcomp_of_comp cres'1)))
in ((

let uu____7066 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____7066) with
| true -> begin
(

let uu____7067 = (FStar_Range.string_of_range tres1.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" uu____7067))
end
| uu____7068 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____7089 when (not (norm1)) -> begin
(

let uu____7090 = (FStar_TypeChecker_Normalize.unfold_whnf env tres1)
in (aux true uu____7090))
end
| uu____7091 -> begin
(

let uu____7092 = (

let uu____7093 = (

let uu____7096 = (

let uu____7097 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____7098 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" uu____7097 uu____7098)))
in (

let uu____7105 = (FStar_Syntax_Syntax.argpos arg)
in ((uu____7096), (uu____7105))))
in FStar_Errors.Error (uu____7093))
in (FStar_Pervasives.raise uu____7092))
end)))
in (aux false chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf -> (

let uu____7118 = (

let uu____7119 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____7119.FStar_Syntax_Syntax.n)
in (match (uu____7118) with
| FStar_Syntax_Syntax.Tm_uvar (uu____7127) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____7187 = (tc_term env1 e)
in (match (uu____7187) with
| (e1, c, g_e) -> begin
(

let uu____7200 = (tc_args1 env1 tl1)
in (match (uu____7200) with
| (args2, comps, g_rest) -> begin
(

let uu____7222 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____7222)))
end))
end))
end))
in (

let uu____7233 = (tc_args1 env args)
in (match (uu____7233) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____7255 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____7278 -> (match (uu____7278) with
| (uu____7286, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____7255))
in (

let ml_or_tot = (fun t r1 -> (

let uu____7302 = (FStar_Options.ml_ish ())
in (match (uu____7302) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____7303 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____7305 = (

let uu____7308 = (

let uu____7309 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7309 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____7308))
in (ml_or_tot uu____7305 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____7318 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7318) with
| true -> begin
(

let uu____7319 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7320 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____7321 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____7319 uu____7320 uu____7321))))
end
| uu____7322 -> begin
()
end));
(

let uu____7324 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____7324));
(

let comp = (

let uu____7326 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____7335 out -> (match (uu____7335) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____7326))
in (

let uu____7344 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 (FStar_Pervasives_Native.Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____7349 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____7344), (comp), (uu____7349)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____7352); FStar_Syntax_Syntax.tk = uu____7353; FStar_Syntax_Syntax.pos = uu____7354; FStar_Syntax_Syntax.vars = uu____7355}, uu____7356) -> begin
(

let rec tc_args1 = (fun env1 args1 -> (match (args1) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl1 -> begin
(

let uu____7430 = (tc_term env1 e)
in (match (uu____7430) with
| (e1, c, g_e) -> begin
(

let uu____7443 = (tc_args1 env1 tl1)
in (match (uu____7443) with
| (args2, comps, g_rest) -> begin
(

let uu____7465 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e1), (imp)))::args2), ((((e1.FStar_Syntax_Syntax.pos), (c)))::comps), (uu____7465)))
end))
end))
end))
in (

let uu____7476 = (tc_args1 env args)
in (match (uu____7476) with
| (args1, comps, g_args) -> begin
(

let bs = (

let uu____7498 = (FStar_All.pipe_right comps (FStar_List.map (fun uu____7521 -> (match (uu____7521) with
| (uu____7529, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (FStar_Pervasives_Native.None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks uu____7498))
in (

let ml_or_tot = (fun t r1 -> (

let uu____7545 = (FStar_Options.ml_ish ())
in (match (uu____7545) with
| true -> begin
(FStar_Syntax_Util.ml_comp t r1)
end
| uu____7546 -> begin
(FStar_Syntax_Syntax.mk_Total t)
end)))
in (

let cres = (

let uu____7548 = (

let uu____7551 = (

let uu____7552 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____7552 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_uvar env uu____7551))
in (ml_or_tot uu____7548 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____7561 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____7561) with
| true -> begin
(

let uu____7562 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____7563 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____7564 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____7562 uu____7563 uu____7564))))
end
| uu____7565 -> begin
()
end));
(

let uu____7567 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) uu____7567));
(

let comp = (

let uu____7569 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun uu____7578 out -> (match (uu____7578) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env FStar_Pervasives_Native.None c ((FStar_Pervasives_Native.None), (out)))
end)) ((((head1.FStar_Syntax_Syntax.pos), (chead)))::comps) uu____7569))
in (

let uu____7587 = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 (FStar_Pervasives_Native.Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let uu____7592 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((uu____7587), (comp), (uu____7592)))));
)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7607 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7607) with
| (bs1, c1) -> begin
(

let head_info = ((head1), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c1)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs1 args))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____7643) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____7649, uu____7650) -> begin
(check_function_app t)
end
| uu____7679 -> begin
(

let uu____7680 = (

let uu____7681 = (

let uu____7684 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((uu____7684), (head1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____7681))
in (FStar_Pervasives.raise uu____7680))
end)))
in (check_function_app thead))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____7739 = (FStar_List.fold_left2 (fun uu____7772 uu____7773 uu____7774 -> (match (((uu____7772), (uu____7773), (uu____7774))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((match ((aq <> aq')) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____7817 -> begin
()
end);
(

let uu____7818 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____7818) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____7830 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard uu____7830 g))
in (

let ghost1 = (ghost || ((

let uu____7834 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____7834))) && (

let uu____7836 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____7836)))))
in (

let uu____7837 = (

let uu____7843 = (

let uu____7849 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____7849)::[])
in (FStar_List.append seen uu____7843))
in (

let uu____7854 = (FStar_TypeChecker_Rel.conj_guard guard g1)
in ((uu____7837), (uu____7854), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____7739) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 (FStar_Pervasives_Native.Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____7881 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____7881 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____7882 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____7883 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____7883) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____7895 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____7916 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____7916) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____7940 = branch1
in (match (uu____7940) with
| (cpat, uu____7959, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let uu____7995 = (FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0)
in (match (uu____7995) with
| (pat_bvs1, exp, p) -> begin
((

let uu____8012 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8012) with
| true -> begin
(

let uu____8013 = (FStar_Syntax_Print.pat_to_string p0)
in (

let uu____8014 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" uu____8013 uu____8014)))
end
| uu____8015 -> begin
()
end));
(

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs1)
in (

let uu____8017 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (uu____8017) with
| (env1, uu____8028) -> begin
(

let env11 = (

let uu___112_8032 = env1
in {FStar_TypeChecker_Env.solver = uu___112_8032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_8032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_8032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_8032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___112_8032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_8032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_8032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_8032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = uu___112_8032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_8032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_8032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_8032.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_8032.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_8032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_8032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___112_8032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___112_8032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___112_8032.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_8032.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___112_8032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_8032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_8032.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___112_8032.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___112_8032.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___112_8032.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___112_8032.FStar_TypeChecker_Env.is_native_tactic})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in ((

let uu____8035 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8035) with
| true -> begin
(

let uu____8036 = (FStar_Syntax_Print.term_to_string exp)
in (

let uu____8037 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" uu____8036 uu____8037)))
end
| uu____8038 -> begin
()
end));
(

let env12 = (FStar_TypeChecker_Env.set_expected_typ env11 expected_pat_t)
in (

let uu____8040 = (tc_tot_or_gtot_term env12 exp)
in (match (uu____8040) with
| (exp1, lc, g) -> begin
(

let g1 = (

let uu___113_8054 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___113_8054.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___113_8054.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___113_8054.FStar_TypeChecker_Env.implicits})
in (

let uu____8055 = (

let g' = (FStar_TypeChecker_Rel.teq env12 lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g2 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (

let env13 = (FStar_TypeChecker_Env.set_range env12 exp1.FStar_Syntax_Syntax.pos)
in (

let uu____8059 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env13 g2)
in (FStar_All.pipe_right uu____8059 FStar_TypeChecker_Rel.resolve_implicits)))))
in (

let norm_exp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env12 exp1)
in (

let uvs1 = (FStar_Syntax_Free.uvars norm_exp)
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in ((

let uu____8070 = (

let uu____8071 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation uu____8071))
in (match (uu____8070) with
| true -> begin
(

let unresolved = (

let uu____8078 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right uu____8078 FStar_Util.set_elements))
in (

let uu____8092 = (

let uu____8093 = (

let uu____8096 = (

let uu____8097 = (FStar_TypeChecker_Normalize.term_to_string env norm_exp)
in (

let uu____8098 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (

let uu____8099 = (

let uu____8100 = (FStar_All.pipe_right unresolved (FStar_List.map (fun uu____8111 -> (match (uu____8111) with
| (u, uu____8115) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right uu____8100 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" uu____8097 uu____8098 uu____8099))))
in ((uu____8096), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (uu____8093))
in (FStar_Pervasives.raise uu____8092)))
end
| uu____8117 -> begin
()
end));
(

let uu____8119 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8119) with
| true -> begin
(

let uu____8120 = (FStar_TypeChecker_Normalize.term_to_string env exp1)
in (FStar_Util.print1 "Done checking pattern expression %s\n" uu____8120))
end
| uu____8121 -> begin
()
end));
(

let p1 = (FStar_TypeChecker_Util.decorate_pattern env p exp1)
in ((p1), (pat_bvs1), (pat_env), (exp1), (norm_exp)));
))))))
end)));
)))
end)));
)
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____8128 = (

let uu____8132 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____8132 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____8128) with
| (scrutinee_env, uu____8145) -> begin
(

let uu____8148 = (tc_pat true pat_t pattern)
in (match (uu____8148) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp) -> begin
(

let uu____8170 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____8185 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____8185) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____8192 -> begin
(

let uu____8193 = (

let uu____8197 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term uu____8197 e))
in (match (uu____8193) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____8170) with
| (when_clause1, g_when) -> begin
(

let uu____8217 = (tc_term pat_env branch_exp)
in (match (uu____8217) with
| (branch_exp1, c, g_branch) -> begin
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____8236 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____8236))
end)
in (

let uu____8238 = (

let eqs = (

let uu____8244 = (

let uu____8245 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8245)))
in (match (uu____8244) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8247 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8250) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____8261) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8262) -> begin
FStar_Pervasives_Native.None
end
| uu____8263 -> begin
(

let uu____8264 = (

let uu____8265 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____8265 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____8264))
end))
end))
in (

let uu____8266 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____8266) with
| (c1, g_branch1) -> begin
(

let uu____8276 = (match (((eqs), (when_condition))) with
| uu____8283 when (

let uu____8288 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8288))) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (

let uu____8296 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____8297 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((uu____8296), (uu____8297))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____8304 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____8304))
in (

let uu____8305 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____8306 = (

let uu____8307 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard uu____8307 g_when))
in ((uu____8305), (uu____8306))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (

let uu____8313 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____8313), (g_when)))))
end)
in (match (uu____8276) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let uu____8321 = (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak)
in (

let uu____8322 = (FStar_TypeChecker_Rel.close_guard env binders g_when_weak)
in ((uu____8321), (uu____8322), (g_branch1)))))
end))
end)))
in (match (uu____8238) with
| (c1, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____8335 = (

let uu____8336 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8336)))
in (match (uu____8335) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____8337 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____8361 = (

let uu____8362 = (

let uu____8363 = (

let uu____8365 = (

let uu____8369 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____8369))
in (FStar_Pervasives_Native.snd uu____8365))
in (FStar_List.length uu____8363))
in (uu____8362 > (Prims.parse_int "1")))
in (match (uu____8361) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____8375 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____8375) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____8386 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____8396 = (

let uu____8397 = (

let uu____8398 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____8398)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____8397))
in (uu____8396 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____8403 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____8403)::[])))
end)))
end
| uu____8404 -> begin
[]
end)))
in (

let fail = (fun uu____8408 -> (

let uu____8409 = (

let uu____8410 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____8411 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____8412 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____8410 uu____8411 uu____8412))))
in (failwith uu____8409)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____8423) -> begin
(head_constructor t1)
end
| uu____8428 -> begin
(fail ())
end))
in (

let pat_exp2 = (

let uu____8430 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____8430 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____8432) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8443); FStar_Syntax_Syntax.tk = uu____8444; FStar_Syntax_Syntax.pos = uu____8445; FStar_Syntax_Syntax.vars = uu____8446}, uu____8447) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____8472) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c2) -> begin
(

let uu____8474 = (

let uu____8475 = (tc_constant pat_exp2.FStar_Syntax_Syntax.pos c2)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____8475 scrutinee_tm1 pat_exp2))
in (uu____8474)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____8476) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____8482 = (

let uu____8483 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8483)))
in (match (uu____8482) with
| true -> begin
[]
end
| uu____8485 -> begin
(

let uu____8486 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____8486))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8488) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____8490 = (

let uu____8491 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8491)))
in (match (uu____8490) with
| true -> begin
[]
end
| uu____8493 -> begin
(

let uu____8494 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____8494))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____8513 = (

let uu____8514 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____8514)))
in (match (uu____8513) with
| true -> begin
[]
end
| uu____8516 -> begin
(

let sub_term_guards = (

let uu____8519 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____8541 -> (match (uu____8541) with
| (ei, uu____8548) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____8554 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____8554) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____8565 -> begin
(

let sub_term = (

let uu____8574 = (

let uu____8575 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let uu____8576 = (

let uu____8577 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____8577)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____8575 uu____8576)))
in (uu____8574 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____8519 FStar_List.flatten))
in (

let uu____8585 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____8585 sub_term_guards)))
end)))
end
| uu____8587 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____8599 = (

let uu____8600 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____8600)))
in (match (uu____8599) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____8601 -> begin
(

let t = (

let uu____8603 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____8603))
in (

let uu____8606 = (FStar_Syntax_Util.type_u ())
in (match (uu____8606) with
| (k, uu____8610) -> begin
(

let uu____8611 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____8611) with
| (t1, uu____8616, uu____8617) -> begin
t1
end))
end)))
end)))
in (

let branch_guard = (build_and_check_branch_guard scrutinee_tm norm_pat_exp)
in (

let branch_guard1 = (match (when_condition) with
| FStar_Pervasives_Native.None -> begin
branch_guard
end
| FStar_Pervasives_Native.Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard1))))
end))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when1 g_branch1)
in ((

let uu____8623 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____8623) with
| true -> begin
(

let uu____8624 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____8624))
end
| uu____8625 -> begin
()
end));
(

let uu____8626 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in ((uu____8626), (branch_guard), (c1), (guard)));
)))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let uu____8644 = (check_let_bound_def true env1 lb)
in (match (uu____8644) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____8658 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____8667 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____8667), (univ_vars1), (c1)))
end
| uu____8668 -> begin
(

let g11 = (

let uu____8670 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____8670 FStar_TypeChecker_Rel.resolve_implicits))
in (

let uu____8673 = (

let uu____8678 = (

let uu____8684 = (

let uu____8689 = (

let uu____8697 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____8697)))
in (uu____8689)::[])
in (FStar_TypeChecker_Util.generalize env1 uu____8684))
in (FStar_List.hd uu____8678))
in (match (uu____8673) with
| (uu____8726, univs1, e11, c11) -> begin
((g11), (e11), (univs1), ((FStar_Syntax_Util.lcomp_of_comp c11)))
end)))
end)
in (match (uu____8658) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____8737 = (

let uu____8742 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8742) with
| true -> begin
(

let uu____8747 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____8747) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____8762 -> begin
((

let uu____8764 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.warn uu____8764 FStar_TypeChecker_Err.top_level_effect));
(

let uu____8765 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____8765), (c12)));
)
end)
end))
end
| uu____8776 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____8779 = (c11.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right uu____8779 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env1)))
in (

let e21 = (

let uu____8787 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____8787) with
| true -> begin
e2
end
| uu____8790 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
end))
in ((e21), (c))));
)
end))
in (match (uu____8737) with
| (e21, c12) -> begin
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit)
in ((FStar_ST.write e21.FStar_Syntax_Syntax.tk (FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e11)
in (

let uu____8815 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) (FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((uu____8815), ((FStar_Syntax_Util.lcomp_of_comp cres)), (FStar_TypeChecker_Rel.trivial_guard))));
))
end))
end))
end))
end
| uu____8830 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___114_8851 = env1
in {FStar_TypeChecker_Env.solver = uu___114_8851.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_8851.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_8851.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_8851.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_8851.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_8851.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_8851.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_8851.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_8851.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_8851.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_8851.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_8851.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_8851.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___114_8851.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_8851.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_8851.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_8851.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_8851.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_8851.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_8851.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_8851.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_8851.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_8851.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___114_8851.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___114_8851.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___114_8851.FStar_TypeChecker_Env.is_native_tactic})
in (

let uu____8852 = (

let uu____8858 = (

let uu____8859 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____8859 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____8858 lb))
in (match (uu____8852) with
| (e1, uu____8871, c1, g1, annotated) -> begin
(

let x = (

let uu___115_8876 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___115_8876.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_8876.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____8877 = (

let uu____8880 = (

let uu____8881 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8881)::[])
in (FStar_Syntax_Subst.open_term uu____8880 e2))
in (match (uu____8877) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let uu____8893 = (

let uu____8897 = (FStar_TypeChecker_Env.push_bv env2 x1)
in (tc_term uu____8897 e21))
in (match (uu____8893) with
| (e22, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env2 (FStar_Pervasives_Native.Some (e1)) c1 ((FStar_Pervasives_Native.Some (x1)), (c2)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e11)
in (

let e3 = (

let uu____8912 = (

let uu____8915 = (

let uu____8916 = (

let uu____8924 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____8924)))
in FStar_Syntax_Syntax.Tm_let (uu____8916))
in (FStar_Syntax_Syntax.mk uu____8915))
in (uu____8912 (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____8939 = (

let uu____8940 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____8941 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____8940 c1.FStar_Syntax_Syntax.res_typ uu____8941 e11)))
in (FStar_All.pipe_left (fun _0_41 -> FStar_TypeChecker_Common.NonTrivial (_0_41)) uu____8939))
in (

let g21 = (

let uu____8943 = (

let uu____8944 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard uu____8944 g2))
in (FStar_TypeChecker_Rel.close_guard env2 xb uu____8943))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g21)
in (

let uu____8946 = (

let uu____8947 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____8947))
in (match (uu____8946) with
| true -> begin
(

let tt = (

let uu____8953 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____8953 FStar_Option.get))
in ((

let uu____8957 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____8957) with
| true -> begin
(

let uu____8958 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____8959 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____8958 uu____8959)))
end
| uu____8960 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____8961 -> begin
(

let t = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((

let uu____8964 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____8964) with
| true -> begin
(

let uu____8965 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____8966 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____8965 uu____8966)))
end
| uu____8967 -> begin
()
end));
((e4), ((

let uu___116_8969 = cres
in {FStar_Syntax_Syntax.eff_name = uu___116_8969.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___116_8969.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___116_8969.FStar_Syntax_Syntax.comp})), (guard));
))
end)))))))))))
end))))
end)))
end)))
end
| uu____8970 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____8991 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____8991) with
| (lbs1, e21) -> begin
(

let uu____9002 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9002) with
| (env0, topt) -> begin
(

let uu____9013 = (build_let_rec_env true env0 lbs1)
in (match (uu____9013) with
| (lbs2, rec_env) -> begin
(

let uu____9024 = (check_let_recs rec_env lbs2)
in (match (uu____9024) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____9036 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g_lbs)
in (FStar_All.pipe_right uu____9036 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (

let uu____9040 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____9040 (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((lb.FStar_Syntax_Syntax.lbunivs = [])) with
| true -> begin
lb
end
| uu____9060 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef)
end)))))
end
| uu____9061 -> begin
(

let ecs = (

let uu____9068 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____9092 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____9092))))))
in (FStar_TypeChecker_Util.generalize env1 uu____9068))
in (FStar_All.pipe_right ecs (FStar_List.map (fun uu____9117 -> (match (uu____9117) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end)
in (

let cres = (

let uu____9142 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____9142))
in ((FStar_ST.write e21.FStar_Syntax_Syntax.tk (FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)));
(

let uu____9151 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____9151) with
| (lbs5, e22) -> begin
((

let uu____9163 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____9163 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____9164 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) (FStar_Pervasives_Native.Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((uu____9164), (cres), (FStar_TypeChecker_Rel.trivial_guard)));
)
end));
)))))
end))
end))
end))
end))
end
| uu____9177 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____9198 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____9198) with
| (lbs1, e21) -> begin
(

let uu____9209 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____9209) with
| (env0, topt) -> begin
(

let uu____9220 = (build_let_rec_env false env0 lbs1)
in (match (uu____9220) with
| (lbs2, rec_env) -> begin
(

let uu____9231 = (check_let_recs rec_env lbs2)
in (match (uu____9231) with
| (lbs3, g_lbs) -> begin
(

let uu____9242 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___117_9258 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___117_9258.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_9258.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___118_9260 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___118_9260.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___118_9260.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___118_9260.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___118_9260.FStar_Syntax_Syntax.lbdef})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____9242) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____9278 = (tc_term env2 e21)
in (match (uu____9278) with
| (e22, cres, g2) -> begin
(

let guard = (

let uu____9289 = (

let uu____9290 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Rel.close_guard env2 uu____9290 g2))
in (FStar_TypeChecker_Rel.conj_guard g_lbs uu____9289))
in (

let cres1 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres)
in (

let tres = (norm env2 cres1.FStar_Syntax_Syntax.res_typ)
in (

let cres2 = (

let uu___119_9294 = cres1
in {FStar_Syntax_Syntax.eff_name = uu___119_9294.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___119_9294.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___119_9294.FStar_Syntax_Syntax.comp})
in (

let uu____9295 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____9295) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) (FStar_Pervasives_Native.Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____9320) -> begin
((e), (cres2), (guard))
end
| FStar_Pervasives_Native.None -> begin
(

let tres1 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (

let cres3 = (

let uu___120_9325 = cres2
in {FStar_Syntax_Syntax.eff_name = uu___120_9325.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___120_9325.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = uu___120_9325.FStar_Syntax_Syntax.comp})
in ((e), (cres3), (guard))))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| uu____9328 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____9351 = (

let uu____9354 = (

let uu____9355 = (FStar_Syntax_Subst.compress t)
in uu____9355.FStar_Syntax_Syntax.n)
in (

let uu____9358 = (

let uu____9359 = (FStar_Syntax_Subst.compress lbdef)
in uu____9359.FStar_Syntax_Syntax.n)
in ((uu____9354), (uu____9358))))
in (match (uu____9351) with
| (FStar_Syntax_Syntax.Tm_arrow (formals, c), FStar_Syntax_Syntax.Tm_abs (actuals, uu____9365, uu____9366)) -> begin
(

let actuals1 = (

let uu____9390 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9390 actuals))
in ((match (((FStar_List.length formals) <> (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((n1 = (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____9414 -> begin
(

let uu____9415 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____9415))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((n1 = (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____9432 -> begin
(

let uu____9433 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____9433))
end))
in (

let msg = (

let uu____9441 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____9442 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____9441 uu____9442 formals_msg actuals_msg)))
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), (lbdef.FStar_Syntax_Syntax.pos))))))))
end
| uu____9443 -> begin
()
end);
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)));
))
end
| uu____9447 -> begin
(

let uu____9450 = (

let uu____9451 = (

let uu____9454 = (

let uu____9455 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____9456 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____9455 uu____9456)))
in ((uu____9454), (lbtyp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____9451))
in (FStar_Pervasives.raise uu____9450))
end))))
in (

let uu____9457 = (FStar_List.fold_left (fun uu____9477 lb -> (match (uu____9477) with
| (lbs1, env1) -> begin
(

let uu____9489 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____9489) with
| (univ_vars1, t, check_t) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t1 = (match ((not (check_t))) with
| true -> begin
t
end
| uu____9502 -> begin
(

let uu____9503 = (

let uu____9507 = (

let uu____9508 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9508))
in (tc_check_tot_or_gtot_term (

let uu___121_9515 = env0
in {FStar_TypeChecker_Env.solver = uu___121_9515.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___121_9515.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___121_9515.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___121_9515.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___121_9515.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___121_9515.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___121_9515.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___121_9515.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___121_9515.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___121_9515.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___121_9515.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___121_9515.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___121_9515.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___121_9515.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___121_9515.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___121_9515.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___121_9515.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___121_9515.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___121_9515.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___121_9515.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___121_9515.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___121_9515.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___121_9515.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___121_9515.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___121_9515.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___121_9515.FStar_TypeChecker_Env.is_native_tactic}) t uu____9507))
in (match (uu____9503) with
| (t1, uu____9517, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.resolve_implicits g)
in ((

let uu____9521 = (FStar_TypeChecker_Rel.discharge_guard env2 g1)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____9521));
(norm env0 t1);
))
end))
end)
in (

let env3 = (

let uu____9523 = ((termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____9523) with
| true -> begin
(

let uu___122_9524 = env2
in {FStar_TypeChecker_Env.solver = uu___122_9524.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___122_9524.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___122_9524.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___122_9524.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___122_9524.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___122_9524.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___122_9524.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___122_9524.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___122_9524.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___122_9524.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___122_9524.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___122_9524.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___122_9524.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___122_9524.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___122_9524.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___122_9524.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___122_9524.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___122_9524.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___122_9524.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___122_9524.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___122_9524.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___122_9524.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___122_9524.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___122_9524.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___122_9524.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___122_9524.FStar_TypeChecker_Env.is_native_tactic})
end
| uu____9531 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname (([]), (t1)))
end))
in (

let lb1 = (

let uu___123_9534 = lb
in {FStar_Syntax_Syntax.lbname = uu___123_9534.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___123_9534.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb1)::lbs1), (env3)))))))
end))
end)) (([]), (env)) lbs)
in (match (uu____9457) with
| (lbs1, env1) -> begin
(((FStar_List.rev lbs1)), (env1))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____9548 = (

let uu____9553 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> ((

let uu____9573 = (

let uu____9574 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____9574.FStar_Syntax_Syntax.n)
in (match (uu____9573) with
| FStar_Syntax_Syntax.Tm_abs (uu____9577) -> begin
()
end
| uu____9587 -> begin
(

let uu____9588 = (

let uu____9589 = (

let uu____9592 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (("Only function literals may be defined recursively"), (uu____9592)))
in FStar_Errors.Error (uu____9589))
in (FStar_Pervasives.raise uu____9588))
end));
(

let uu____9593 = (

let uu____9597 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____9597 lb.FStar_Syntax_Syntax.lbdef))
in (match (uu____9593) with
| (e, c, g) -> begin
((

let uu____9604 = (

let uu____9605 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____9605)))
in (match (uu____9604) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end
| uu____9606 -> begin
()
end));
(

let lb1 = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e)
in ((lb1), (g)));
)
end));
))))
in (FStar_All.pipe_right uu____9553 FStar_List.unzip))
in (match (uu____9548) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____9634 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9634) with
| (env1, uu____9644) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____9650 = (check_lbtyp top_level env lb)
in (match (uu____9650) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (univ_vars1 <> []))) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end
| uu____9673 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____9677 = (tc_maybe_toplevel_term (

let uu___124_9683 = env11
in {FStar_TypeChecker_Env.solver = uu___124_9683.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___124_9683.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___124_9683.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___124_9683.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___124_9683.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___124_9683.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___124_9683.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___124_9683.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___124_9683.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___124_9683.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___124_9683.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___124_9683.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___124_9683.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___124_9683.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___124_9683.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___124_9683.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___124_9683.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___124_9683.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___124_9683.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___124_9683.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___124_9683.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___124_9683.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___124_9683.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___124_9683.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___124_9683.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___124_9683.FStar_TypeChecker_Env.is_native_tactic}) e11)
in (match (uu____9677) with
| (e12, c1, g1) -> begin
(

let uu____9692 = (

let uu____9695 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____9699 -> FStar_TypeChecker_Err.ill_kinded_type))) uu____9695 e12 c1 wf_annot))
in (match (uu____9692) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in ((

let uu____9709 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9709) with
| true -> begin
(

let uu____9710 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9711 = (FStar_Syntax_Print.term_to_string c11.FStar_Syntax_Syntax.res_typ)
in (

let uu____9712 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" uu____9710 uu____9711 uu____9712))))
end
| uu____9713 -> begin
()
end));
((e12), (univ_vars1), (c11), (g11), ((FStar_Option.isSome topt)));
))
end))
end)));
)
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt Prims.list * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end
| uu____9734 -> begin
()
end);
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env));
)
end
| uu____9738 -> begin
(

let uu____9739 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____9739) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____9766 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars1), (univ_opening), (uu____9766)))
end
| uu____9770 -> begin
(

let uu____9771 = (FStar_Syntax_Util.type_u ())
in (match (uu____9771) with
| (k, uu____9782) -> begin
(

let uu____9783 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____9783) with
| (t2, uu____9795, g) -> begin
((

let uu____9798 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____9798) with
| true -> begin
(

let uu____9799 = (

let uu____9800 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____9800))
in (

let uu____9801 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____9799 uu____9801)))
end
| uu____9802 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____9804 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____9804))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____9809 -> (match (uu____9809) with
| (x, imp) -> begin
(

let uu____9820 = (FStar_Syntax_Util.type_u ())
in (match (uu____9820) with
| (tu, u) -> begin
((

let uu____9832 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____9832) with
| true -> begin
(

let uu____9833 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____9834 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____9835 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" uu____9833 uu____9834 uu____9835))))
end
| uu____9836 -> begin
()
end));
(

let uu____9837 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____9837) with
| (t, uu____9848, g) -> begin
(

let x1 = (((

let uu___125_9854 = x
in {FStar_Syntax_Syntax.ppname = uu___125_9854.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___125_9854.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in ((

let uu____9856 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____9856) with
| true -> begin
(

let uu____9857 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____9858 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____9857 uu____9858)))
end
| uu____9859 -> begin
()
end));
(

let uu____9860 = (push_binding env x1)
in ((x1), (uu____9860), (g), (u)));
))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> (

let rec aux = (fun env1 bs1 -> (match (bs1) with
| [] -> begin
(([]), (env1), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs2 -> begin
(

let uu____9911 = (tc_binder env1 b)
in (match (uu____9911) with
| (b1, env', g, u) -> begin
(

let uu____9934 = (aux env' bs2)
in (match (uu____9934) with
| (bs3, env'1, g', us) -> begin
(

let uu____9963 = (

let uu____9964 = (FStar_TypeChecker_Rel.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g uu____9964))
in (((b1)::bs3), (env'1), (uu____9963), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____10018 uu____10019 -> (match (((uu____10018), (uu____10019))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____10056 = (tc_term env1 t)
in (match (uu____10056) with
| (t1, uu____10066, g') -> begin
(

let uu____10068 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____10068)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p uu____10094 -> (match (uu____10094) with
| (pats1, g) -> begin
(

let uu____10108 = (tc_args env p)
in (match (uu____10108) with
| (args, g') -> begin
(

let uu____10116 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats1), (uu____10116)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____10124 = (tc_maybe_toplevel_term env e)
in (match (uu____10124) with
| (e1, c, g) -> begin
(

let uu____10134 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____10134) with
| true -> begin
((e1), (c), (g))
end
| uu____10138 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (c.FStar_Syntax_Syntax.comp ())
in (

let c2 = (norm_c env c1)
in (

let uu____10144 = (

let uu____10147 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____10147) with
| true -> begin
(

let uu____10150 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____10150), (false)))
end
| uu____10151 -> begin
(

let uu____10152 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____10152), (true)))
end))
in (match (uu____10144) with
| (target_comp, allow_ghost) -> begin
(

let uu____10158 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____10158) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____10164 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in ((e1), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (uu____10164)))
end
| uu____10165 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____10170 = (

let uu____10171 = (

let uu____10174 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in ((uu____10174), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____10171))
in (FStar_Pervasives.raise uu____10170))
end
| uu____10178 -> begin
(

let uu____10179 = (

let uu____10180 = (

let uu____10183 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in ((uu____10183), (e1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____10180))
in (FStar_Pervasives.raise uu____10179))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____10196 = (tc_tot_or_gtot_term env t)
in (match (uu____10196) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____10218 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____10218) with
| true -> begin
(

let uu____10219 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____10219))
end
| uu____10220 -> begin
()
end));
(

let env1 = (

let uu___126_10222 = env
in {FStar_TypeChecker_Env.solver = uu___126_10222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___126_10222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___126_10222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___126_10222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___126_10222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___126_10222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___126_10222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___126_10222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___126_10222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___126_10222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___126_10222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___126_10222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___126_10222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___126_10222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___126_10222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___126_10222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___126_10222.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___126_10222.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___126_10222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___126_10222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___126_10222.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___126_10222.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___126_10222.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___126_10222.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___126_10222.FStar_TypeChecker_Env.is_native_tactic})
in (

let uu____10225 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)
with
| FStar_Errors.Error (msg, uu____10246) -> begin
(

let uu____10247 = (

let uu____10248 = (

let uu____10251 = (FStar_TypeChecker_Env.get_range env1)
in (((Prims.strcat "Implicit argument: " msg)), (uu____10251)))
in FStar_Errors.Error (uu____10248))
in (FStar_Pervasives.raise uu____10247))
end
in (match (uu____10225) with
| (t, c, g) -> begin
(

let uu____10261 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____10261) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____10267 -> begin
(

let uu____10268 = (

let uu____10269 = (

let uu____10272 = (

let uu____10273 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____10273))
in (

let uu____10274 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____10272), (uu____10274))))
in FStar_Errors.Error (uu____10269))
in (FStar_Pervasives.raise uu____10268))
end))
end)));
))


let level_of_type_fail = (fun env e t -> (

let uu____10299 = (

let uu____10300 = (

let uu____10303 = (

let uu____10304 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____10304 t))
in (

let uu____10305 = (FStar_TypeChecker_Env.get_range env)
in ((uu____10303), (uu____10305))))
in FStar_Errors.Error (uu____10300))
in (FStar_Pervasives.raise uu____10299)))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____10325 = (

let uu____10326 = (FStar_Syntax_Util.unrefine t1)
in uu____10326.FStar_Syntax_Syntax.n)
in (match (uu____10325) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____10330 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____10332 -> begin
(

let uu____10333 = (FStar_Syntax_Util.type_u ())
in (match (uu____10333) with
| (t_u, u) -> begin
(

let env1 = (

let uu___129_10339 = env
in {FStar_TypeChecker_Env.solver = uu___129_10339.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___129_10339.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___129_10339.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___129_10339.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___129_10339.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___129_10339.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___129_10339.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___129_10339.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___129_10339.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___129_10339.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___129_10339.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___129_10339.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___129_10339.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___129_10339.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___129_10339.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___129_10339.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___129_10339.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___129_10339.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___129_10339.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___129_10339.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___129_10339.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___129_10339.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___129_10339.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___129_10339.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___129_10339.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___129_10339.FStar_TypeChecker_Env.is_native_tactic})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____10343 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____10343))
end
| uu____10344 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____10355 = (

let uu____10356 = (FStar_Syntax_Subst.compress e)
in uu____10356.FStar_Syntax_Syntax.n)
in (match (uu____10355) with
| FStar_Syntax_Syntax.Tm_bvar (uu____10361) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____10366) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____10383) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____10394) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10409, t) -> begin
t
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____10428) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10435 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10435) with
| ((uu____10442, t), uu____10444) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____10447, (FStar_Util.Inl (t), uu____10449), uu____10450) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____10486, (FStar_Util.Inr (c), uu____10488), uu____10489) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____10532; FStar_Syntax_Syntax.pos = uu____10533; FStar_Syntax_Syntax.vars = uu____10534}, us) -> begin
(

let uu____10540 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10540) with
| ((us', t), uu____10549) -> begin
((match (((FStar_List.length us) <> (FStar_List.length us'))) with
| true -> begin
(

let uu____10561 = (

let uu____10562 = (

let uu____10565 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (uu____10565)))
in FStar_Errors.Error (uu____10562))
in (FStar_Pervasives.raise uu____10561))
end
| uu____10566 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____10577 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____10578) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____10586) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____10603 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____10603) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____10618 -> (match (uu____10618) with
| (b, uu____10622) -> begin
(

let uu____10623 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____10623))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____10628 = (universe_of_aux env res)
in (level_of_type env res uu____10628)))
in (

let u_c = (

let uu____10630 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____10630) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____10633 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____10633))
end))
in (

let u = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max ((u_c)::us)))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))))
end))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rec type_of_head = (fun retry hd2 args1 -> (

let hd3 = (FStar_Syntax_Subst.compress hd2)
in (match (hd3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____10703) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____10713) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____10737) -> begin
(

let uu____10738 = (universe_of_aux env hd3)
in ((uu____10738), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____10748) -> begin
(

let uu____10749 = (universe_of_aux env hd3)
in ((uu____10749), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10759) -> begin
(

let uu____10770 = (universe_of_aux env hd3)
in ((uu____10770), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____10780) -> begin
(

let uu____10785 = (universe_of_aux env hd3)
in ((uu____10785), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____10795) -> begin
(

let uu____10813 = (universe_of_aux env hd3)
in ((uu____10813), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____10823) -> begin
(

let uu____10828 = (universe_of_aux env hd3)
in ((uu____10828), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____10838) -> begin
(

let uu____10839 = (universe_of_aux env hd3)
in ((uu____10839), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10849) -> begin
(

let uu____10857 = (universe_of_aux env hd3)
in ((uu____10857), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____10867) -> begin
(

let uu____10872 = (universe_of_aux env hd3)
in ((uu____10872), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____10882) -> begin
(

let uu____10883 = (universe_of_aux env hd3)
in ((uu____10883), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____10893, (hd4)::uu____10895) -> begin
(

let uu____10938 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____10938) with
| (uu____10948, uu____10949, hd5) -> begin
(

let uu____10963 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____10963) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____10998 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let uu____11000 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____11000) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____11035 -> begin
(

let uu____11036 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____11036) with
| (env1, uu____11050) -> begin
(

let env2 = (

let uu___130_11054 = env1
in {FStar_TypeChecker_Env.solver = uu___130_11054.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_11054.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_11054.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_11054.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_11054.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_11054.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_11054.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_11054.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_11054.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_11054.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_11054.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_11054.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_11054.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___130_11054.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___130_11054.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_11054.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_11054.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___130_11054.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___130_11054.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_11054.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___130_11054.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___130_11054.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___130_11054.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___130_11054.FStar_TypeChecker_Env.is_native_tactic})
in ((

let uu____11056 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____11056) with
| true -> begin
(

let uu____11057 = (

let uu____11058 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____11058))
in (

let uu____11059 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____11057 uu____11059)))
end
| uu____11060 -> begin
()
end));
(

let uu____11061 = (tc_term env2 hd3)
in (match (uu____11061) with
| (uu____11074, {FStar_Syntax_Syntax.eff_name = uu____11075; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____11077; FStar_Syntax_Syntax.comp = uu____11078}, g) -> begin
((

let uu____11088 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____11088 FStar_Pervasives.ignore));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____11096 = (type_of_head true hd1 args)
in (match (uu____11096) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____11125 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____11125) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match (((FStar_List.length bs) = (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____11161 -> begin
(

let uu____11162 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____11162))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____11165, (hd1)::uu____11167) -> begin
(

let uu____11210 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____11210) with
| (uu____11213, uu____11214, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____11228, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____11262 = (universe_of_aux env e)
in (level_of_type env e uu____11262)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____11277 = (tc_binders env tps)
in (match (uu____11277) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))




