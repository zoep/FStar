#light "off"

open Prims
open FStar
open FStar.Range
open FStar.Ident
open FStar.Const
open FStar.Syntax.Syntax
open FStar.Syntax.Util


type search_result =
  | FromEnv  of lident           (* A lident which should be resolved with the environment *)
  | LocalVar of bv               (* A local variable *)
  | Resolved of either<lident, string> * term    (* An entirely resolved name or constant *)

let option_or x f = match x with
    | None -> f ()
    | _ -> x

(* TODO : Check if it may be necessary to update local vars *)
let maybe_resolve_binders bs = function
    | res -> res

let search_lid range x =
  if range_contains_range (range_of_lid x) range
  then Some (FromEnv x)
  else None

let search_binder range (bv, _) =
  (* TODO : the range might fall inside the type of this binder *)
  if range_contains_range (range_of_bv bv) range
  then Some LocalVar bv
  else None

let search_const e =
  let lid_to_tm lid = lid_as_fv lid Delta_equational |> fv_to_tm in
  let type_of_int = function
      | None -> lid_to_tm C.int_lid
      | Some x -> match x with
          | C.Signed, C.Int8 -> lid_to_tm C.int8_lid
          | C.Unsigned, C.Int8 -> lid_to_tm C.uint8_lid
          | C.Signed, C.Int16 -> lid_to_tm C.int16_lid
          | C.Unsigned, C.Int16 -> lid_to_tm C.uint16_lid
          | C.Signed, C.Int32 -> lid_to_tm C.int32_lid
          | C.Unsigned, C.Int32 -> lid_to_tm C.uint32_lid
          | C.Signed, C.Int64 -> lid_to_tm C.int64_lid
          | C.Unsigned, C.Int64 -> lid_to_tm C.int64_lid
  in match e with
  (* TODO : returning Effect as lid does not makes much sense but Effect itself does not make that much sense in the first place *)
  | Const_effect -> Resolved (Inr "Effect", ktype)
  | Const_unit -> Resolved (Inr "()", lid_to_tm C.unit_lid)
  | Const_bool b -> Resolved (Inr (string_of_bool b), lid_to_tm C.bool_lid)
  | Const_int (s, t) -> Resolved (Inr s, type_of_int t)
  | Const_char c -> Resolved (Inr (string_of_char c), lid_to_tm C.char_lid)
  | Const_float d -> Resolved (Inr (float_of_string d), lid_to_tm C.float_lid)
  (* TODO : figure out how to print the 2 byte arrays below *)
  | Const_bytearray (barr, _) -> Resolved ("<some byte array>", lid_to_tm C.bytes_lid)
  | Const_string (barr, _) -> Resolved("<some string>", lid_to_tm C.string_lid)
  | Const_range -> failwith "Source program should not be able to contain these"
  | Const_reify -> failwith "Dunno what to do with that one"
  | Const_reflect _ -> failwith "Dunno what to do with that one"


let rec search_term range e =
  if not (range_contains_range (range_of_term e) range)
  then None
  else
    match e.tm with
    | Tm_bvar b -> Some (LocalVar b)
    | Tm_fvar -> Resolved (fv., fv.)
    | Tm_constant e -> search_const e
    | Tm_type u -> None (* TODO : should we answer Type for some universe ? *)
    | Tm_abs (bs, e, rettyp) ->
        option_or (List.tryPick (search_binder range) bs)
          (fun () -> search_term range e) (* TODO : can the return type be targeted ? *)
    | Tm_arrow (bs, c) ->
        option_or (List.tryPick (search_binder range) bs)
          (fun () -> search_comp range c)
    | Tm_refine (b, fml) ->
        option_or (search_binder range b) (fun () -> search_term range fml)
    | Tm_app (e, args) ->
        option_or (search_term range e) (fun () -> List.tryPick (search_arg range) args)
    | Tm_match (e, branches) ->
        option_or (search_term range e) (fun () -> List.tryPick (search_branch range) branches)
    | Tm_ascribed (e, annot, _) ->
        option_or (search_term range e)
          (fun () -> match annot with
                     | Inl t -> search_term range t
                     | Inr c -> search_comp range c)
    | Tm_let (lbs, e) ->
        option_or (List.tryPick (search_letbinding range) letbindings)
          (fun () -> search_term range e)
    | Tm_meta (e, _) -> search_term range e
    | Tm_name _
    | Tm_uinst _
    | Tm_uvar _
    | Tm_delayed _
    | Tm_unknown -> None

and search_arg range arg = (* TODO *)

and search_branch range (pattern, when_opt, body) =
    option_or (search_pat range pattern)
      (fun () -> option_or (option_bind when_opt (search_term range))
        (fun () -> search_term range body))

and search_pat range pattern = (* TODO *)

and search_comp range c = (* TODO *)

and search_letbinding range lb =
  if range_contains_range (range_of_lbname lb.lbname)
  then match lb.lbname with
      | Inl _ -> failwith "Let bindings should not be using bv as name after typechecking"
      | Inr fv ->
  (* TODO *)

let search_effect_definition range ed = (* TODO *)

let search_sub_effect range se = (* TODO *)

let search_sigelt range s =
  if not (range_contains_range (range_of_sigelt s) range)
  then None
  else match s with
    | Sig_inductive_typ (tname, _, bs, t, _, _, _, _) ->
      option_or (search_lid range tname)
        (fun () -> option_or (List.tryPick (search_binder) range bs)
                    (fun () -> search_term range t |> maybe_resolve_binders bs))
    | Sig_bundle _ -> None
    | Sig_datacon (constr, _, t, _, _, _, _, _) ->
        option_or (search_lid range constr) (fun () -> search_term range t)
    | Sig_declare_typ (tname, _, t, _, _) ->
        option_or (search_lid range tname) (fun () -> search_term range t)
    | Sig_let (lbs, _, _, _, _) ->
        List.tryPick (search_letbinding range) lbs
    | Sig_main (t, _) -> search_term range t
    | Sig_assume (tname, t, _, _) ->
        option_or (search_lid range tname) (fun () -> search_term range t)
    | Sig_new_effect (ed, _)
    | Sig_new_effect_for_free (ed, _) ->  (* This second case should not happen *)
        search_effect_definition range ed
    | Sig_sub_effect (se, _) ->
        search_sub_effect range se
    | Sig_effect_abbrev (abbrevname, _, bs, c, _, _, _) ->
        option_or (search_lid abbrevname)
          (fun () -> option_or (List.tryPick (search_binder range) bs)
           (fun () -> search_comp range c |> maybe_resolve_binders bs))


let search_modul range modul =
    (* TODO : should check that the range in in this module *)
    List.tryPick (search_sigelt range) modul.declarations
