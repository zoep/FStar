module FStar.Serialize
open FStar.Char
open FStar.String

(** Helpers to escape backslashes *)

private let backslash : char = char_of_int 92

private let rec escape_spec
  (s: string)
: Ghost string
  (requires True)
  (ensures (fun _ -> True))
  (decreases (length s))
=
 let n = length s in
 if n = 0
 then make 0 backslash
 else let c_at_0 = index s 0 in
      let c_at_0_as_string = string_of_char c_at_0 in
      let replace_c_at_0_with = if c_at_0 = backslash then strcat c_at_0_as_string c_at_0_as_string else c_at_0_as_string in
      let n' = n - 1 in
      let s_1_n' = sub s 1 n' in
      strcat replace_c_at_0_with (escape_spec s_1_n')

(* Implement [escape_spec] as a tail-recursive function *)

private let rec escape_aux
  (s: string)
  (i: nat {i <= length s})
  (res: string)
: Tot string =
  if i = 0
  then res
  else let i' = i - 1 in
       let c_at_i = index s i' in
       let c_at_i_as_string = string_of_char c_at_i in
       let replace_c_at_i_with = if c_at_i = backslash then strcat c_at_i_as_string c_at_i_as_string else c_at_i_as_string in
       let res' = strcat replace_c_at_i_with res in
       escape_aux s i' res'

let escape (s: string) : Tot string = escape_aux s (length s) (make 0 backslash)

private let rec escape_aux_correct
  (s: string)
  (i: nat {i <= length s})
  (res: string)
: Lemma
  (requires (res == escape_spec (sub s i (length s - i))))
  (ensures  (escape_aux s i res == escape_spec s))
  (decreases i)
= if i = 0
  then sub_zero_length s
  else
       let i' = i - 1 in
       let c_at_i' = index s i' in
       let c_at_i'_as_string = string_of_char c_at_i' in
       let replace_c_at_i'_with = if c_at_i' = backslash then strcat c_at_i'_as_string c_at_i'_as_string else c_at_i'_as_string in
       let res' = strcat replace_c_at_i'_with res in
       let s_i' = sub s i' (length s - i') in
       sub_sub s i' (length s - i') 1 (length s_i' - 1);
       index_sub s i' (length s - i') 0;
       escape_aux_correct s i' res'

private let escape_correct
  (s: string)
: Lemma
  (ensures (escape s == escape_spec s))
= escape_aux_correct s (length s) (make 0 backslash)

(* Properties of [escape]: every sequence of backslashes always has an even length *)

let rec backslashes_in_pairs
  (s: string)
: Ghost bool
  (requires True)
  (ensures (fun _ -> True))
  (decreases (length s))
= let n = length s in
  if n = 0
  then true
  else if index s 0 = backslash
       then n > 1 &&
            index s 1 = backslash &&
            backslashes_in_pairs (sub s 2 (n-2))
       else backslashes_in_pairs (sub s 1 (n-1))

private let rec backslashes_in_pairs_escape_spec
  (s: string)  
: Lemma
  (requires True)
  (ensures (backslashes_in_pairs (escape_spec s)))
  (decreases (length s))
  [SMTPat (backslashes_in_pairs (escape_spec s))]
=
  let n = length s in
  if n = 0
  then ()
  else let c_at_0 = index s 0 in
       let c_at_0_as_string = string_of_char c_at_0 in
       length_string_of_char c_at_0;
       let _ : squash (index c_at_0_as_string 0 == c_at_0) =
         index_string_of_char c_at_0
       in
       let n' = n - 1 in
       let s_1_n' = sub s 1 n' in
       let res' = escape_spec s_1_n' in
       let res = escape_spec s in
       if c_at_0 = backslash
       then begin
	 index_strcat_l (strcat c_at_0_as_string c_at_0_as_string) res' 0;
	 index_strcat_l c_at_0_as_string c_at_0_as_string 0;
	 index_strcat_l (strcat c_at_0_as_string c_at_0_as_string) res' 1;
	 index_strcat_r c_at_0_as_string c_at_0_as_string 1;
	 backslashes_in_pairs_escape_spec s_1_n';
	 sub_strcat_r (strcat c_at_0_as_string c_at_0_as_string) res' 2 (length res - 2);
	 sub_zero_length res'
       end else begin
	 index_strcat_l c_at_0_as_string res' 0;
	 backslashes_in_pairs_escape_spec s_1_n';
	 sub_strcat_r c_at_0_as_string res' 1 (length res - 1);
	 sub_zero_length res'
       end

private let rec unescape_spec
  (s: string {backslashes_in_pairs s})
: Ghost string
  (requires True)
  (ensures (fun _ -> True))
  (decreases (length s))
= let n = length s in
  if n = 0
  then make 0 backslash
  else let c = index s 0 in
       let c_as_string = string_of_char c in
       if c = backslash
       then strcat c_as_string (unescape_spec (sub s 2 (n-2)))
       else strcat c_as_string (unescape_spec (sub s 1 (n-1)))

(* Same as before: unescape as a tail-recursive function *)

let rec backslashes_in_pairs_strcat
  (s1: string {backslashes_in_pairs s1})
  (s2: string {backslashes_in_pairs s2})
: Lemma
  (requires True)
  (ensures (backslashes_in_pairs (strcat s1 s2)))
  (decreases (length s1))
  [SMTPat (backslashes_in_pairs (strcat s1 s2))]
= let n1 = length s1 in
  if n1 = 0
  then strcat_empty_l s1 s2
  else let c = index s1 0 in
       let _ : squash (index (strcat s1 s2) 0 == c) =
        index_strcat_l s1 s2 0
       in
       if c = backslash
       then
        let _ : squash (index (strcat s1 s2) 1 == backslash) =
	 index_strcat_l s1 s2 1
	in
	let _ : squash (sub (strcat s1 s2) 2 (length (strcat s1 s2) - 2) == strcat (sub s1 2 (length s1 - 2)) s2) =
	 sub_strcat s1 s2 2 (length (strcat s1 s2) - 2);
	 sub_zero_length s2
	in
	backslashes_in_pairs_strcat (sub s1 2 (length s1 - 2)) s2
       else
        let _ : squash (sub (strcat s1 s2) 1 (length (strcat s1 s2) - 1) == strcat (sub s1 1 (length s1 - 1)) s2) =
	 sub_strcat s1 s2 1 (length (strcat s1 s2) - 1);
	 sub_zero_length s2
	in
	backslashes_in_pairs_strcat (sub s1 1 (length s1 - 1)) s2

let backslashes_in_pairs_backslash
: squash (backslashes_in_pairs (strcat (string_of_char backslash) (string_of_char backslash)))
= let c = string_of_char backslash in
  let s = strcat c c in
  let _ = index_string_of_char backslash in
  let _ : squash (index s 0 == backslash) = index_strcat_l c c 0 in
  let _ : squash (index s 1 == backslash) = index_strcat_r c c 1 in
  ()

let backslashes_in_pairs_not_backslash
  (c: char {c <> backslash})
: Lemma
  (ensures (backslashes_in_pairs (string_of_char c)))
= let s = string_of_char c in
  let n = length s in
  let _ : squash (~ (index s 0 == backslash)) = index_string_of_char c in
  ()


(*
private let rec unescape_aux
  (s: string)
  (i: nat {i <= length s /\ backslashes_in_pairs (sub s i (length s - i))})
  (res: string)
: Pure string
  (requires True)
  (ensures (fun _ -> True))
  (decreases (length s - i))
= if i = length s
  then res
  else let j = length s - i in
*)

private let rec unescape_spec_escape_spec
  (s: string)
: Lemma
  (requires True)
  (ensures (unescape_spec (escape_spec s) == s))
  (decreases (length s))
= let n = length s in
  if n = 0
  then empty_unique s (make 0 backslash)
  else
    let c_at_0 = index s 0 in
    let c_at_0_as_string = string_of_char c_at_0 in
    index_string_of_char c_at_0;
    let res = escape_spec s in
    let s_1_n' = sub s 1 (n - 1) in
    let _ : squash (c_at_0_as_string == sub s 0 1) =
     let (l : nat {0 + l <= length s}) = 1 in
     FStar.Classical.forall_intro (index_sub s 0 l);
     eq_intro (sub s 0 1) c_at_0_as_string
    in
    let _ : squash (s == strcat c_at_0_as_string s_1_n') =
     strcat_sub s 1
    in
    let res' = escape_spec s_1_n' in
    let _ : squash (unescape_spec res' == s_1_n') =
     unescape_spec_escape_spec s_1_n'
    in
    if c_at_0 = backslash
    then begin
      let _ : squash (index res 0 == backslash) =
	index_strcat_l (strcat c_at_0_as_string c_at_0_as_string) res' 0;
	index_strcat_l c_at_0_as_string c_at_0_as_string 0
      in
      let _ : squash (sub res 2 (length res - 2) == res') =
        sub_strcat_r (strcat c_at_0_as_string c_at_0_as_string) res' 2 (length res - 2);
	sub_zero_length res'
      in
      ()
    end else begin
      let _ : squash (~ (index res 0 == backslash)) =
	index_strcat_l c_at_0_as_string res' 0
      in
      let _ : squash (sub res 1 (length res - 1) == res') =
        sub_strcat_r c_at_0_as_string res' 1 (length res - 1);
	sub_zero_length res'
      in
      ()
    end



(*
      strcat_sub s 1;
      sub_strcat_l c_at_0_as_string s_1_n' 0 1 ;
      unescape_spec_escape_spec s_1_n'

    let replace_c_at_0_with = if c_at_0 = backslash then strcat c_at_0_as_string c_at_0_as_string else c_at_0_as_string in
    let n' = n - 1 in
    let s_1_n' = sub s 1 n' in
    strcat replace_c_at_0_with (escape_spec s_1_n')
    let c = index s 0 in
    if c = backslash
    then admit ()
    else unescape_spec_escape_spec (sub s 1 (n-1))
  end
*)       

noeq type serializable (t: Type) =
| Serializable :
  (to_string : (t -> Tot string)) ->
  (from_string : (string -> Tot (option t))) ->
  (from_string_to_string: squash (forall x . from_string (to_string x) == Some x)) ->
  (to_string_from_string: squash (forall s x . from_string s == Some x ==> to_string x == s)) ->
  serializable t

let to_string (#t: Type) (#h: serializable t) (x: t) : Tot string =
  Serializable?.to_string h x

let from_string (#t: Type) (#h: serializable t) (s: string): Tot (option t) =
  Serializable?.from_string h s

let from_string_to_string
  (#t: Type)
  (#h: serializable t)
: Lemma
  (ensures forall (x: t) . from_string #t #h (to_string #t #h x) == Some x)
= Serializable?.from_string_to_string h
