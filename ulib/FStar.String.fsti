(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.String

open FStar.All

type char = FStar.Char.char

(* Not much in here; we should extend and refine this interface *)

val length:  string -> Tot nat
val make: l:nat -> char -> Tot (s:string {length s = l}) 
val split:   list char -> string -> Tot (list string)
val strcat:  s0:string -> s1:string -> Tot (s:string{length s = length s0 + length s1})
val concat:  string -> list string -> Tot string
val compare: string -> string -> Tot int
val strlen:  string -> Tot nat
val lowercase:  string -> Tot string

val index: s:string -> n:nat {n < length s} -> Tot char
val sub: s:string -> i:nat -> l:nat{i + l <= length s} -> Tot string

(* may fail with index out of bounds *)
(* Second argument is a length, not an index. *)
val substring: string -> int -> int -> ML string
val get: string -> int -> ML char
val collect: (char -> string) -> string -> ML string

val list_of_string : string -> Tot (list char)

let string_of_char (c:char) : Tot string = make 1 c

(** Equality by extensionality *)

val eq_intro
  (s1 s2: string)
: Lemma
  (requires 
   (length s1 == length s2 /\
    (forall (i: nat {i < length s1}) . index s1 i == index s2 i)))
  (ensures (s1 == s2))

let empty_unique
    (s1 s2: string)
: Lemma
  (requires (length s1 == 0 /\ length s2 == 0))
  (ensures (s1 == s2))
= eq_intro s1 s2

(** Properties of [strcat] *)

val index_strcat_l
  (s1 s2: string)
  (i: nat {i < length s1})
: Lemma
  (ensures (index (strcat s1 s2) i == index s1 i))

val index_strcat_r
  (s1 s2: string)
  (i: nat {length s1 <= i /\ i < length s1 + length s2})
: Lemma
  (ensures (index (strcat s1 s2) i == index s2 (i - length s1)))

let strcat_assoc
  (s1 s2 s3: string)
: Lemma
  (ensures (strcat (strcat s1 s2) s3 == strcat s1 (strcat s2 s3)))
= FStar.Classical.forall_intro (index_strcat_l s1 s2);
  FStar.Classical.forall_intro (index_strcat_r s1 s2);
  FStar.Classical.forall_intro (index_strcat_l (strcat s1 s2) s3);
  FStar.Classical.forall_intro (index_strcat_r (strcat s1 s2) s3);
  FStar.Classical.forall_intro (index_strcat_l s2 s3);
  FStar.Classical.forall_intro (index_strcat_r s2 s3);
  FStar.Classical.forall_intro (index_strcat_l s1 (strcat s2 s3));
  FStar.Classical.forall_intro (index_strcat_r s1 (strcat s2 s3));
  eq_intro (strcat (strcat s1 s2) s3) (strcat s1 (strcat s2 s3))

let strcat_empty_l
  (s1 s2: string)
: Lemma
  (requires (length s1 == 0))
  (ensures (strcat s1 s2 == s2))
= FStar.Classical.forall_intro (index_strcat_l s1 s2);
  FStar.Classical.forall_intro (index_strcat_r s1 s2);
  eq_intro (strcat s1 s2) s2

let strcat_empty_r
  (s1 s2: string)
: Lemma
  (requires (length s2 == 0))
  (ensures (strcat s1 s2 == s1))
= FStar.Classical.forall_intro (index_strcat_l s1 s2);
  FStar.Classical.forall_intro (index_strcat_r s1 s2);
  eq_intro (strcat s1 s2) s1

(** Properties of [sub] *)

val length_sub
  (s: string)
  (i: nat)
  (l: (l: nat {i + l <= length s}))
: Lemma
  (requires True)
  (ensures length (sub s i l) == l)
  [SMTPat (length (sub s i l))]

val index_sub
  (s: string)
  (i: nat)
  (l: nat {i + l <= length s})
  (i': nat {i' < l})
: Lemma
  (ensures (index (sub s i l) i' == index s (i + i')))

let sub_zero_length
  (s: string)
: Lemma
  (ensures (sub s 0 (length s) == s))
= FStar.Classical.forall_intro (index_sub s 0 (length s));
  eq_intro (sub s 0 (length s)) s

let sub_sub
  (s: string)
  (i1: nat)
  (l1: nat {i1 + l1 <= length s})
  (i2: nat)
  (l2: nat {i2 + l2 <= l1})
: Lemma
  (ensures (sub (sub s i1 l1) i2 l2 == sub s (i1 + i2) l2))
= FStar.Classical.forall_intro (index_sub (sub s i1 l1) i2 l2);
  FStar.Classical.forall_intro (index_sub s i1 l1);
  FStar.Classical.forall_intro (index_sub s (i1 + i2) l2);
  eq_intro (sub (sub s i1 l1) i2 l2) (sub s (i1 + i2) l2)

let sub_strcat_l
 (s1 s2: string)
 (i: nat)
 (l: nat {i + l <= length s1})
: Lemma
  (ensures (sub (strcat s1 s2) i l == sub s1 i l))
= FStar.Classical.forall_intro (index_sub (strcat s1 s2) i l);
  FStar.Classical.forall_intro (index_strcat_l s1 s2);
  FStar.Classical.forall_intro (index_sub s1 i l);
  eq_intro (sub (strcat s1 s2) i l) (sub s1 i l)

let sub_strcat_r
 (s1 s2: string)
 (i: nat {length s1 <= i})
 (l: nat {i - length s1 + l <= length s2})
: Lemma
  (ensures (sub (strcat s1 s2) i l == sub s2 (i - length s1) l))
= FStar.Classical.forall_intro (index_sub (strcat s1 s2) i l);
  FStar.Classical.forall_intro (index_strcat_r s1 s2);
  FStar.Classical.forall_intro (index_sub s2 (i - length s1) l);
  eq_intro (sub (strcat s1 s2) i l) (sub s2 (i - length s1) l)

let sub_strcat
 (s1 s2: string)
 (i: nat {i <= length s1})
 (l: nat {length s1 <= i + l /\ i + l <= length s1 + length s2})
: Lemma
  (ensures (sub (strcat s1 s2) i l == strcat (sub s1 i (length s1 - i)) (sub s2 0 ((i + l) - length s1))))
= FStar.Classical.forall_intro (index_sub (strcat s1 s2) i l);
  FStar.Classical.forall_intro (index_strcat_l s1 s2);
  FStar.Classical.forall_intro (index_strcat_r s1 s2);
  FStar.Classical.forall_intro (index_strcat_l (sub s1 i (length s1 - i)) (sub s2 0 ((i + l) - length s1)));
  FStar.Classical.forall_intro (index_strcat_r (sub s1 i (length s1 - i)) (sub s2 0 ((i + l) - length s1)));
  FStar.Classical.forall_intro (index_sub s1 i (length s1 - i));
  FStar.Classical.forall_intro (index_sub s2 0 ((i + l) - length s1));
  eq_intro (sub (strcat s1 s2) i l) (strcat (sub s1 i (length s1 - i)) (sub s2 0 ((i + l) - length s1)))

let strcat_sub
  (s: string)
  (l: nat {l <= length s})
: Lemma
  (ensures (s == strcat (sub s 0 l) (sub s l (length s - l))))
= FStar.Classical.forall_intro (index_strcat_l (sub s 0 l) (sub s l (length s - l)));
  FStar.Classical.forall_intro (index_strcat_r (sub s 0 l) (sub s l (length s - l)));
  FStar.Classical.forall_intro (index_sub s 0 l);
  FStar.Classical.forall_intro (index_sub s l (length s - l));
  eq_intro s (strcat (sub s 0 l) (sub s l (length s - l)))

(* Specification of [make] *)

val index_make
  (l: nat)
  (c: char)
: Lemma
  (ensures (forall (i: nat {i < l}) . index (make l c) i == c))

(* Properties of [string_of_char] *)

let length_string_of_char
  (c: char)
: Lemma
  (ensures (length (string_of_char c) == 1))
= ()

let index_string_of_char
  (c: char)
: Lemma
  (ensures (forall (i: nat {i < 1}) . index (string_of_char c) i == c))
= index_make 1 c
