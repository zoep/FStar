(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi,
                       Microsoft Research, University of Maryland

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
(** Propositional sets (on any types): membership is a predicate *)
module FStar.TSet
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

abstract let set (a: Type): Tot Type = a -> Tot prop
abstract type equal (#a:Type) (s1:set a) (s2:set a) = forall x. s1 x <==> s2 x

(* destructors *)

abstract val mem : 'a -> set 'a -> Tot Type0
let mem x s = s x

(* constructors *)
abstract let empty (#a: Type) : Tot (set a) = let p (x: a) : Tot prop = False in p

abstract val singleton  : 'a -> Tot (set 'a)
abstract val union      : set 'a -> set 'a -> Tot (set 'a)
abstract val intersect  : set 'a -> set 'a -> Tot (set 'a)
abstract val complement : set 'a -> Tot (set 'a)

let singleton x     = let p y : Tot prop = y == x in p
let union s1 s2     = let p x : Tot prop = s1 x \/ s2 x in p
let intersect s1 s2 = let p x : Tot prop = s1 x /\ s2 x in p
let complement s    = let p x : Tot prop = ~ (s x) in p

(* ops *)
let subset (#a:Type) (s1:set a) (s2:set a) : Tot Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
abstract val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (~ (mem x empty)))
   [SMTPat (mem x empty)]

abstract val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) <==> (x==y)))
   [SMTPat (mem y (singleton x))]

abstract val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) == (mem x s1 \/ mem x s2)))
   [SMTPat (mem x (union s1 s2))]

abstract val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) == (mem x s1 /\ mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

abstract val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) == ~(mem x s)))
   [SMTPat (mem x (complement s))]

abstract val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

abstract val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

let mem_empty      #a x       = ()
let mem_singleton  #a x y     = ()
let mem_union      #a x s1 s2 = ()
let mem_intersect  #a x s1 s2 = ()
let mem_complement #a x s     = ()
let subset_mem     #a s1 s2   = ()
let mem_subset     #a s1 s2   = ()

(* extensionality *)

abstract val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 <==> mem x s2))
    (ensures (equal s1 s2))
    [SMTPatT (equal s1 s2)]

abstract val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPatT (equal s1 s2)]

abstract val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPatT (equal s1 s2)]

let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim  #a s1 s2 = PredicateExtensionality.predicateExtensionality a s1 s2
let lemma_equal_refl  #a s1 s2 = ()

(* NOTE: the following lemmas should be provable abstractly *)

let union_comm
  (#a: Type)
  (x y: set a)
: Lemma
  (requires True)
  (ensures (union x y == union y x))
//  [SMTPat (union x y)]
= lemma_equal_elim (union x y) (union y x)

let union_empty_l
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (union empty x == x))
  [SMTPat (union empty x)]
= lemma_equal_elim (union empty x) x

let union_empty_r
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (union x empty == x))
  [SMTPat (union x empty)]
= lemma_equal_elim (union x empty) x

let union_assoc
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires True)
  (ensures (union x (union y z) == union (union x y) z))
//  [SMTPat (union (union x y) z)]
= lemma_equal_elim (union x (union y z)) (union (union x y) z)

let intersect_comm
  (#a: Type)
  (x y: set a)
: Lemma
  (requires True)
  (ensures (intersect x y == intersect y x))
//  [SMTPat (intersect x y)]
= lemma_equal_elim (intersect x y) (intersect y x)

let intersect_empty_l
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (intersect empty x == empty))
  [SMTPat (intersect empty x)]
= lemma_equal_elim (intersect empty x) empty

let intersect_empty_r
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (intersect x empty == empty))
  [SMTPat (intersect x empty)]
= lemma_equal_elim (intersect x empty) empty

let intersect_assoc
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires True)
  (ensures (intersect x (intersect y z) == intersect (intersect x y) z))
//  [SMTPat (intersect (intersect x y) z)]
= lemma_equal_elim (intersect x (intersect y z)) (intersect (intersect x y) z)

let union_intersect
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires True)
  (ensures (x `union` (y `intersect` z) == (x `union` y) `intersect` (x `union` z)))
//  [SMTPat (x `union` (y `intersect` z))] // TODO: resolve conflict with union_subset_simpl below
= lemma_equal_elim (x `union` (y `intersect` z)) ((x `union` y) `intersect` (x `union` z))

let intersect_union
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires True)
  (ensures (x `intersect` (y `union` z) == (x `intersect` y) `union` (x `intersect` z)))
//  [SMTPat (x `intersect` (y `union` z))] // TODO: resolve conflict with intersect_subset_simpl below
= lemma_equal_elim (x `intersect` (y `union` z)) ((x `intersect` y) `union` (x `intersect` z))

let complement_complement
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (complement (complement x) == x))
  [SMTPat (complement (complement x))]
= lemma_equal_elim (complement (complement x)) x

let complement_union
  (#a: Type)
  (x y: set a)
: Lemma
  (requires True)
  (ensures (complement (x `union` y) == complement x `intersect` complement y))
  [SMTPat (complement (x `union` y))]
= lemma_equal_elim (complement (x `union` y)) (complement x `intersect` complement y)

let complement_intersect
  (#a: Type)
  (x y: set a)
: Lemma
  (requires True)
  (ensures (complement (x `intersect` y) == complement x `union` complement y))
  [SMTPat (complement (x `intersect` y))]
= lemma_equal_elim (complement (x `intersect` y)) (complement x `union` complement y)

let subset_refl
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (x `subset` x))
  [SMTPat (x `subset` x)]
= ()

let subset_trans
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires (x `subset` y /\ y `subset` z))
  (ensures (x `subset` z))
  [SMTPatT (x `subset` y); SMTPatT (y `subset` z)]
= ()

let subset_antisym
  (#a: Type)
  (x y: set a)
: Lemma
  (requires (x `subset` y /\ y `subset` x))
  (ensures (x == y))
  [SMTPatT (x `subset` y); SMTPatT (y `subset` x)]
= lemma_equal_elim x y

let subset_empty
  (#a: Type)
  (x: set a)
: Lemma
  (requires True)
  (ensures (empty `subset` x))
  [SMTPat (empty `subset` x)]
= ()

let subset_union_l
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires (x `subset` z /\ y `subset` z))
  (ensures ((x `union` y) `subset` z))
  [SMTPat ((x `union` y) `subset` z)]
= ()

let subset_union_r
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires (x `subset` y \/ x `subset` z))
  (ensures (x `subset` (y `union` z)))
  [SMTPat (x `subset` (y `union` z))]
= ()

let subset_intersect_l
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires (x `subset` z \/ y `subset` z))
  (ensures ((x `intersect` y) `subset` z))
  [SMTPat ((x `intersect` y) `subset` z)]
= ()

let subset_intersect_r
  (#a: Type)
  (x y z: set a)
: Lemma
  (requires (x `subset` y /\ x `subset` z))
  (ensures (x `subset` (y `intersect` z)))
  [SMTPat (x `subset` (y `intersect` z))]
= ()

let union_subset_simpl
  (#a: Type)
  (x y: set a)
: Lemma
  (requires (x `subset` y))
  (ensures (x `union` y == y))
  [SMTPatT (x `subset` y); SMTPat (x `union` y)]
= lemma_equal_elim (x `union` y) y

let intersect_subset_simpl
  (#a: Type)
  (x y: set a)
: Lemma
  (requires (x `subset` y))
  (ensures (x `intersect` y == x))
  [SMTPatT (x `subset` y); SMTPat (x `intersect` y)]
= lemma_equal_elim (x `intersect` y) x

abstract let tset_of_set
  (#a:eqtype)
  (s:Set.set a)
: Tot (set a)
= let f
    (x: a)
  : Tot prop
  = Set.mem x s == true
  in
  f

private let lemma_mem_tset_of_set_l (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures (mem x (tset_of_set s) ==> Set.mem x s))
  = ()

private let lemma_mem_tset_of_set_r (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures (Set.mem x s ==> mem x (tset_of_set s)))
  = ()

let lemma_mem_tset_of_set (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures  (Set.mem x s <==> mem x (tset_of_set s)))
	 [SMTPat (mem x (tset_of_set s))]
  = ()
