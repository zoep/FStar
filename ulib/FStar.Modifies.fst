module FStar.Modifies

assume val heap: Type

noeq type class: nat -> (carrier: Type) -> Tot Type =
| Class:
  (level: nat) ->
  (carrier: Type) ->
  (disjoint: (carrier -> carrier -> Tot Type0)) ->
  (live: (heap -> carrier -> Tot Type0)) ->
  (contains: (heap -> carrier -> Tot Type0)) ->
  (preserved: (carrier -> heap -> heap -> Tot Type0)) ->
  (ancestor_count: (carrier -> Tot (x: nat { level > 0 ==> x > 0 } ))) ->
  (ancestor_types: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot Type)) ->
  (ancestor_class_levels: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (y:nat { y < level } ))) ->
  (ancestor_classes: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (class (ancestor_class_levels x i) (ancestor_types x i)))) ->
  (ancestor_objects: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (ancestor_types x i))) ->
  class level carrier

assume val root_type: Type
assume val root_class: class 0 root_type

(*
let enum_forall
  (n: nat { n > 0 } )
  (p: nat -> Tot Type0)
: Lemma
  (requires (p (n-1) /\ (forall (i: nat {i < n - 1}) . p i)))
  (ensures (forall (i: nat {i < n}) . p i))
  [SMTPat (forall (i: nat {i < n}) . p i)]
= ()
*)

unfold
let preserved_refl_t
  (#level: nat) (#ty: Type) (c: class level ty) 
  : Tot Type
= (x: ty) ->
  (h : heap) ->
  Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))
  [SMTPat (Class?.preserved c x h h)]

unfold
let preserved_trans_t
  (#level: nat) (#ty: Type) (c: class level ty) 
  : Tot Type
= (x: ty) ->
  (h1: heap) ->
  (h2: heap) ->
  (h3 : heap) ->
  Lemma
  (requires (Class?.preserved c x h1 h2 /\ Class?.preserved c x h2 h3))
  (ensures (Class?.preserved c x h1 h3))

unfold
let preserved_ancestors_preserved_t
  (#level: nat) (#ty: Type) (c: class level ty) 
  : Tot Type
= (x: ty) ->
  (h: heap) ->
  (h' : heap) ->
  (s: squash (Class?.ancestor_count c x > 0)) ->
  (f: (
    (i: nat { i < Class?.ancestor_count c x } ) ->
    Lemma
    (ensures (Class?.preserved (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i) h h'))
  )) ->
  Lemma
  (ensures (Class?.preserved c x h h'))

unfold
let class_disjoint_sym_t
  (#level: nat) (#ty: Type) (c: class level ty) 
  : Tot Type
= (x1: ty) ->
  (x2: ty) ->
  Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))

unfold
let level_0_class_eq_root_t
  (#level: nat) (#ty: Type) (c: class level ty) 
  : Tot Type
= squash (level == 0 ==> ty == root_type /\ c == root_class)

unfold
let class_fresh_disjoint_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (oold: ty) ->
  (onew: ty) ->
  (hbefore: heap) ->
  (hafter: heap) ->
  Lemma
  (requires (
    Class?.live c hbefore oold /\
    (~ (Class?.contains c hbefore onew)) /\
    Class?.live c hafter oold /\
    Class?.live c hafter onew
  ))
  (ensures (Class?.disjoint c oold onew))
  
unfold
let preserved_live_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (hbefore: heap) ->
  (hafter: heap) ->
  (o: ty) ->
  Lemma
  (requires (
    Class?.preserved c o hbefore hafter /\
    Class?.live c hbefore o
  ))
  (ensures (Class?.live c hafter o))

unfold
let preserved_contains_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (hbefore: heap) ->
  (hafter: heap) ->
  (o: ty) ->
  Lemma
  (requires (
    Class?.preserved c o hbefore hafter /\
    Class?.contains c hbefore o
  ))
  (ensures (Class?.contains c hafter o))

unfold
let live_contains_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (h: heap) ->
  (o: ty) ->
  Lemma
  (requires (Class?.live c h o))
  (ensures (Class?.contains c h o))

unfold
let ancestors_contains_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (h: heap) ->
  (o: ty) ->
  (s: squash (Class?.ancestor_count c o > 0)) ->
  (f: (
    (i: nat {i < Class?.ancestor_count c o } ) ->
    Lemma
    (ensures (Class?.contains (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)))
  )) ->
  Lemma
  (ensures (Class?.contains c h o))

unfold
let live_ancestors_t
  (#level: nat) (#ty: Type) (c: class level ty)
: Tot Type
= (h: heap) ->
  (o: ty) ->
  (i: nat {i < Class?.ancestor_count c o } ) ->
  Lemma
  (requires (Class?.live c h o))
  (ensures (
    Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)
  ))

noeq
type class_invariant_body (#level: nat) (#ty: Type) (c: class level ty) = {
  preserved_refl: preserved_refl_t c;
  preserved_trans: preserved_trans_t c;
  preserved_ancestors_preserved: preserved_ancestors_preserved_t c;
  class_disjoint_sym: class_disjoint_sym_t c;
  level_0_class_eq_root: level_0_class_eq_root_t c;
  class_fresh_disjoint: class_fresh_disjoint_t c;
  preserved_live: preserved_live_t c;
  preserved_contains: preserved_contains_t c;
  live_contains: live_contains_t c;
  ancestors_contains: ancestors_contains_t c;
  live_ancestors: live_ancestors_t c
}

abstract
let rec class_invariant (#level: nat) (#ty: Type) (c: class level ty)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases level)
= (squash (class_invariant_body c) /\ (forall
    (x: ty)
    (i: nat {i < Class?.ancestor_count c x})
    . (class_invariant (Class?.ancestor_classes c x i))
  ))

let class_invariant_intro
  (#level: nat) (#ty: Type) (c: class level ty)
  (b: class_invariant_body c)
: Lemma
  (requires (forall
    (x: ty)
    (i: nat {i < Class?.ancestor_count c x})
    . (class_invariant (Class?.ancestor_classes c x i))
  ))
  (ensures (class_invariant c))
= Squash.return_squash b

let class_invariant_ancestor_classes
  (#level: nat)
  (#ty: Type)
  (c: class level ty { class_invariant c } )
  (x: ty)
  (i: nat {i < Class?.ancestor_count c x})
: Lemma
  (requires True)
  (ensures (class_invariant (Class?.ancestor_classes c x i)))
  [SMTPat (class_invariant (Class?.ancestor_classes c x i))]
= ()

(** FIXME: statements are duplicated here due to the SMT patterns *)

let preserved_refl
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (x: ty)
  (h : heap)
: Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))
  [SMTPat (Class?.preserved c x h h)]
= Squash.bind_squash #_ #(Class?.preserved c x h h) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.preserved_refl x h)

let preserved_trans
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (x: ty)
  (h1: heap)
  (h2: heap)
  (h3: heap)
: Lemma
  (requires (Class?.preserved c x h1 h2 /\ Class?.preserved c x h2 h3))
  (ensures (Class?.preserved c x h1 h3))
  [SMTPatT (Class?.preserved c x h1 h2); SMTPatT (Class?.preserved c x h2 h3)]
= Squash.bind_squash #_ #(Class?.preserved c x h1 h3) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.preserved_trans x h1 h2 h3)

let preserved_ancestors_preserved
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c}) 
  (x: ty)
  (h: heap)
  (h' : heap)
: Lemma
  (requires (
    Class?.ancestor_count c x > 0 /\ (forall
    (i: nat { i < Class?.ancestor_count c x } ) .
    (Class?.preserved (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i) h h')
  )))
  (ensures (Class?.preserved c x h h'))
= Squash.bind_squash #_ #(Class?.preserved c x h h') (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.preserved_ancestors_preserved x h h' () (fun _ -> ()))

let class_disjoint_sym
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c}) 
  (x1: ty)
  (x2: ty)
: Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))
  [SMTPat (Class?.disjoint c x2 x1)]
= Squash.bind_squash #_ #(Class?.disjoint c x2 x1) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.class_disjoint_sym x1 x2)

let level_0_class_eq_root
  (#ty: Type) (c: class 0 ty {class_invariant c})
: Lemma
  (ensures (ty == root_type /\ c == root_class))
= Squash.bind_squash #_ #(0 == 0 ==> ty == root_type /\ c == root_class) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.level_0_class_eq_root)

let class_fresh_disjoint
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (oold: ty)
  (onew: ty)
  (hbefore: heap)
  (hafter: heap)
: Lemma
  (requires (
    Class?.live c hbefore oold /\
    (~ (Class?.contains c hbefore onew)) /\
    Class?.live c hafter oold /\
    Class?.live c hafter onew
  ))
  (ensures (Class?.disjoint c oold onew))
  [SMTPatT (Class?.live c hbefore oold); SMTPatT (~ (Class?.contains c hbefore onew)); SMTPatT (Class?.live c hafter oold); SMTPatT (Class?.live c hafter onew)]
= Squash.bind_squash #_ #(Class?.disjoint c oold onew) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.class_fresh_disjoint oold onew hbefore hafter)

let preserved_live
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (hbefore: heap)
  (hafter: heap)
  (o: ty)
: Lemma
  (requires (
    Class?.preserved c o hbefore hafter /\
    Class?.live c hbefore o
  ))
  (ensures (Class?.live c hafter o))
  [SMTPatT (Class?.preserved c o hbefore hafter); SMTPatT (Class?.live c hbefore o)]
= Squash.bind_squash #_ #(Class?.live c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.preserved_live hbefore hafter o)

let preserved_contains_t
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (hbefore: heap)
  (hafter: heap)
  (o: ty)
: Lemma
  (requires (
    Class?.preserved c o hbefore hafter /\
    Class?.contains c hbefore o
  ))
  (ensures (Class?.contains c hafter o))
  [SMTPatT (Class?.preserved c o hbefore hafter); SMTPatT (Class?.contains c hbefore o)]
= Squash.bind_squash #_ #(Class?.contains c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.preserved_contains hbefore hafter o)

let live_contains
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (h: heap)
  (o: ty)
: Lemma
  (requires (Class?.live c h o))
  (ensures (Class?.contains c h o))
  [SMTPatT (Class?.live c h o)]
= Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.live_contains h o)

let ancestors_contains
  (#level: nat) (#ty: Type) (c: class level ty {class_invariant c})
  (h: heap)
  (o: ty)
  (s: squash (Class?.ancestor_count c o > 0))
: Lemma
  (requires (forall 
    (i: nat {i < Class?.ancestor_count c o } )
    .
    (Class?.contains (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i))
  ))
  (ensures (Class?.contains c h o))
=  Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.ancestors_contains h o s (fun _ -> ()))

let live_ancestors
  (#level: nat) (#ty: Type) (c: class level ty { class_invariant c } )
  (h: heap)
  (o: ty)
  (i: nat {i < Class?.ancestor_count c o } )
: Lemma
  (requires (Class?.live c h o))
  (ensures (
    Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)
  ))
  [SMTPat (Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i))]
= Squash.bind_squash #_ #(Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)) (Squash.join_squash ()) (fun (j: class_invariant_body c) -> j.live_ancestors h o i)

private
noeq type disjoint_t: (#level1: nat) -> (#level2: nat) -> (#t1: Type) -> (#t2: Type) -> class level1 t1 -> class level2 t2 -> t1 -> t2 -> Tot Type =
| DisjointObjects:
  (#level: nat) ->
  (#t: Type) ->
  (c: class level t) ->
  (o1: t) ->
  (o2: t) ->
  squash (Class?.disjoint c o1 o2) ->
  disjoint_t c c o1 o2
| DisjointAncestors:
  (#level: (bool -> Tot nat)) ->
  (#t: (bool -> Tot Type)) ->
  (c: ((b: bool) -> Tot (class (level b) (t b)))) ->
  (o: ((b: bool) -> Tot (t b))) ->
  (h: ((i: nat { i < Class?.ancestor_count (c true) (o true) } ) -> Tot (disjoint_t (Class?.ancestor_classes (c true) (o true) i) (c false) (Class?.ancestor_objects (c true) (o true) i) (o false)))) ->
  (b: bool) ->
  disjoint_t (c b) (c (not b)) (o b) (o (not b))  

abstract
let disjoint
 (#level1: nat)
 (#level2: nat)
 (#t1: Type)
 (#t2: Type)
 (c1: class level1 t1)
 (c2: class level2 t2)
 (o1: t1)
 (o2: t2)
: Tot Type0
= squash (disjoint_t c1 c2 o1 o2)

private
let rec disjoint_t_sym
  (#level1: nat)
  (#level2: nat)
  (#t1: Type)
  (#t2: Type)
  (c1: class level1 t1 { class_invariant c1 } )
  (c2: class level2 t2 { class_invariant c2 } )
  (o1: t1)
  (o2: t2)
  (d: disjoint_t c1 c2 o1 o2)
: Pure (disjoint_t c2 c1 o2 o1)
  (requires True)
  (ensures (fun _ -> True))
  (decreases d)
= match d with
  | DisjointObjects #level #t c o1 o2 h ->
    DisjointObjects #level #t c o2 o1 (class_disjoint_sym c o1 o2)
  | DisjointAncestors #level #t c o h b ->
    DisjointAncestors #level #t c o h (not b)

abstract
let disjoint_sym
  (#level1: nat)
  (#level2: nat)
  (#t1: Type)
  (#t2: Type)
  (c1: class level1 t1 { class_invariant c1 } )
  (c2: class level2 t2 { class_invariant c2 } )
  (o1: t1)
  (o2: t2)
: Lemma
  (requires (disjoint c1 c2 o1 o2))
  (ensures (disjoint c2 c1 o2 o1))
  [SMTPat (disjoint c2 c1 o2 o1)]
= Squash.bind_squash (Squash.join_squash ()) (fun (d: disjoint_t c1 c2 o1 o2) -> Squash.return_squash (disjoint_t_sym c1 c2 o1 o2 d))

let disjoint_objects
  (#level: nat)
  (#t: Type)
  (c: class level t {class_invariant c})
  (o1: t)
  (o2: t)
: Lemma
  (requires (Class?.disjoint c o1 o2))
  (ensures (disjoint c c o1 o2))
  [SMTPatT (Class?.disjoint c o1 o2)]
= Squash.return_squash (DisjointObjects c o1 o2 ())

let disjoint_ancestors_left
  (#level1: nat)
  (#t1: Type)
  (c1: class level1 t1 { class_invariant c1 })
  (#level2: nat)
  (#t2: Type)
  (c2: class level2 t2 { class_invariant c2 })
  (o1: t1)
  (o2: t2)
  (h: (
    (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
    Lemma (disjoint (Class?.ancestor_classes c1 o1 i) c2 (Class?.ancestor_objects c1 o1 i) o2)
  ))
: Lemma
  (requires (
    Class?.ancestor_count c1 o1 > 0
  ))
  (ensures (disjoint c1 c2 o1 o2))
= let f
    (i: nat { i < Class?.ancestor_count c1 o1 } )
  : Tot (squash (disjoint_t (Class?.ancestor_classes c1 o1 i) c2 (Class?.ancestor_objects c1 o1 i) o2))
  = Squash.join_squash (h i)
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c1 o1 } ) -> Tot (disjoint_t (Class?.ancestor_classes c1 o1 i) c2 (Class?.ancestor_objects c1 o1 i) o2))) ->
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #(fun b -> if b then level1 else level2) #(fun b -> if b then t1 else t2) (fun b -> if b then c1 else c2) (fun b -> if b then o1 else o2) h true in
    Squash.return_squash d
  )

let disjoint_ancestors_right
  (#level1: nat)
  (#t1: Type)
  (c1: class level1 t1 { class_invariant c1 })
  (#level2: nat)
  (#t2: Type)
  (c2: class level2 t2 { class_invariant c2 })
  (o1: t1)
  (o2: t2)
  (h: (
    (i: nat { i < Class?.ancestor_count c2 o2 } ) ->
    Lemma (disjoint c1 (Class?.ancestor_classes c2 o2 i) o1 (Class?.ancestor_objects c2 o2 i))
  ))
: Lemma
  (requires (
    Class?.ancestor_count c2 o2 > 0
  ))
  (ensures (disjoint c1 c2 o1 o2))
= let f
    (i: nat { i < Class?.ancestor_count c2 o2 } )
  : Tot (squash (disjoint_t (Class?.ancestor_classes c2 o2 i) c1 (Class?.ancestor_objects c2 o2 i) o1))
  = let _ : squash (disjoint_t c1 (Class?.ancestor_classes c2 o2 i) o1 (Class?.ancestor_objects c2 o2 i)) = Squash.join_squash (h i) in
    Squash.join_squash (disjoint_sym c1 (Class?.ancestor_classes c2 o2 i) o1 (Class?.ancestor_objects c2 o2 i))
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c2 o2 } ) -> Tot (disjoint_t (Class?.ancestor_classes c2 o2 i) c1 (Class?.ancestor_objects c2 o2 i) o1))) ->
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #(fun b -> if b then level2 else level1) #(fun b -> if b then t2 else t1) (fun b -> if b then c2 else c1) (fun b -> if b then o2 else o1) h false in
    Squash.return_squash d
  )

noeq type object: Type =
| Object:
  (ty: Type) ->
  (level: nat) ->
  (class: class level ty { class_invariant class } ) ->
  (obj: ty) ->
  object

let modifies
  (s: TSet.set object )
  (h h': heap)
: Tot Type0
= forall (o: object) .
    (forall (o': object { TSet.mem o' s }) . disjoint (Object?.class o) (Object?.class o') (Object?.obj o) (Object?.obj o' )) ==>
    Class?.preserved (Object?.class o) (Object?.obj o) h h'

let modifies_refl
  (s: TSet.set object )
  (h: heap)
: Lemma
  (requires True)
  (ensures (modifies s h h))
  [SMTPat (modifies s h h)]
= ()

let modifies_trans
  (s: TSet.set object )
  (h1 h2 h3: heap)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
  [SMTPatT (modifies s h1 h2); SMTPatT (modifies s h2 h3)]
= ()

let modifies_subset
  (s1 s2: TSet.set object)
  (h h': heap)
: Lemma
  (requires (modifies s1 h h' /\ TSet.subset s1 s2))
  (ensures (modifies s2 h h'))
  [SMTPatT (modifies s1 h h'); SMTPatT (TSet.subset s1 s2)]
= ()

(*
let rec fresh_disjoint
  (#levelold: nat) (#tyold: Type)
  (#levelnew: nat) (#tynew: Type)
  (cold: class levelold tyold {class_invariant cold})
  (cnew: class levelnew tynew {class_invariant cnew})
  (oold: tyold)
  (onew: tynew)
  (hbefore: heap)
  (hafter: heap)
: Lemma
  (requires (
    Class?.live cold hbefore oold /\
    (~ (Class?.contains cnew hbefore onew)) /\
    Class?.live cold hafter oold /\
    Class?.live cnew hafter onew
  ))
  (ensures (disjoint cold cnew oold onew))
  (decreases (levelold + levelnew))
  [SMTPatT (Class?.live cold hbefore oold); SMTPatT (~ (Class?.contains cnew hbefore onew)); SMTPatT (Class?.live cold hafter oold); SMTPatT (Class?.live cnew hafter onew)]
= Classical.or_elim
    


= Squash.bind_squash #_ #(Class?.disjoint c oold onew) (Squash.join_squash ()) (fun (i: class_invariant_body c) -> i.class_fresh_disjoint oold onew hbefore hafter)


(*

let ancestors_closed
  (s: TSet.set object)
= forall (o: object { TSet.mem o s } ) (i: nat {i < Class?.ancestor_count (Object?.class o) (Object?.obj o)}) .
  TSet.mem (Object
    (Class?.ancestor_types (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_class_levels (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_classes (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_objects (Object?.class o) (Object?.obj o) i)
  ) s

let ancestors_closed_empty
: squash (ancestors_closed TSet.empty)
= ()

let ancestors_closed_union
  (s1 s2: (s: TSet.set object {ancestors_closed s} ))
: Lemma
  (requires True)
  (ensures (ancestors_closed (TSet.union s1 s2)))
  [SMTPat (ancestors_closed (TSet.union s1 s2))]
= ()

let leibniz (#t: Type) (f: (t -> Tot Type)) (a1 a2: t) (s: squash (a1 == a2)) (u: squash (f a1)) : Lemma
  (ensures (f a2))
= ()

let ancestors_closed_big_union
  (#index: Type)
  (f: (index -> Tot (s: TSet.set object {ancestors_closed s} )))
: Lemma
  (requires True)
  (ensures (ancestors_closed (TSet.big_union f)))
  [SMTPat (ancestors_closed (TSet.big_union f))]
= Classical.forall_intro' #_ #(fun (o: object {TSet.mem o (TSet.big_union f)}) -> 
forall (i: nat {i < Class?.ancestor_count (Object?.class o) (Object?.obj o)}) .
      TSet.mem (Object
	(Class?.ancestor_types (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_class_levels (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_classes (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_objects (Object?.class o) (Object?.obj o) i)
    ) (TSet.big_union f)
    )
    (fun (o: object { TSet.mem o (TSet.big_union f) } ) ->
    let a: squash ( TSet.mem o (TSet.big_union f) ) = () in    
    let x: squash  ( exists (j: index) . TSet.mem o (f j) ) = leibniz #Type0 (fun u -> u) (TSet.mem o (TSet.big_union f)) (exists (j: index) . TSet.mem o (f j)) (TSet.mem_big_union f o) a in
    Classical.exists_elim (forall (i: nat {i < Class?.ancestor_count (Object?.class o) (Object?.obj o)}) .
      TSet.mem (Object
	(Class?.ancestor_types (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_class_levels (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_classes (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_objects (Object?.class o) (Object?.obj o) i)
    ) (TSet.big_union f) )
    x
    (fun (j: index { TSet.mem o (f j) } ) ->
       let x : squash (forall (i: nat {i < Class?.ancestor_count (Object?.class o) (Object?.obj o)}) .
      TSet.mem (Object
	(Class?.ancestor_types (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_class_levels (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_classes (Object?.class o) (Object?.obj o) i)
	(Class?.ancestor_objects (Object?.class o) (Object?.obj o) i)
    ) (f j) ) = () in
      ()
  ))

let ancestors_add_element
  (o: object)
  (s: TSet.set object { ancestors_closed s } )
: Lemma
  (requires (forall (i: nat {i < Class?.ancestor_count (Object?.class o) (Object?.obj o)}) .
  TSet.mem (Object
    (Class?.ancestor_types (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_class_levels (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_classes (Object?.class o) (Object?.obj o) i)
    (Class?.ancestor_objects (Object?.class o) (Object?.obj o) i)
  ) s))
  (ensures (ancestors_closed (TSet.union (TSet.singleton o) s)))
  [SMTPat (TSet.union (TSet.singleton o) s)]
= ()

let rec ancestors_closed_from_one
  (#ty: Type)
  (#level: nat)
  (cl: class level ty { class_invariant cl } )
  (obj: ty)
: Tot (s: TSet.set object { ancestors_closed s /\ TSet.mem (Object ty level cl obj) s } )
= let a = TSet.big_union (fun (i: nat {i < Class?.ancestor_count cl obj}) -> ancestors_closed_from_one (Class?.ancestor_classes cl obj i) (Class?.ancestor_objects cl obj i)) in
  let x = TSet.union (TSet.singleton (Object ty level cl obj)) a in
  let _ : squash (
  forall (i: nat {i < Class?.ancestor_count cl obj}) .
  TSet.mem (Object
    (Class?.ancestor_types cl obj i)
    (Class?.ancestor_class_levels cl obj i)
    (Class?.ancestor_classes cl obj i)
    (Class?.ancestor_objects cl obj i)
  ) a) =
    Classical.forall_intro' #_ #(fun (i: nat {i < Class?.ancestor_count cl obj}) ->
  TSet.mem (Object
    (Class?.ancestor_types cl obj i)
    (Class?.ancestor_class_levels cl obj i)
    (Class?.ancestor_classes cl obj i)
    (Class?.ancestor_objects cl obj i)
  ) a) (fun i ->
    Classical.exists_intro (fun i' ->
    TSet.mem (Object
      (Class?.ancestor_types cl obj i)
      (Class?.ancestor_class_levels cl obj i)
      (Class?.ancestor_classes cl obj i)
      (Class?.ancestor_objects cl obj i)
      ) (ancestors_closed_from_one (Class?.ancestor_classes cl obj i') (Class?.ancestor_objects cl obj i'))) i )
  in
  let _ = ancestors_add_element (Object ty level cl obj) a in
  x
 

let disjoint_ancestors_left
  (o1: object)
  (o2: object)
: Lemma
  (requires (Cons? (ancestors o1) /\ (forall (x: object {List.Tot.memP x (ancestors o1) }) . disjoint x o2)))
  (ensures (disjoint o1 o2))
= let f (x: object { List.Tot.memP x (ancestors o1) }) : Tot (squash (disjoint_t x o2)) = Squash.join_squash () in
  let g = SquashProperties.squash_arrow f in

let disjoint_ancestors_right
  (o1: object)
  (o2: object)
: Lemma
  (requires (Cons? (ancestors o2) /\ (forall (x: object {List.Tot.memP x (ancestors o2) }) . disjoint o1 x)))
  (ensures (disjoint o1 o2))
= let f (x: object { List.Tot.memP x (ancestors o2) }) : Tot (squash (disjoint_t o1 x)) = Squash.join_squash () in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun h ->
    Squash.return_squash (DisjointAncestorsRight o1 o2 h)
  )

(*
let disjoint_ind
  (x:
    (o1: object) ->
    (o2: object) ->
    Pure Type0
    (requires (disjoint o1 o2))
    (ensures (fun _ -> True)))
  (h_classes:
    (o1: object) ->
    (o2: object) ->
    Lemma
    (requires (disjoint o1 o2 /\ (~ (Object?.cl o1 == Object?.cl o2))))
    (ensures (disjoint o1 o2 /\ x o1 o2)))
  (h_objects:
    (o1: object) ->
    (o2: object) ->
    Lemma
    (requires (disjoint o1 o2 /\ ))
: Tot Type0
= True
    


(*
{
      (forall h h' .
	(Cons? (ancestors h) /\ (forall x . List.Tot.memP x (ancestors h) ==> Class?.preserved (Object?.cl x) (Object?.obj x) h h')) ==>
	Class?.preserved (Object?.cl x) obj)
  }
*)
