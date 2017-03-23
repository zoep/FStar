module FStar.Modifies

noeq type class' (heap: Type) : (level: nat) -> (carrier: Type) -> Tot Type =
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
  (ancestor_classes: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (class' heap (ancestor_class_levels x i) (ancestor_types x i)))) ->
  (ancestor_objects: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (ancestor_types x i))) ->
  class' heap level carrier

unfold
let preserved_refl_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty) 
  : Tot Type
= (x: ty) ->
  (h : heap) ->
  Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))

unfold
let preserved_trans_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty) 
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
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty) 
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
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty) 
  : Tot Type
= (x1: ty) ->
  (x2: ty) ->
  Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))

unfold
let level_0_class_eq_root_t
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class' heap level ty) 
  : Tot Type
= squash (level == 0 ==> ty == root_type /\ c == root_class)

unfold
let level_0_fresh_disjoint_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
: Tot Type
= (oold: ty) ->
  (onew: ty) ->
  (hbefore: heap) ->
  (hafter: heap) ->
  Lemma
  (requires (
    level == 0 /\
    Class?.live c hbefore oold /\
    (~ (Class?.contains c hbefore onew)) /\
    Class?.live c hafter oold /\
    Class?.live c hafter onew
  ))
  (ensures (Class?.disjoint c oold onew))
  
unfold
let preserved_live_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
: Tot Type
= (hbefore: heap) ->
  (hafter: heap) ->
  (o: ty) ->
  Lemma
  (requires (
    Class?.preserved c o hbefore hafter    
  ))
  (ensures (Class?.live c hbefore o ==> Class?.live c hafter o))

unfold
let preserved_contains_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
: Tot Type
= (hbefore: heap) ->
  (hafter: heap) ->
  (o: ty) ->
  Lemma
  (requires (
    Class?.preserved c o hbefore hafter    
  ))
  (ensures (Class?.contains c hbefore o ==> Class?.contains c hafter o))

unfold
let live_contains_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
: Tot Type
= (h: heap) ->
  (o: ty) ->
  Lemma
  (requires (Class?.live c h o))
  (ensures (Class?.contains c h o))

unfold
let ancestors_contains_t
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
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
  (#heap: Type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
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
type class_invariant_body
  (#heap: Type)
  (#root_type: Type)
  (root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type)
  (c: class' heap level ty)
= {
  preserved_refl: preserved_refl_t c;
  preserved_trans: preserved_trans_t c;
  preserved_ancestors_preserved: preserved_ancestors_preserved_t c;
  class_disjoint_sym: class_disjoint_sym_t c;
  level_0_class_eq_root: level_0_class_eq_root_t root_class c;
  level_0_fresh_disjoint: level_0_fresh_disjoint_t c;
  preserved_live: preserved_live_t c;
  preserved_contains: preserved_contains_t c;
  live_contains: live_contains_t c;
  ancestors_contains: ancestors_contains_t c;
  live_ancestors: live_ancestors_t c
}

abstract
let rec class_invariant
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases level)
= (squash (class_invariant_body root_class c) /\ (forall
    (x: ty)
    (i: nat {i < Class?.ancestor_count c x})
    . (class_invariant root_class (Class?.ancestor_classes c x i))
  ))

let class_invariant_intro
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class' heap level ty)
  (b: class_invariant_body root_class c)
: Lemma
  (requires (forall
    (x: ty)
    (i: nat {i < Class?.ancestor_count c x})
    . (class_invariant root_class (Class?.ancestor_classes c x i))
  ))
  (ensures (class_invariant root_class c))
= Squash.return_squash b

type class
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type)
  (level: nat)
  (ty: Type)
= (c: class' heap level ty { class_invariant root_class c } )

let class_invariant_ancestor_classes
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type)
  (c: class root_class level ty)
  (x: ty)
  (i: nat {i < Class?.ancestor_count c x})
: Lemma
  (requires True)
  (ensures (class_invariant root_class (Class?.ancestor_classes c x i)))
  [SMTPat (class_invariant root_class (Class?.ancestor_classes c x i))]
= ()

(** FIXME: statements are duplicated here due to the SMT patterns *)

let preserved_refl
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
  (x: ty)
  (h : heap)
: Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))
  [SMTPat (Class?.preserved c x h h)]
= Squash.bind_squash #_ #(Class?.preserved c x h h) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_refl x h)

let preserved_trans
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
  (x: ty)
  (h1: heap)
  (h2: heap)
  (h3: heap)
: Lemma
  (requires (Class?.preserved c x h1 h2 /\ Class?.preserved c x h2 h3))
  (ensures (Class?.preserved c x h1 h3))
  [SMTPatT (Class?.preserved c x h1 h2); SMTPatT (Class?.preserved c x h2 h3)]
= Squash.bind_squash #_ #(Class?.preserved c x h1 h3) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_trans x h1 h2 h3)

let preserved_ancestors_preserved
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty) 
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
= Squash.bind_squash #_ #(Class?.preserved c x h h') (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_ancestors_preserved x h h' () (fun _ -> ()))

let class_disjoint_sym
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty) 
  (x1: ty)
  (x2: ty)
: Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))
  [SMTPat (Class?.disjoint c x2 x1)]
= Squash.bind_squash #_ #(Class?.disjoint c x2 x1) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.class_disjoint_sym x1 x2)

let level_0_class_eq_root
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#ty: Type) (c: class root_class 0 ty)
: Lemma
  (ensures (ty == root_type /\ c == root_class))
= Squash.bind_squash #_ #(0 == 0 ==> ty == root_type /\ c == root_class) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.level_0_class_eq_root)

let level_0_fresh_disjoint
  (#heap: Type)
  (#root_type: Type) (root_class: class' heap 0 root_type { class_invariant root_class root_class } )
  (oold: root_type)
  (onew: root_type)
  (hbefore: heap)
  (hafter: heap)
: Lemma
  (requires (
    Class?.live root_class hbefore oold /\
    (~ (Class?.contains root_class hbefore onew)) /\
    Class?.live root_class hafter oold /\
    Class?.live root_class hafter onew
  ))
  (ensures (Class?.disjoint root_class oold onew))
  [SMTPatT (Class?.live root_class hbefore oold); SMTPatT (~ (Class?.contains root_class hbefore onew)); SMTPatT (Class?.live root_class hafter oold); SMTPatT (Class?.live root_class hafter onew)]
= Squash.bind_squash #_ #(Class?.disjoint root_class oold onew) (Squash.join_squash ()) (fun (i: class_invariant_body root_class root_class) -> i.level_0_fresh_disjoint oold onew hbefore hafter)

let preserved_live
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
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
= Squash.bind_squash #_ #(Class?.live c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_live hbefore hafter o)

let preserved_contains
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
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
= Squash.bind_squash #_ #(Class?.contains c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_contains hbefore hafter o)

let live_contains
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
  (h: heap)
  (o: ty)
: Lemma
  (requires (Class?.live c h o))
  (ensures (Class?.contains c h o))
  [SMTPatT (Class?.live c h o)]
= Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.live_contains h o)

let ancestors_contains
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty)
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
=  Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.ancestors_contains h o s (fun _ -> ()))

let live_ancestors
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty )
  (h: heap)
  (o: ty)
  (i: nat {i < Class?.ancestor_count c o } )
: Lemma
  (requires (Class?.live c h o))
  (ensures (
    Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)
  ))
  [SMTPat (Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i))]
= Squash.bind_squash #_ #(Class?.live (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.live_ancestors h o i)

private
noeq type disjoint_t  (#heap: Type) : (#level1: nat) -> (#level2: nat) -> (#t1: Type) -> (#t2: Type) -> class' heap level1 t1 -> class' heap level2 t2 -> t1 -> t2 -> Tot Type =
| DisjointObjects:
  (#level: nat) ->
  (#t: Type) ->
  (c: class' heap level t) ->
  (o1: t) ->
  (o2: t) ->
  squash (Class?.disjoint c o1 o2) ->
  disjoint_t c c o1 o2
| DisjointAncestors:
  (#level: (bool -> Tot nat)) ->
  (#t: (bool -> Tot Type)) ->
  (c: ((b: bool) -> Tot (class' heap (level b) (t b)))) ->
  (o: ((b: bool) -> Tot (t b))) ->
  (h: ((i: nat { i < Class?.ancestor_count (c true) (o true) } ) -> Tot (disjoint_t (Class?.ancestor_classes (c true) (o true) i) (c false) (Class?.ancestor_objects (c true) (o true) i) (o false)))) ->
  (b: bool) ->
  disjoint_t (c b) (c (not b)) (o b) (o (not b))  

abstract
let disjoint
 (#heap: Type)
 (#level1: nat)
 (#level2: nat)
 (#t1: Type)
 (#t2: Type)
 (c1: class' heap level1 t1)
 (c2: class' heap level2 t2)
 (o1: t1)
 (o2: t2)
: Tot Type0
= squash (disjoint_t c1 c2 o1 o2)

private
let rec disjoint_t_sym
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level1: nat)
  (#level2: nat)
  (#t1: Type)
  (#t2: Type)
  (c1: class root_class level1 t1 )
  (c2: class root_class level2 t2 )
  (o1: t1)
  (o2: t2)
  (d: disjoint_t c1 c2 o1 o2)
: Pure (disjoint_t c2 c1 o2 o1)
  (requires True)
  (ensures (fun _ -> True))
  (decreases d)
= match d with
  | DisjointObjects #heap #level #t c o1 o2 h ->
    let (c: class root_class level t) = c in
    DisjointObjects #heap #level #t c o2 o1 (class_disjoint_sym c o1 o2)
  | DisjointAncestors #heap #level #t c o h b ->
    DisjointAncestors #heap #level #t c o h (not b)

abstract
let disjoint_sym
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level1: nat)
  (#level2: nat)
  (#t1: Type)
  (#t2: Type)
  (c1: class root_class level1 t1 )
  (c2: class root_class level2 t2 )
  (o1: t1)
  (o2: t2)
: Lemma
  (requires (disjoint c1 c2 o1 o2))
  (ensures (disjoint c2 c1 o2 o1))
  [SMTPat (disjoint c2 c1 o2 o1)]
= Squash.bind_squash (Squash.join_squash ()) (fun (d: disjoint_t c1 c2 o1 o2) -> Squash.return_squash (disjoint_t_sym c1 c2 o1 o2 d))

let disjoint_objects
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#t: Type)
  (c: class root_class level t)
  (o1: t)
  (o2: t)
: Lemma
  (requires (Class?.disjoint c o1 o2))
  (ensures (disjoint c c o1 o2))
  [SMTPatT (Class?.disjoint c o1 o2)]
= Squash.return_squash (DisjointObjects c o1 o2 ())

let disjoint_ancestors_left
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level1: nat)
  (#t1: Type)
  (c1: class root_class level1 t1)
  (#level2: nat)
  (#t2: Type)
  (c2: class root_class level2 t2)
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
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #heap #(fun b -> if b then level1 else level2) #(fun b -> if b then t1 else t2) (fun b -> if b then c1 else c2) (fun b -> if b then o1 else o2) h true in
    Squash.return_squash d
  )

let disjoint_ancestors_right
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level1: nat)
  (#t1: Type)
  (c1: class root_class level1 t1)
  (#level2: nat)
  (#t2: Type)
  (c2: class root_class level2 t2)
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
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #heap #(fun b -> if b then level2 else level1) #(fun b -> if b then t2 else t1) (fun b -> if b then c2 else c1) (fun b -> if b then o2 else o1) h false in
    Squash.return_squash d
  )

noeq type object (#heap: Type) (#root_type: Type) (root_class: class' heap 0 root_type) : Type =
| Object:
  (ty: Type) ->
  (level: nat) ->
  (class: class root_class level ty) ->
  (obj: ty) ->
  object root_class

let modifies
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (s: TSet.set (object root_class))
  (h h': heap)
: Tot Type0
= forall (ty: Type) (l: nat) (c: class root_class l ty) (o: ty) .
    (forall (o': object root_class { TSet.mem o' s }) . disjoint c (Object?.class o') o (Object?.obj o' )) ==>
    Class?.preserved c o h h'

let modifies_refl
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (s: TSet.set (object root_class))
  (h: heap)
: Lemma
  (requires True)
  (ensures (modifies s h h))
  [SMTPat (modifies s h h)]
= ()

let modifies_trans
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (s: TSet.set (object root_class) )
  (h1 h2 h3: heap)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
  [SMTPatT (modifies s h1 h2); SMTPatT (modifies s h2 h3)]
= ()

let modifies_subset
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (s1 s2: TSet.set (object root_class))
  (h h': heap)
: Lemma
  (requires (modifies s1 h h' /\ TSet.subset s1 s2))
  (ensures (modifies s2 h h'))
  [SMTPatT (modifies s1 h h'); SMTPatT (TSet.subset s1 s2)]
= ()

let singleton
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#ty: Type)
  (#level: nat)
  (class: class root_class level ty)
  (obj: ty)
: TSet.set (object root_class)
= TSet.singleton (Object ty level class obj)

private
let modifies_test_1
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#ty: Type)
  (#level: nat)
  (c: class root_class level ty)
  (#ty2: Type)
  (#level2: nat)
  (c2: class root_class level2 ty2)
  (o1 o3: ty)
  (o2: ty2)
  (h h': heap)
: Lemma
  (requires (Class?.disjoint c o1 o3 /\ disjoint c c2 o3 o2 /\ modifies (TSet.union (singleton c o1) (singleton c2 o2)) h h'))
  (ensures (Class?.preserved c o3 h h'))
= ()

let rec fresh
  (#heap: Type)
  (#level: nat)
  (#ty: Type)
  (c: class' heap level ty)
  (o: ty)
  (h h': heap)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases level)
= (~ ( Class?.contains c h o )) /\
  Class?.live c h' o /\ (
    forall (i: nat {i < Class?.ancestor_count c o}) . fresh (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i) h h'
  )

let fresh_ancestor
  (#heap: Type)
  (#level: nat)
  (#ty: Type)
  (c: class' heap level ty)
  (o: ty)
  (h h': heap)
  (i: nat {i < Class?.ancestor_count c o})
: Lemma
  (requires (fresh c o h h'))
  (ensures (fresh (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i) h h'))
  [SMTPat (fresh (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i) h h')]
= ()

abstract
let rec fresh_live
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type)
  (c: class root_class level ty)
  (o: ty)
  (h0 h1 h2: heap)
: Lemma
  (requires (fresh c o h0 h1 /\ Class?.live c h2 o))
  (ensures (fresh c o h0 h2))
  [SMTPatT (fresh c o h0 h1); SMTPatT (Class?.live c h2 o)]
= let f
    (i: nat {i < Class?.ancestor_count c o})
  : Lemma
    (ensures (
      fresh (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i) h0 h2
    ))
  = let (c': class root_class (Class?.ancestor_class_levels c o i) (Class?.ancestor_types c o i)) = (Class?.ancestor_classes c o i) in
    fresh_live c' (Class?.ancestor_objects c o i) h0 h1 h2
  in
  Classical.forall_intro f

abstract
let rec fresh_disjoint
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#levelold: nat) (#tyold: Type)
  (#levelnew: nat) (#tynew: Type)
  (cold: class root_class levelold tyold)
  (cnew: class root_class levelnew tynew)
  (oold: tyold)
  (onew: tynew)
  (hbefore: heap)
  (hafter: heap)
: Lemma
  (requires (
    Class?.live cold hbefore oold /\
    Class?.live cold hafter oold /\
    fresh cnew onew hbefore hafter
  ))
  (ensures (disjoint cold cnew oold onew))
  (decreases (levelold + levelnew))
  [SMTPatT (Class?.live cold hbefore oold); SMTPatT (Class?.live cold hafter oold); SMTPatT (fresh cnew onew hbefore hafter)]
= if
    levelold = 0
  then
    let _ : squash (tyold == root_type /\ cold == root_class) = level_0_class_eq_root #heap #root_type #root_class #tyold cold in
    if
      levelnew = 0
    then
      let _ : squash (tynew == root_type /\ cnew == root_class) = level_0_class_eq_root #heap #root_type #root_class #tynew cnew in
      level_0_fresh_disjoint cold oold onew hbefore hafter
    else
      let f
	(i: nat { i < Class?.ancestor_count cnew onew } )
      : Lemma
	(disjoint cold (Class?.ancestor_classes cnew onew i) oold (Class?.ancestor_objects cnew onew i))
      = let cnew' = Class?.ancestor_classes cnew onew i in
	let onew' = Class?.ancestor_objects cnew onew i in
	fresh_disjoint cold cnew' oold onew' hbefore hafter
      in
      disjoint_ancestors_right cold cnew oold onew f
  else
    let f
      (i: nat { i < Class?.ancestor_count cold oold } )
    : Lemma
      (disjoint (Class?.ancestor_classes cold oold i) cnew (Class?.ancestor_objects cold oold i) onew)
    = let cold' = Class?.ancestor_classes cold oold i in
      let oold' = Class?.ancestor_objects cold oold i in
      fresh_disjoint cold' cnew oold' onew hbefore hafter
    in
    disjoint_ancestors_left cold cnew oold onew f
