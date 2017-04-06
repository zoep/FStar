module FStar.Modifies

noeq type class' : (heap: (Type u#a)) -> (level: nat) -> (carrier: (Type u#b)) -> (Type u#(1 + max a b)) =
| Class:
  (heap: (Type u#a)) ->
  (level: nat) ->
  (carrier: (Type u#b)) ->
  (disjoint: (carrier -> carrier -> Tot Type0)) ->
  (live: (heap -> carrier -> Tot Type0)) ->
  (contains: (heap -> carrier -> Tot Type0)) ->
  (preserved: (carrier -> heap -> heap -> Tot Type0)) ->
  (includes: (carrier -> carrier -> Tot Type0)) ->
  (ancestor_count: (carrier -> Tot (x: nat { level > 0 ==> x > 0 } ))) ->
  (ancestor_types: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (Type u#b))) ->
  (ancestor_class_levels: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (y:nat { y < level } ))) ->
  (ancestor_classes: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (class' heap (ancestor_class_levels x i) (ancestor_types x i)))) ->
  (ancestor_objects: ((x: carrier) -> (i: nat {i < ancestor_count x}) -> Tot (ancestor_types x i))) ->
  class' heap level carrier

let hetero_id
  (#a: Type)
  (#b: Type)
  (x: a)
: Pure b
  (requires (a == b))
  (ensures (fun y -> a == b /\ y == x))
= x

(*


let carrier_eq
  (#heap: (Type 'ua))
  (#level: nat)
  (#carrier: (Type 'ub))
  (c: class'  heap level carrier)
: Lemma
  (requires True)
  (ensures (Class?.carrier c == carrier))
  [SMTPat (Class?.carrier c)]
= ()

let carrier_ancestor_classes
  (#heap: (Type 'ua))
  (#level: nat)
  (#carrier: (Type 'ub))
  (c: class'  heap level carrier)
  (x: carrier)
  (i: nat {i < Class?.ancestor_count c x})
: Lemma
  (requires True)
  (ensures (Class?.carrier (Class?.ancestor_classes c x i) == Class?.ancestor_types c x i))
  [SMTPat (Class?.carrier (Class?.ancestor_classes c x i))]
= ()
*)

unfold
let ancestor_objects
  (#heap: (Type u#a))
  (#level: nat)
  (#carrier: (Type u#b))
  (c: class'  heap level carrier)
  (x: carrier)
  (i: nat {i < Class?.ancestor_count c x})
: Tot (Class?.carrier (Class?.ancestor_classes c x i))
= hetero_id (Class?.ancestor_objects c x i)

unfold
let preserved_refl_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty) 
  : Tot (Type u#(max a b))
= (x: ty) ->
  (h : heap) ->
  Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))

unfold
let preserved_trans_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty) 
  : Tot (Type u#(max a b))
= (x: ty) ->
  (h1: heap) ->
  (h2: heap) ->
  (h3 : heap) ->
  Lemma
  (requires (Class?.preserved c x h1 h2 /\ Class?.preserved c x h2 h3))
  (ensures (Class?.preserved c x h1 h3))

unfold
let preserved_ancestors_preserved_t
  (#heap: (Type u#a))
  (#level: nat) (#ty: (Type u#b)) (c: class' heap level ty) 
  : Tot (Type u#(max a b))
= (x: ty) ->
  (h: heap) ->
  (h' : heap) ->
  (s: squash (Class?.ancestor_count c x > 0)) ->
  (f: (
    (i: nat { i < Class?.ancestor_count c x } ) ->
    Lemma
    (Class?.preserved (Class?.ancestor_classes c x i) (ancestor_objects c x i) h h')
  )) ->
  Lemma
  (ensures (Class?.preserved c x h h'))

unfold
let disjoint_sym_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty) 
  : Tot (Type u#b)
= (x1: ty) ->
  (x2: ty) ->
  Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))

unfold
let level_0_class_eq_root_t
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty) 
  : Tot Type0
= squash (level == 0 ==> ty == root_type /\ c == root_class)

unfold
let level_0_fresh_disjoint_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
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
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
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
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
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
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (h: heap) ->
  (o: ty) ->
  Lemma
  (requires (Class?.live c h o))
  (ensures (Class?.contains c h o))

unfold
let ancestors_contains_t
  (#heap: Type u#a)
  (#level: nat) (#ty: (Type u#b)) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (h: heap) ->
  (o: ty) ->
  (s: squash (Class?.ancestor_count c o > 0)) ->
  (f: (
    (i: nat {i < Class?.ancestor_count c o } ) ->
    Lemma
    (Class?.contains (Class?.ancestor_classes c o i) h (ancestor_objects c o i))
  )) ->
  Lemma
  (ensures (Class?.contains c h o))

unfold
let live_ancestors_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (h: heap) ->
  (o: ty) ->
  (i: nat {i < Class?.ancestor_count c o } ) ->
  Lemma
  (requires (Class?.live c h o))
  (ensures (
    Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i)
  ))

unfold
let includes_refl_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#b)
= (o: ty) ->
  Lemma
  (ensures (Class?.includes c o o))

unfold
let includes_trans_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#b)
= (o1: ty) ->
  (o2: ty) ->
  (o3: ty) ->
  Lemma
  (requires (Class?.includes c o1 o2 /\ Class?.includes c o2 o3))
  (ensures (Class?.includes c o1 o3))

unfold
let preserved_includes_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (o1: ty) ->
  (o2: ty) ->
  (hbefore: heap) ->
  (hafter: heap) ->
  Lemma
  (requires (Class?.preserved c o1 hbefore hafter /\ Class?.includes c o1 o2))
  (ensures (Class?.preserved c o2 hbefore hafter))

unfold
let includes_contains_t
  (#heap: Type u#a)
  (#level: nat) (#ty: (Type u#b)) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (h: heap) ->
  (o1: ty) ->
  (o2: ty) ->
  Lemma
  (requires (Class?.contains c h o1 /\ Class?.includes c o1 o2))
  (ensures (Class?.contains c h o2))

unfold
let contains_live_t
  (#heap: Type u#a)
  (#level: nat) (#ty: (Type u#b)) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (h: heap) ->
  (o1: ty) ->
  (o2: ty) ->
  Lemma
  (requires (Class?.live c h o2 /\ Class?.includes c o1 o2))
  (ensures (Class?.live c h o1))

let includes_ancestors_t_prop
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
  (o1: ty)
  (o2: ty {Class?.includes c o1 o2 } )
  (i2: nat {i2 < Class?.ancestor_count c o2 } )
  (i1 : nat {i1 < Class?.ancestor_count c o1} )
: Tot Type0
=   Class?.ancestor_types c o1 i1 == Class?.ancestor_types c o2 i2 /\
    Class?.ancestor_class_levels c o1 i1 == Class?.ancestor_class_levels c o2 i2 /\
    Class?.ancestor_classes c o1 i1 == Class?.ancestor_classes c o2 i2 /\
    Class?.includes (Class?.ancestor_classes c o1 i1) (Class?.ancestor_objects c o1 i1) (Class?.ancestor_objects c o2 i2)

let includes_ancestors_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
: Tot (Type u#b)
= (o1: ty) ->
  (o2: ty {Class?.includes c o1 o2 } ) ->
  (i2: nat {i2 < Class?.ancestor_count c o2 } ) ->
  Tot (squash (i1: (i1 : nat {i1 < Class?.ancestor_count c o1} ) {
    includes_ancestors_t_prop c o1 o2 i2 i1
  } ))

let disjoint_includes_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
: Tot (Type u#b)
= (o1: ty) ->
  (o2: ty) ->
  (o1': ty) ->
  Lemma
  (requires (Class?.disjoint c o1 o2 /\ Class?.includes c o1 o1'))
  (ensures (Class?.disjoint c o1' o2))

noeq
type class_invariant_body
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type u#b)
  (c: class' heap level ty)
: Type u#(max a b)
= {
  preserved_refl: preserved_refl_t c;
  preserved_trans: preserved_trans_t c;
  preserved_ancestors_preserved: preserved_ancestors_preserved_t c;
  disjoint_sym: disjoint_sym_t c;
  level_0_class_eq_root: level_0_class_eq_root_t root_class c;
  level_0_fresh_disjoint: level_0_fresh_disjoint_t c;
  preserved_live: preserved_live_t c;
  preserved_contains: preserved_contains_t c;
  live_contains: live_contains_t c;
  ancestors_contains: ancestors_contains_t u#a u#b c;
  live_ancestors: live_ancestors_t c;
  includes_refl: includes_refl_t c;
  includes_trans: includes_trans_t c;
  preserved_includes: preserved_includes_t c;
  includes_contains: includes_contains_t c;
  contains_live: contains_live_t c;
  includes_ancestors: includes_ancestors_t c;
  disjoint_includes: disjoint_includes_t c
}

abstract
let rec class_invariant
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases level)
= (squash (class_invariant_body root_class c) /\ (forall
    (x: ty)
    (i: nat {i < Class?.ancestor_count c x})
    . (class_invariant root_class (Class?.ancestor_classes c x i))
  ))

abstract
let class_invariant_intro
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (#c: class' heap level ty)
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
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type)
  (level: nat)
  (ty: Type u#b)
= (c: class' heap level ty { class_invariant root_class c } )

let class_invariant_ancestor_classes
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type u#b)
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
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty)
  (x: ty)
  (h : heap)
: Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))
  [SMTPat (Class?.preserved c x h h)]
= Squash.bind_squash #_ #(Class?.preserved c x h h) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_refl x h)

let preserved_trans
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty)
  (x: ty)
  (h1: heap)
  (h2: heap)
  (h3: heap)
: Lemma
  (requires (Class?.preserved c x h1 h2 /\ Class?.preserved c x h2 h3))
  (ensures (Class?.preserved c x h1 h3))
  [SMTPatT u#(max a b) (Class?.preserved c x h1 h2); SMTPatT (Class?.preserved c x h2 h3)]
= Squash.bind_squash #_ #(Class?.preserved c x h1 h3) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_trans x h1 h2 h3)

(* let preserved_ancestors_preserved *)
(*   (#heap: Type u#a) *)
(*   (#root_type: Type u#b) (#root_class: class' heap 0 root_type) *)
(*   (#level: nat) (#ty: Type u#b) (c: class root_class level ty) *)
(*   (x: ty) *)
(*   (h: heap) *)
(*   (h' : heap) *)
(* : Lemma *)
(*   (requires ( *)
(*     Class?.ancestor_count c x > 0 /\ (forall *)
(*     (i: nat { i < Class?.ancestor_count c x } ) . *)
(*     (Class?.preserved (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i) h h') *)
(*   ))) *)
(*   (ensures (Class?.preserved c x h h')) *)
(* = Squash.bind_squash #_ #(Class?.preserved c x h h') (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_ancestors_preserved x h h' () (fun _ -> ())) *)

let preserved_ancestors_preserved
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty)
  (x: ty { Class?.ancestor_count c x > 0 } )
  (h: heap)
  (h' : heap)
  (f: (
    (i: nat { i < Class?.ancestor_count c x } ) ->
    Lemma
    (Class?.preserved (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i) h h')
  ))
: Lemma
  (ensures (Class?.preserved c x h h'))
= Squash.bind_squash #_ #(Class?.preserved c x h h') (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_ancestors_preserved x h h' () f)

let object_disjoint_sym
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty) 
  (x1: ty)
  (x2: ty)
: Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))
  [SMTPat (Class?.disjoint c x2 x1)]
= Squash.bind_squash #_ #(Class?.disjoint c x2 x1) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.disjoint_sym x1 x2)

let level_0_class_eq_root
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#ty: Type u#b) (c: class root_class 0 ty)
: Lemma
  (ensures (ty == root_type /\ c == root_class))
= Squash.bind_squash #_ #(0 == 0 ==> ty == root_type /\ c == root_class) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.level_0_class_eq_root)

let level_0_fresh_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type { class_invariant root_class root_class } )
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
  [SMTPatT u#(max a b) (Class?.live root_class hbefore oold); SMTPatT (~ (Class?.contains root_class hbefore onew)); SMTPatT (Class?.live root_class hafter oold); SMTPatT (Class?.live root_class hafter onew)]
= Squash.bind_squash #_ #(Class?.disjoint root_class oold onew) (Squash.join_squash ()) (fun (i: class_invariant_body root_class root_class) -> i.level_0_fresh_disjoint oold onew hbefore hafter)

(* let preserved_live *)
(*   (#heap: Type) *)
(*   (#root_type: Type) (#root_class: class' heap 0 root_type) *)
(*   (#level: nat) (#ty: Type) (c: class root_class level ty) *)
(*   (hbefore: heap) *)
(*   (hafter: heap) *)
(*   (o: ty) *)
(* : Lemma *)
(*   (requires ( *)
(*     Class?.preserved c o hbefore hafter /\ *)
(*     Class?.live c hbefore o *)
(*   )) *)
(*   (ensures (Class?.live c hafter o)) *)
(*   [SMTPatT (Class?.preserved c o hbefore hafter); SMTPatT (Class?.live c hbefore o)] *)
(* = Squash.bind_squash #_ #(Class?.live c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_live hbefore hafter o) *)

(* let preserved_contains *)
(*   (#heap: Type) *)
(*   (#root_type: Type) (#root_class: class' heap 0 root_type) *)
(*   (#level: nat) (#ty: Type) (c: class root_class level ty) *)
(*   (hbefore: heap) *)
(*   (hafter: heap) *)
(*   (o: ty) *)
(* : Lemma *)
(*   (requires ( *)
(*     Class?.preserved c o hbefore hafter /\ *)
(*     Class?.contains c hbefore o *)
(*   )) *)
(*   (ensures (Class?.contains c hafter o)) *)
(*   [SMTPatT (Class?.preserved c o hbefore hafter); SMTPatT (Class?.contains c hbefore o)] *)
(* = Squash.bind_squash #_ #(Class?.contains c hafter o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_contains hbefore hafter o) *)

(* let live_contains *)
(*   (#heap: Type) *)
(*   (#root_type: Type) (#root_class: class' heap 0 root_type) *)
(*   (#level: nat) (#ty: Type) (c: class root_class level ty) *)
(*   (h: heap) *)
(*   (o: ty) *)
(* : Lemma *)
(*   (requires (Class?.live c h o)) *)
(*   (ensures (Class?.contains c h o)) *)
(*   [SMTPatT (Class?.live c h o)] *)
(* = Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.live_contains h o) *)

(* let ancestors_contains *)
(*   (#heap: Type) *)
(*   (#root_type: Type) (#root_class: class' heap 0 root_type) *)
(*   (#level: nat) (#ty: Type) (c: class root_class level ty) *)
(*   (h: heap) *)
(*   (o: ty) *)
(*   (s: squash (Class?.ancestor_count c o > 0)) *)
(* : Lemma *)
(*   (requires (forall  *)
(*     (i: nat {i < Class?.ancestor_count c o } ) *)
(*     . *)
(*     (Class?.contains (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)) *)
(*   )) *)
(*   (ensures (Class?.contains c h o)) *)
(* =  Squash.bind_squash #_ #(Class?.contains c h o) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.ancestors_contains h o s (fun _ -> ())) *)

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
    Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i)
  ))
  [SMTPat (Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i))]
= Squash.bind_squash #_ #(Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i)) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.live_ancestors h o i)

let object_includes_refl
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty )
  (o: ty)
: Lemma
  (ensures (Class?.includes c o o))
= Squash.bind_squash #_ #(Class?.includes c o o) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.includes_refl o)

let object_includes_trans
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty )
  (o1 o2 o3: ty)
: Lemma
  (requires (Class?.includes c o1 o2 /\ Class?.includes c o2 o3))
  (ensures (Class?.includes c o1 o3))
= Squash.bind_squash #_ #(Class?.includes c o1 o3) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.includes_trans o1 o2 o3)

let object_includes_ancestors
  (#heap: Type u#a)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty )
  (o1: ty)
  (o2: ty {Class?.includes c o1 o2 } )
  (i2: nat {i2 < Class?.ancestor_count c o2 } )
: Tot (squash (i1: (i1 : nat {i1 < Class?.ancestor_count c o1} ) {
    includes_ancestors_t_prop c o1 o2 i2 i1
  } ))
= Squash.bind_squash #_ #(i1: (i1 : nat {i1 < Class?.ancestor_count c o1} ) {
    includes_ancestors_t_prop c o1 o2 i2 i1
  } ) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.includes_ancestors o1 o2 i2)

let object_disjoint_includes
  (#heap: Type u#a)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty )
  (o1: ty)
  (o2: ty)
  (o1': ty)
  (o2': ty)
: Lemma
  (requires (Class?.disjoint c o1 o2 /\ Class?.includes c o1 o1' /\ Class?.includes c o2 o2'))
  (ensures (Class?.disjoint c o1' o2'))
= Squash.bind_squash #_ #(Class?.disjoint c o1' o2') (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) ->
    j.disjoint_includes o1 o2 o1';
    j.disjoint_sym o1' o2;
    j.disjoint_includes o2 o1' o2';
    j.disjoint_sym o2' o1'
  )

private
noeq type disjoint_t: (#heap: Type u#a) -> (#level1: nat) -> (#level2: nat) -> (#t1: (Type u#b)) -> (#t2: (Type u#b)) -> class' heap level1 t1 -> class' heap level2 t2 -> t1 -> t2 -> Tot (Type u#(1 + max a b)) =
| DisjointObjects:
  (#heap: (Type u#a)) ->
  (#level: nat) ->
  (#t: (Type u#b)) ->
  (c: class' heap level t) ->
  (o1: t) ->
  (o2: t) ->
  squash (Class?.disjoint c (hetero_id o1) (hetero_id o2)) ->
  disjoint_t c c o1 o2
| DisjointAncestors:
  (#heap: (Type u#a)) ->
  (#level: (bool -> Tot nat)) ->
  (#t: (bool -> Tot (Type u#b))) ->
  (c: ((b: bool) -> Tot (class' heap (level b) (t b)))) ->
  (o: ((b: bool) -> Tot (t b)) { Class?.ancestor_count (c true) (o true) > 0 } ) ->
  (h: (
    (i: nat { i < Class?.ancestor_count (c true) (hetero_id (o true)) } ) ->
    Tot (disjoint_t (Class?.ancestor_classes (c true) (hetero_id (o true)) i) (c false) (Class?.ancestor_objects (c true) (hetero_id (o true)) i) (o false))
  )) ->
  (b: bool) ->
  disjoint_t (c b) (c (not b)) (o b) (o (not b))  

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
    DisjointObjects #heap #level #t c o2 o1 (object_disjoint_sym c o1 o2)
  | DisjointAncestors #heap #level #t c o h b ->
    DisjointAncestors #heap #level #t c o h (not b)

private
noeq type _location (#heap: Type u#a) (#root_type: Type u#b) (root_class: class' heap 0 root_type) : Type u#(1 + max a b) =
| Location:
  (ty: Type u#b) ->
  (level: nat) ->
  (class: class root_class level ty) ->
  (obj: ty) ->
  _location root_class

abstract let loc (#heap: Type u#a) (#root_type: Type u#b) (root_class: class' heap 0 root_type) : Tot (Type u#(1 + max a b))  = _location #heap #root_type root_class

abstract
let loc_of_object
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#ty: Type u#b)
  (#level: nat)
  (class: class root_class level ty)
  (obj: ty)
: Tot (loc root_class)
= Location ty level class obj

abstract
let loc_of_object_inj
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#ty1: Type u#b)
  (#level1: nat)
  (class1: class root_class level1 ty1)
  (obj1: ty1)
  (#ty2: Type u#b)
  (#level2: nat)
  (class2: class root_class level2 ty2)
  (obj2: ty2)
: Lemma
  (requires (loc_of_object class1 obj1 == loc_of_object class2 obj2))
  (ensures (ty1 == ty2 /\ level1 == level2 /\ class1 == (let class2 : class root_class level1 ty1 = class2 in class2) /\ obj1 == obj2))
= ()

abstract
let loc_of_object_inj_forall
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (root_class: class' heap 0 root_type)
: Lemma (forall
    (ty1: Type u#b)
    (level1: nat)
    (class1: class root_class level1 ty1)
    (obj1: ty1)
    (ty2: Type u#b)
    (level2: nat)
    (class2: class root_class level2 ty2)
    (obj2: ty2)
  .
    (loc_of_object class1 obj1 == loc_of_object class2 obj2) ==>
    (ty1 == ty2 /\ level1 == level2 /\ class1 == (let class2 : class root_class level1 ty1 = class2 in class2) /\ obj1 == obj2)
  )
= ()

abstract
let loc_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
: Tot Type0
= squash (disjoint_t (Location?.class l1) (Location?.class l2) (Location?.obj l1) (Location?.obj l2))

abstract
let loc_disjoint_sym
  (#heap: Type)
  (#root_type: Type)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2))
  (ensures (loc_disjoint l2 l1))
  [SMTPat (loc_disjoint l1 l2)]
= let c1 = Location?.class l1 in
  let c2 = Location?.class l2 in
  let o1 = Location?.obj l1 in
  let o2 = Location?.obj l2 in
  Squash.bind_squash (Squash.join_squash ()) (fun (d: disjoint_t c1 c2 o1 o2) -> Squash.return_squash (disjoint_t_sym c1 c2 o1 o2 d))

let loc_disjoint_objects
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#t: Type u#b)
  (c: class root_class level t)
  (o1: t)
  (o2: t)
: Lemma
  (requires (Class?.disjoint c o1 o2))
  (ensures (loc_disjoint (loc_of_object c o1) (loc_of_object c o2)))
  [SMTPatT u#(1 + max a b) (Class?.disjoint c o1 o2)]
= Squash.return_squash (DisjointObjects c o1 o2 ())

let loc_disjoint_ancestors_left
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level1: nat)
  (#t1: Type u#b)
  (c1: class root_class level1 t1)
  (o1: t1)
  (l2: loc root_class)
  (h: (
    (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
    Lemma (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2)
  ))
: Lemma
  (requires (
    Class?.ancestor_count c1 o1 > 0
  ))
  (ensures (loc_disjoint (loc_of_object c1 o1) l2))
= let c2 = Location?.class l2 in
  let o2 = Location?.obj l2 in
  let level2 = Location?.level l2 in
  let t2 = Location?.ty l2 in
  let f
    (i: nat { i < Class?.ancestor_count c1 o1 } )
  : Tot (squash (disjoint_t (Class?.ancestor_classes c1 o1 i) c2 (Class?.ancestor_objects c1 o1 i) o2))
  = Squash.join_squash (h i)
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c1 o1 } ) -> Tot (disjoint_t (Class?.ancestor_classes c1 o1 i) c2 (Class?.ancestor_objects c1 o1 i) o2))) ->
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #heap #(fun b -> if b then level1 else level2) #(fun b -> if b then t1 else t2) (fun b -> if b then c1 else c2) (fun b -> if b then o1 else o2) h true in
    Squash.return_squash d
  )

let loc_disjoint_ancestors_right
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (#level2: nat)
  (#t2: Type)
  (c2: class root_class level2 t2)
  (o2: t2)
  (h: (
    (i: nat { i < Class?.ancestor_count c2 o2 } ) ->
    Lemma (loc_disjoint l1 (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)))
  ))
: Lemma
  (requires (
    Class?.ancestor_count c2 o2 > 0
  ))
  (ensures (loc_disjoint l1 (loc_of_object c2 o2)))
= let c1 = Location?.class l1 in
  let o1 = Location?.obj l1 in
  let level1 = Location?.level l1 in
  let t1 = Location?.ty l1 in
  let f
    (i: nat { i < Class?.ancestor_count c2 o2 } )
  : Tot (squash (disjoint_t (Class?.ancestor_classes c2 o2 i) c1 (Class?.ancestor_objects c2 o2 i) o1))
  = let _ : squash (disjoint_t c1 (Class?.ancestor_classes c2 o2 i) o1 (Class?.ancestor_objects c2 o2 i)) = Squash.join_squash (h i) in
    Squash.join_squash (loc_disjoint_sym (loc_of_object c1 o1) (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)))
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c2 o2 } ) -> Tot (disjoint_t (Class?.ancestor_classes c2 o2 i) c1 (Class?.ancestor_objects c2 o2 i) o1))) ->
    let d : disjoint_t c1 c2 o1 o2 = DisjointAncestors #heap #(fun b -> if b then level2 else level1) #(fun b -> if b then t2 else t1) (fun b -> if b then c2 else c1) (fun b -> if b then o2 else o1) h false in
    Squash.return_squash d
  )

let loc_disjoint_ind
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (p: (
    (l1: loc root_class) ->
    (l2: loc root_class) ->
    Ghost Type0
    (requires (loc_disjoint l1 l2))
    (ensures (fun _ -> True))
  ))
  (h_object: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o1: ty) ->
    (o2: ty) ->
    squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)) ->
    Lemma
    (p (loc_of_object c o1) (loc_of_object c o2) \/ p (loc_of_object c o2) (loc_of_object c o1))
  ))
  (h_ancestors: (
    (#level1: nat) ->
    (#t1: Type u#b) ->
    (c1: class root_class level1 t1) ->
    (o1: t1) ->
    (l2: loc root_class) ->
    (h: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    )) ->
    squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)) ->
    Lemma
    (p (loc_of_object c1 o1) l2 \/ p l2 (loc_of_object c1 o1))
  ))
  (h_sym: (
    (l1: loc root_class) ->
    (l2: loc root_class) ->
    squash (loc_disjoint l1 l2 /\ loc_disjoint l2 l1 /\ p l1 l2) ->
    Lemma
    (p l2 l1)
  ))
  (l1: loc root_class)
  (l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2))
  (ensures (loc_disjoint l1 l2 /\ p l1 l2))
= let rec g
    (#level1: nat)
    (#ty1: Type u#b)
    (c1: class root_class level1 ty1)
    (o1: ty1)
    (#level2: nat)
    (#ty2: Type u#b)
    (c2: class root_class level2 ty2)
    (o2: ty2)
    (h: disjoint_t c1 c2 o1 o2)
    (z: nat)
  : Lemma
    (requires (z == level1 + level2))
    (ensures (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2) /\ p (loc_of_object c1 o1) (loc_of_object c2 o2)))
    (decreases z)
  = let _ : squash (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2)) = Squash.return_squash (Squash.return_squash h) in
    let j : squash (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2) /\ p (loc_of_object c1 o1) (loc_of_object c2 o2)) =
    match h with
    | DisjointObjects #heap' #level #ty c' o1' o2' h' ->
      let c' : class root_class level ty = c' in
      object_disjoint_sym c' o1' o2';
      h_object c' o1' o2' ();
      Classical.or_elim
	#(p (loc_of_object c' o1') (loc_of_object c' o2'))
	#(p (loc_of_object c' o2') (loc_of_object c' o1'))
	#(fun _ -> p (loc_of_object c' o1') (loc_of_object c' o2') /\ p (loc_of_object c' o2') (loc_of_object c' o1'))
	(fun _ -> h_sym (loc_of_object c' o1') (loc_of_object c' o2') ())
	(fun _ -> h_sym (loc_of_object c' o2') (loc_of_object c' o1') ())
    | DisjointAncestors #heap' #level' #ty' c' o' h' b ->
      let c1: class root_class (level' true) (ty' true) = c' true in
      let o1 = o' true in
      let c2: class root_class (level' false) (ty' false) = c' false in
      let o2 = o' false in
      let l1 = loc_of_object c1 o1 in
      let l2 = loc_of_object c2 o2 in
      let h_
	(i: nat { i < Class?.ancestor_count c1 o1 } )
      : Lemma
        (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
      = let _ : squash (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2) = Squash.return_squash (Squash.return_squash (h' i)) in
	let _ : squash (loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i))) = loc_disjoint_sym (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 in
        let l1' =  (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) in
	let _ : squash (p l1' l2) =
	g (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i) c2 o2 (h' i) (Class?.level (Class?.ancestor_classes c1 o1 i) + level' false)
	in
	h_sym l1' l2 ()
      in
      let _ : squash (p l1 l2 \/ p l2 l1) = h_ancestors c1 o1 l2 h_ () in
      Classical.or_elim
	#(p l1 l2)
	#(p l2 l1)
	#(fun _ -> p l1 l2 /\ p l2 l1)
	(fun _ -> h_sym l1 l2 ())
	(fun _ -> h_sym l2 l1 ())
      in
      j
  in
  let c1 = Location?.class l1 in
  let o1 = Location?.obj l1 in
  let c2 = Location?.class l2 in
  let o2 = Location?.obj l2 in
  let h : squash (disjoint_t c1 c2 o1 o2) = Squash.join_squash () in
  Squash.bind_squash #_ #(p l1 l2) h (fun h -> g c1 o1 c2 o2 h (Class?.level c1 + Class?.level c2))

let loc_disjoint_ind2
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (p: (
    (l1: loc root_class) ->
    (l2: loc root_class) ->
    Ghost Type0
    (requires (loc_disjoint l1 l2))
    (ensures (fun _ -> True))
  ))
  (h_object: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o1: ty) ->
    (o2: ty) ->
    squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)) ->
    Lemma
    (p (loc_of_object c o1) (loc_of_object c o2))
  ))
  (h_ancestors: (
    (#level1: nat) ->
    (#t1: Type u#b) ->
    (c1: class root_class level1 t1) ->
    (o1: t1) ->
    (l2: loc root_class) ->
    (h: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    )) ->
    squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)) ->
    Lemma
    (p (loc_of_object c1 o1) l2 /\ p l2 (loc_of_object c1 o1))
  ))
  (l1: loc root_class)
  (l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2))
  (ensures (loc_disjoint l1 l2 /\ p l1 l2))
= let p' l1 l2 = loc_disjoint l1 l2 /\ loc_disjoint l2 l1 /\ p l1 l2 /\ p l2 l1 in
  let h_object'
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty)
    (o2: ty)
    (h: squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)))
  : Lemma
    (p' (loc_of_object c o1) (loc_of_object c o2) \/ p' (loc_of_object c o2) (loc_of_object c o1))
  = h_object c o1 o2 (); h_object c o2 o1 ()
  in
  let h_ancestors'
    (#level1: nat)
    (#t1: Type u#b)
    (c1: class root_class level1 t1)
    (o1: t1)
    (l2: loc root_class)
    (h: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p' (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p' l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    ))
    (h_: squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)))
  : Lemma
    (p' (loc_of_object c1 o1) l2 \/ p' l2 (loc_of_object c1 o1))
  = let h'
      (i: nat { i < Class?.ancestor_count c1 o1 } )
    : Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    = h i
    in
    h_ancestors c1 o1 l2 h' ()
  in
  let h_sym'
    (l1: loc root_class)
    (l2: loc root_class)
    (h: squash (loc_disjoint l1 l2 /\ loc_disjoint l2 l1 /\ p' l1 l2))
  : Lemma
    (p' l2 l1)
  = ()
  in
  loc_disjoint_ind p' h_object' h_ancestors' h_sym' l1 l2

let locset
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (root_class: class' heap 0 root_type)
: GTot (Type u#(1 + max a b))
= TSet.set (loc root_class)

let locset_of_object
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#ty: Type u#b)
  (#level: nat)
  (class: class root_class level ty)
  (obj: ty)
: Tot (locset root_class)
= TSet.singleton (loc_of_object class obj)

abstract
let modifies
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class)
  (h h': heap)
: Tot Type0
= forall (ty: Type) (l: nat) (c: class root_class l ty) (o: ty) .
    (forall (o': loc root_class { TSet.mem o' s }) . loc_disjoint (loc_of_object c o) o') ==>
    Class?.preserved c o h h'

abstract
let modifies_equiv
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class)
  (h h': heap)
: Lemma
  (requires True)
  (ensures (modifies s h h' <==> (
    forall (ty: Type) (l: nat) (c: class root_class l ty) (o: ty) .
    (forall (o': loc root_class { TSet.mem o' s }) . loc_disjoint (loc_of_object c o) o') ==>
    Class?.preserved c o h h'  
  )))
  [SMTPat (modifies s h h')]
= ()

abstract
let modifies_elim
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class)
  (h h': heap)
  (mod: squash (modifies s h h'))
  (#ty: Type u#b)
  (#l: nat)
  (c: class root_class l ty)
  (o: ty)
  (f: (
    (o': loc root_class { TSet.mem o' s }) ->
    Lemma
    (loc_disjoint (loc_of_object c o) o')
  ))
: Lemma
  (Class?.preserved c o h h')
= Classical.forall_intro f

abstract
let modifies_intro
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class)
  (h h': heap)
  (f: (
    (ty: Type u#b) ->
    (l: nat) ->
    (c: class root_class l ty ) ->
    (o: ty) ->
    (g: (
      (o' : loc root_class { TSet.mem o' s } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) o')
    )) ->
    Lemma
    (Class?.preserved c o h h')
  ))
: Lemma
  (modifies s h h')
= let f'
    (ty: Type u#b)
    (l: nat)
    (c: class root_class l ty )
    (o: ty)
  : Lemma
    ((forall (o' : loc root_class { TSet.mem o' s } ) . (loc_disjoint (loc_of_object c o) o')) ==>
      (Class?.preserved c o h h')
    )
  = Classical.impl_intro_gen #(forall (o' : loc root_class { TSet.mem o' s } ) . (loc_disjoint (loc_of_object c o) o')) #(fun _ -> Class?.preserved c o h h') (fun _ -> f ty l c o (fun _ -> ()))
  in
  let g
    (ty: Type u#b)
  : Lemma  (forall 
      (l: nat)
      (c: class root_class l ty )
      (o: ty)
      .
	((forall (o' : loc root_class { TSet.mem o' s } ) . (loc_disjoint (loc_of_object c o) o')) ==>
	  (Class?.preserved c o h h')
    ))
  = Classical.forall_intro_3 (f' ty)
  in
  Classical.forall_intro g

let modifies_refl
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class)
  (h: heap)
: Lemma
  (requires True)
  (ensures (modifies s h h))
  [SMTPat (modifies s h h)]
= ()

let modifies_trans
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class )
  (h1 h2 h3: heap)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
  [SMTPatT u#(max a b) (modifies s h1 h2); SMTPatT (modifies s h2 h3)]
= ()

(*
let modifies_subset
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s1 s2: locset root_class)
  (h h': heap)
: Lemma
  (requires (modifies s1 h h' /\ TSet.subset s1 s2))
  (ensures (modifies s2 h h'))
  [SMTPatT u#(max a b) (modifies s1 h h'); SMTPatT (TSet.subset s1 s2)]
= modifies_equiv s1 h h';
  modifies_equiv s2 h h'
*)

private
let modifies_test_1
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#ty: Type u#b)
  (#level: nat)
  (c: class root_class level ty)
  (#ty2: Type u#b)
  (#level2: nat)
  (c2: class root_class level2 ty2)
  (o1 o3: ty)
  (o2: ty2)
  (h h': heap)
: Lemma
  (requires (Class?.disjoint c o1 o3 /\ loc_disjoint (loc_of_object c o3) (loc_of_object c2 o2) /\ modifies (TSet.union (locset_of_object c o1) (locset_of_object c2 o2)) h h'))
  (ensures (Class?.preserved c o3 h h'))
= ()

let rec fresh
  (#heap: Type u#a)
  (#level: nat)
  (#ty: Type u#b)
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
  (#heap: Type u#a)
  (#level: nat)
  (#ty: Type u#b)
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
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type u#b)
  (c: class root_class level ty)
  (o: ty)
  (h0 h1 h2: heap)
: Lemma
  (requires (fresh c o h0 h1 /\ Class?.live c h2 o))
  (ensures (fresh c o h0 h2))
  [SMTPatT u#(max a b) (fresh c o h0 h1); SMTPatT (Class?.live c h2 o)]
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
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#levelold: nat) (#tyold: Type u#b)
  (#levelnew: nat) (#tynew: Type u#b)
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
  (ensures (loc_disjoint (loc_of_object cold oold) (loc_of_object cnew onew)))
  (decreases (levelold + levelnew))
  [SMTPatT u#(max a b) (Class?.live cold hbefore oold); SMTPatT (Class?.live cold hafter oold); SMTPatT (fresh cnew onew hbefore hafter)]
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
	(loc_disjoint (loc_of_object cold oold) (loc_of_object (Class?.ancestor_classes cnew onew i) (Class?.ancestor_objects cnew onew i)))
      = let cnew' = Class?.ancestor_classes cnew onew i in
	let onew' = Class?.ancestor_objects cnew onew i in
	fresh_disjoint cold cnew' oold onew' hbefore hafter
      in
      loc_disjoint_ancestors_right (loc_of_object cold oold) cnew onew f
  else
    let f
      (i: nat { i < Class?.ancestor_count cold oold } )
    : Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes cold oold i) (Class?.ancestor_objects cold oold i)) (loc_of_object cnew onew))
    = let cold' = Class?.ancestor_classes cold oold i in
      let oold' = Class?.ancestor_objects cold oold i in
      fresh_disjoint cold' cnew oold' onew hbefore hafter
    in
    loc_disjoint_ancestors_left cold oold (loc_of_object cnew onew) f

let locset_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls1 ls2: locset root_class)
: Tot Type0
= forall
    (l1: loc root_class { TSet.mem l1 ls1 } )
    (l2: loc root_class { TSet.mem l2 ls2 } )
  .
    loc_disjoint l1 l2

let locset_disjoint_sym
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls1 ls2: locset root_class)
: Lemma
  (requires (locset_disjoint ls1 ls2))
  (ensures (locset_disjoint ls2 ls1))
  [SMTPatT u#0 (locset_disjoint ls1 ls2)]
= let f
    (x: loc root_class { TSet.mem x ls2 } )
  : Lemma
    (forall (y: loc root_class { TSet.mem y ls1 }) . loc_disjoint x y )
  = let g 
      (y: loc root_class { TSet.mem y ls1 } )
    : Lemma (ensures ( loc_disjoint x y ))
    = loc_disjoint_sym y x
    in
    Classical.forall_intro g
  in
  Classical.forall_intro f

let locset_disjoint_loc_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1 l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2))
  (ensures (locset_disjoint (TSet.singleton l1) (TSet.singleton l2)))
  [SMTPat (locset_disjoint (TSet.singleton l1) (TSet.singleton l2))]
= ()

noeq
private
type locset_includes_object_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
:
  (ls: locset root_class) ->
  (#level: nat) ->
  (#ty: Type u#b) ->
  (c: class root_class level ty) ->
  (o: ty) ->
  Type u#(1 + max a b)
=
| LocsetIncludesObject:
    (ls: locset root_class) ->
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o1: ty { TSet.mem (loc_of_object c o1) ls } ) ->
    (o2: ty { Class?.includes c o1 o2 } ) ->
    locset_includes_object_t ls c o2
| LocsetIncludesAncestors:
    (ls: locset root_class) ->
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o: ty { Class?.ancestor_count c o > 0 } ) ->
    (f: (
      (i: nat {i < Class?.ancestor_count c o } ) ->
      Tot (locset_includes_object_t ls (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i))
    )) ->
    locset_includes_object_t ls c o

abstract
let locset_includes_loc
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class)
: Tot Type0
= squash (locset_includes_object_t ls (Location?.class l) (Location?.obj l))

let mem_locset_includes_loc
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class)
: Lemma
  (requires (TSet.mem l ls))
  (ensures (locset_includes_loc ls l))
  [SMTPat (TSet.mem l ls)]
= let (Location _ _ c o) = l in
  object_includes_refl c o;
  Squash.return_squash (LocsetIncludesObject ls c o o)

let locset_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls_big ls_small: locset root_class)
: Tot Type0
= forall (l: loc root_class { TSet.mem l ls_small } ) . locset_includes_loc ls_big l

let subset_locset_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls_big ls_small: locset root_class)
: Lemma
  (requires (TSet.subset ls_small ls_big))
  (ensures (locset_includes ls_big ls_small))
  [SMTPat (TSet.subset ls_small ls_big)]
= ()

let locset_includes_loc_object
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (#level: nat)
  (#ty: Type u#b)
  (c: class root_class level ty)
  (o1: ty )
  (o2: ty )
: Lemma
  (requires (TSet.mem (loc_of_object c o1) ls /\ Class?.includes c o1 o2))
  (ensures (locset_includes_loc ls (loc_of_object c o2)))
  [SMTPat (TSet.mem (loc_of_object c o1)); SMTPatT (Class?.includes c o1 o2)]
= Squash.return_squash (LocsetIncludesObject ls c o1 o2)

let locset_includes_locset_of_object
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#ty: Type u#b)
  (c: class root_class level ty)
  (o1: ty )
  (o2: ty )
: Lemma
  (requires (Class?.includes c o1 o2))
  (ensures (locset_includes (locset_of_object c o1) (locset_of_object c o2)))
  [SMTPat (locset_includes (locset_of_object c o1) (locset_of_object c o2))]
= locset_includes_loc_object (locset_of_object c o1) c o1 o2

let locset_includes_loc_ancestors
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (#level: nat)
  (#ty: Type u#b)
  (c: class root_class level ty)
  (o: ty { Class?.ancestor_count c o > 0 } )
  (f: (
    (i: nat {i < Class?.ancestor_count c o } ) ->
    Lemma (locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
  ))
: Lemma
  (locset_includes_loc ls (loc_of_object c o))
= let g
    (i: nat {i < Class?.ancestor_count c o } )
  : Tot (squash (locset_includes_object_t ls (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
  = Squash.join_squash (f i)
  in
  let g = SquashProperties.squash_arrow g in
  Squash.bind_squash g (fun (h: ((i: nat {i < Class?.ancestor_count c o } ) -> Tot (locset_includes_object_t ls (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))) -> Squash.return_squash (LocsetIncludesAncestors ls c o h))

let locset_includes_loc_ind
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (p: ((l: loc root_class { locset_includes_loc ls l }) -> Tot Type0))
  (h_object: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o1: ty { TSet.mem (loc_of_object c o1) ls } ) ->
    (o2: ty { Class?.includes c o1 o2 /\ locset_includes_loc ls (loc_of_object c o2) } ) ->
    Lemma
    (p (loc_of_object c o2))
  ))
  (h_ancestors: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o: ty { Class?.ancestor_count c o > 0 /\ locset_includes_loc ls (loc_of_object c o) } ) ->
    (f: (
      (i: nat {i < Class?.ancestor_count c o } ) ->
      Lemma
      (locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)) /\ p (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
    )) ->
    Lemma
    (p (loc_of_object c o))
  ))
  (l: loc root_class { locset_includes_loc ls l } )
: Lemma
  (p l)
= let rec g
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o: ty)
    (h: locset_includes_object_t ls c o)
  : Lemma
    (requires True)
    (ensures (locset_includes_loc ls (loc_of_object c o) /\ p (loc_of_object c o)))
    (decreases level)
  = let h' : locset_includes_loc ls (loc_of_object c o) = Squash.return_squash h in
    match h with
    | LocsetIncludesObject _ c' o1 o2 ->
      h_object c' o1 o2
    | LocsetIncludesAncestors _ c' o' f ->
      let f'
	(i: nat {i < Class?.ancestor_count c' o' } )
      : Lemma
        (locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c' o' i) (Class?.ancestor_objects c' o' i)) /\ p (loc_of_object (Class?.ancestor_classes c' o' i) (Class?.ancestor_objects c' o' i)))
      = g (Class?.ancestor_classes c' o' i) (Class?.ancestor_objects c' o' i) (f i)
      in
      h_ancestors c' o' f'
  in
  let (Location _ _ c o) = l in
  let h : squash (locset_includes_object_t ls c o) = Squash.join_squash () in
  Squash.bind_squash #_ #(p l) h (fun (h: locset_includes_object_t ls c o) ->
    let h' : squash (p l) = g c o h in h'
  )

private
let locset_includes_loc_includes_p_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class { locset_includes_loc ls l } )
: Tot Type
= (o: Location?.ty l { Class?.includes (Location?.class l) (Location?.obj l) o } ) ->
  Lemma
  (locset_includes_loc ls (Location _ _ (Location?.class l) o))

private
let locset_includes_loc_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class { locset_includes_loc ls l } )
  (o: Location?.ty l { Class?.includes (Location?.class l) (Location?.obj l) o } )
: Lemma
  (locset_includes_loc ls (Location _ _ (Location?.class l) o))
= let p
    (l: loc root_class { locset_includes_loc ls l })
  : Tot Type0
  = squash (locset_includes_loc_includes_p_t ls l)
  in
  let h_object
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty { TSet.mem (loc_of_object c o1) ls } )
    (o2: ty { Class?.includes c o1 o2 /\ locset_includes_loc ls (loc_of_object c o2) } )
  : Lemma
    (p (loc_of_object c o2))
  = let f
      (o3: ty { Class?.includes c o2 o3 } )
    : Lemma
      (locset_includes_loc ls (loc_of_object c o3))
    = object_includes_trans c o1 o2 o3;
      locset_includes_loc_object ls c o1 o3
    in
    let g : locset_includes_loc_includes_p_t ls (loc_of_object c o2) = f in
    Squash.return_squash g
  in
  let h_ancestors
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o: ty { Class?.ancestor_count c o > 0 /\ locset_includes_loc ls (loc_of_object c o) } )
    (f: (
      (i: nat {i < Class?.ancestor_count c o } ) ->
      Lemma
      (locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)) /\ p (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
    ))
  : Lemma
    (p (loc_of_object c o))
  = let g
      (o': ty {Class?.includes c o o'})
    : Lemma
      (locset_includes_loc ls (loc_of_object c o'))
    = let _ : squash (Class?.ancestor_count c o' > 0) =
	if Class?.level c = 0
	then let (n: nat) = Class?.ancestor_class_levels c o 0 in
	     let _ = assert (n < 0) in
	     false_elim ()
	else ()
      in
      let k
	(i': nat {i' < Class?.ancestor_count c o' } )
      : Lemma
	(locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o' i') (Class?.ancestor_objects c o' i')))
      = Squash.bind_squash
          #_
	  #(locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o' i') (Class?.ancestor_objects c o' i')))
	  (object_includes_ancestors c o o' i')
	  (fun (i: (i : nat {i < Class?.ancestor_count c o} ) {
	    includes_ancestors_t_prop c o o' i' i
	  } ) ->
	    f i;
	    let (o_ : loc root_class { locset_includes_loc ls o_ } ) =
	      loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)
	    in
            Squash.bind_squash
	      #(locset_includes_loc_includes_p_t ls o_)
	      #(locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o' i') (Class?.ancestor_objects c o' i')))
	      (Squash.join_squash ())
	      (fun (j: locset_includes_loc_includes_p_t ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i))) ->
		j (Class?.ancestor_objects c o' i')
        ))
      in
      locset_includes_loc_ancestors ls c o' k
    in
    let g' : locset_includes_loc_includes_p_t ls (loc_of_object c o) = g in
    Squash.return_squash (Squash.return_squash g')
  in
  let _ : squash (p l) =
    locset_includes_loc_ind ls p h_object h_ancestors l
  in
  Squash.bind_squash #_ #(locset_includes_loc ls (Location _ _ (Location?.class l) o)) (Squash.join_squash ()) (fun (f: locset_includes_loc_includes_p_t ls l) ->
    f o
  )

let locset_includes_loc_trans
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls0: locset root_class)
  (ls: locset root_class { locset_includes ls0 ls } )
  (l: loc root_class { locset_includes_loc ls l } )
: Lemma
  (locset_includes_loc ls0 l)
= let p
    (l: loc root_class { locset_includes_loc ls l })
  : Tot Type0
  = locset_includes_loc ls0 l
  in
  let h_object
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty { TSet.mem (loc_of_object c o1) ls } )
    (o2: ty { Class?.includes c o1 o2 /\ locset_includes_loc ls (loc_of_object c o2) } )
  : Lemma
    (p (loc_of_object c o2))
  = locset_includes_loc_includes ls0 (loc_of_object c o1) o2
  in
  let h_ancestors
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o: ty { Class?.ancestor_count c o > 0 /\ locset_includes_loc ls (loc_of_object c o) } )
    (f: (
      (i: nat {i < Class?.ancestor_count c o } ) ->
      Lemma
      (locset_includes_loc ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)) /\ p (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
    ))
  : Lemma
    (p (loc_of_object c o))
  = locset_includes_loc_ancestors ls0 c o f
  in
  locset_includes_loc_ind ls p h_object h_ancestors l

let locset_includes_trans
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls0: locset root_class)
  (ls1: locset root_class)
  (ls2: locset root_class)
: Lemma
  (requires (locset_includes ls0 ls1 /\ locset_includes ls1 ls2))
  (ensures (locset_includes ls0 ls2))
  [SMTPat (locset_includes ls0 ls1); SMTPat (locset_includes ls1 ls2)]
= let f
    (l: loc root_class { TSet.mem l ls2 } )
  : Lemma
    (locset_includes_loc ls0 l)
  = locset_includes_loc_trans ls0 ls1 l
  in
  Classical.forall_intro f

(* Same thing, to provide the witness *)

let locset_includes_trans'
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls1: locset root_class)
: Lemma
  (requires True)
  (ensures (forall
    (ls0: locset root_class)
    (ls2: locset root_class)
  .
    (locset_includes ls0 ls1 /\ locset_includes ls1 ls2) ==>
    locset_includes ls0 ls2
  ))
= let f
    (ls0: locset root_class)
  : Tot (
      (ls2: locset root_class) ->
      Lemma (
	(locset_includes ls0 ls1 /\ locset_includes ls1 ls2) ==>
	locset_includes ls0 ls2
  ))
  = let p
      (ls2: locset root_class)
    : Tot Type0
    = (locset_includes ls0 ls1 /\ locset_includes ls1 ls2)
    in
    let q
      (ls2: locset root_class)
    : Tot Type0
    = locset_includes ls0 ls2
    in
    let g
      (ls2: locset root_class)
    : Lemma
      (requires (p ls2))
      (ensures (q ls2))
    = locset_includes_trans ls0 ls1 ls2
    in
    Classical.move_requires #_ #p #q g
  in
  Classical.forall_intro_2 f

(*
let locset_includes_refl
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls0: locset root_class)
: Lemma
  (requires True)
  (ensures (locset_includes ls0 ls0))
  [SMTPat (locset_includes ls0 ls0)]
= ()
*)

unfold
private
let loc_disjoint_object_includes_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class { loc_disjoint l1 l2 } )
: Tot (Type u#b)
= (o1: Location?.ty l1 { Class?.includes (Location?.class l1) (Location?.obj l1) o1 } ) ->
  (o2: Location?.ty l2 { Class?.includes (Location?.class l2) (Location?.obj l2) o2 } ) ->
  Lemma
    (loc_disjoint (loc_of_object (Location?.class l1) o1) (loc_of_object (Location?.class l2) o2))

private
let loc_disjoint_object_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class { loc_disjoint l1 l2 } )
: Tot Type0
= squash (loc_disjoint_object_includes_t l1 l2)

private
let loc_disjoint_object_includes_sym
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2 /\ loc_disjoint_object_includes l1 l2))
  (ensures (loc_disjoint l2 l1 /\ loc_disjoint_object_includes l2 l1))
= let (l2: loc root_class { loc_disjoint l1 l2 } ) = l2 in
  loc_disjoint_sym l1 l2;
  let (l1: loc root_class { loc_disjoint l2 l1 } ) = l1 in
  Squash.bind_squash #_ #(loc_disjoint_object_includes_t l2 l1) (Squash.join_squash ()) (fun (f: loc_disjoint_object_includes_t l1 l2) ->
    Squash.return_squash (
      let g
	(o2: Location?.ty l2 { Class?.includes (Location?.class l2) (Location?.obj l2) o2 } )
	(o1: Location?.ty l1 { Class?.includes (Location?.class l1) (Location?.obj l1) o1 } )
      : Lemma
    (loc_disjoint (loc_of_object (Location?.class l2) o2) (loc_of_object (Location?.class l1) o1))
      = f o1 o2; loc_disjoint_sym (loc_of_object (Location?.class l2) o2) (loc_of_object (Location?.class l1) o1)
      in g
  ))

private
let loc_disjoint_object_includes_elim
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
  (o1: Location?.ty l1 { Class?.includes (Location?.class l1) (Location?.obj l1) o1 } )
  (o2: Location?.ty l2 { Class?.includes (Location?.class l2) (Location?.obj l2) o2 } )  
: Lemma
  (requires (loc_disjoint l1 l2 /\ loc_disjoint_object_includes l1 l2))
  (ensures  (loc_disjoint (loc_of_object (Location?.class l1) o1) (loc_of_object (Location?.class l2) o2)))
= let (l2: loc root_class { loc_disjoint l1 l2 } ) = l2 in
  Squash.bind_squash #_ #(loc_disjoint (loc_of_object (Location?.class l1) o1) (loc_of_object (Location?.class l2) o2)) (Squash.join_squash ()) (fun (f: loc_disjoint_object_includes_t l1 l2) -> f o1 o2)

private
let loc_disjoint_object_includes_intro
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
: Lemma
  (requires (loc_disjoint l1 l2))
  (ensures (loc_disjoint l1 l2 /\ loc_disjoint_object_includes l1 l2))
= let p
    (l1: loc root_class)
    (l2: loc root_class)
  : Tot Type0
  = loc_disjoint l1 l2 ==> loc_disjoint_object_includes #heap #root_type #root_class l1 l2
  in
  let h_object
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty)
    (o2: ty)
    (h: squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)))
  : Lemma
    (p (loc_of_object c o1) (loc_of_object c o2) \/ p (loc_of_object c o2) (loc_of_object c o1))
  = let f
      (o1': ty { Class?.includes c o1 o1' } )
      (o2': ty { Class?.includes c o2 o2' } )
    : Lemma
      (loc_disjoint (loc_of_object c o1') (loc_of_object c o2'))
    = object_disjoint_includes c o1 o2 o1' o2' ;
      loc_disjoint_objects c o1' o2'
    in
    let f' : squash (loc_disjoint_object_includes_t (loc_of_object c o1) (loc_of_object c o2)) = Squash.return_squash f in
    let g : squash (loc_disjoint_object_includes (loc_of_object c o1) (loc_of_object c o2)) =
      Squash.return_squash f'
    in
    g
  in
  let h_ancestors
    (#level1: nat)
    (#t1: Type u#b)
    (c1: class root_class level1 t1)
    (o1: t1)
    (l2: loc root_class)
    (h: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    ))
    (h': squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)))
  : Lemma
    (p (loc_of_object c1 o1) l2 \/ p l2 (loc_of_object c1 o1))
  = let (Location t2 level2 c2 o2) = l2 in
    let f
      (o1': t1 { Class?.includes c1 o1 o1' } )
      (o2': t2 { Class?.includes c2 o2 o2' } )
    : Lemma
      (loc_disjoint (loc_of_object c1 o1') (loc_of_object c2 o2'))
    = let _ : squash (Class?.level c1 > 0) =
	if Class?.level c1 = 0
	then let (y: nat {y < 0}) = Class?.ancestor_class_levels c1 o1 0 in assert False
	else ()
      in
      assert (Class?.ancestor_count c1 o1' > 0);
      let g
	(i': nat {i' < Class?.ancestor_count c1 o1'})
      : Lemma
	(loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1' i') (Class?.ancestor_objects c1 o1' i')) (loc_of_object c2 o2'))
      = Squash.bind_squash
	  #_
	  #(loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1' i') (Class?.ancestor_objects c1 o1' i')) (loc_of_object c2 o2'))
	  (object_includes_ancestors c1 o1 o1' i')
	  (fun (i: (i: nat {i < Class?.ancestor_count c1 o1}) { includes_ancestors_t_prop c1 o1 o1' i' i } ) ->
	    h i;
	    loc_disjoint_object_includes_elim (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) (loc_of_object c2 o2) (Class?.ancestor_objects c1 o1' i') o2'
	  )
      in
      loc_disjoint_ancestors_left c1 o1' (loc_of_object c2 o2') g
    in
    let (l2: loc root_class { loc_disjoint (loc_of_object c1 o1) l2 } ) = l2 in
    let f' : squash (loc_disjoint_object_includes_t (loc_of_object c1 o1) l2) = Squash.return_squash f in
    let g : squash (loc_disjoint_object_includes (loc_of_object c1 o1) l2) =
      Squash.return_squash f'
    in
    g    
  in
  loc_disjoint_ind
    p
    h_object
    h_ancestors
    (fun l1 l2 _ -> loc_disjoint_object_includes_sym l1 l2)
    l1
    l2

let loc_disjoint_locset_includes_loc
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l: loc root_class)
  (ls: locset root_class)
  (h: (
    (l1: loc root_class { TSet.mem l1 ls } ) ->
    Lemma
    (loc_disjoint l l1)
  ))
  (l2: loc root_class { locset_includes_loc ls l2 } )
: Lemma
  (loc_disjoint l l2)
= locset_includes_loc_ind
    ls
    (fun l' -> loc_disjoint l l')
    (fun #level #ty c o1 o2 ->
      let _ : squash (loc_disjoint l (loc_of_object c o1)) = h (loc_of_object c o1) in
      let j : squash (loc_disjoint_object_includes l (loc_of_object c o1)) = loc_disjoint_object_includes_intro l (loc_of_object c o1) in
      object_includes_refl (Location?.class l) (Location?.obj l);
      loc_disjoint_object_includes_elim l (loc_of_object c o1) (Location?.obj l) o2
    )
    (fun #level #ty c o f ->
      loc_disjoint_ancestors_right l c o f
    )
    l2

let locset_disjoint_locset_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls1: locset root_class)
  (ls2: locset root_class)
  (ls2': locset root_class)
: Lemma
  (requires (locset_disjoint ls1 ls2 /\ locset_includes ls2 ls2'))
  (ensures  (locset_disjoint ls1 ls2'))
  [SMTPat (locset_disjoint ls1 ls2); SMTPat (locset_includes ls2 ls2')]
= let f
    (l1: loc root_class { TSet.mem l1 ls1 } )
  : Lemma
    (forall (l2' : loc root_class { TSet.mem l2' ls2' } ) . loc_disjoint l1 l2' )
  = let g
      (l2' : loc root_class { TSet.mem l2' ls2' } )
    : Lemma
      (loc_disjoint l1 l2')
    = loc_disjoint_locset_includes_loc l1 ls2 (fun _ -> ()) l2'
    in
    Classical.forall_intro g
  in
  Classical.forall_intro f

let modifies_locset_includes
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s1 s2: locset root_class)
  (h h': heap)
: Lemma
  (requires (modifies s2 h h' /\ locset_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s2 h h'); SMTPatT (locset_includes s1 s2)]
= modifies_equiv s1 h h';
  modifies_equiv s2 h h';
  let f
    (ty: Type u#b)
    (l: nat)
    (c: class root_class l ty )
    (o: ty)
    (g: (
      (o' : loc root_class { TSet.mem o' s1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) o')
    ))
  : Lemma
    (Class?.preserved c o h h')
  = let k
      (o' : loc root_class { TSet.mem o' s2 } ) 
    : Lemma
      (loc_disjoint (loc_of_object c o) o')
    = loc_disjoint_locset_includes_loc (loc_of_object c o) s1 g o'
    in
    Classical.forall_intro k
  in
  modifies_intro s1 h h' f

(* How to refine ancestors with
their immediate child if we know that all siblings of the child (in the
same class) are preserved. *)

unfold
private
let modifies_loc_refines_p_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level1_: nat)
  (#ty1_: Type u#b)
  (c1_: class root_class level1_ ty1_)
  (o1_: ty1_)
  (h h': heap)
  (l1: loc root_class)
  (l2: loc root_class)
: Tot Type
= squash (l2 == loc_of_object c1_ o1_) -> Lemma (Class?.preserved (Location?.class l1) (Location?.obj l1) h h')

private
let modifies_loc_refines_p_t_elim
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level1_: nat)
  (#ty1_: Type u#b)
  (c1_: class root_class level1_ ty1_)
  (o1_: ty1_)
  (h h': heap)
  (l1: loc root_class)
  (l2: loc root_class)  
  (f: modifies_loc_refines_p_t c1_ o1_ h h' l1 l2)
  (u: squash (l2 == loc_of_object c1_ o1_))
: Lemma
  (Class?.preserved (Location?.class l1) (Location?.obj l1) h h')
= f u

private
let modifies_loc_refines_p_elim
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level1_: nat)
  (#ty1_: Type u#b)
  (c1_: class root_class level1_ ty1_)
  (o1_: ty1_)
  (h h': heap)
  (l1: loc root_class)
  (l2: loc root_class)  
  (f: squash (squash (modifies_loc_refines_p_t c1_ o1_ h h' l1 l2)))
  (u: squash (l2 == loc_of_object c1_ o1_))
: Lemma
  (Class?.preserved (Location?.class l1) (Location?.obj l1) h h')
= Squash.bind_squash #_ #(Class?.preserved (Location?.class l1) (Location?.obj l1) h h') (Squash.join_squash f) (fun (f: modifies_loc_refines_p_t c1_ o1_ h h' l1 l2) ->
    modifies_loc_refines_p_t_elim c1_ o1_ h h' l1 l2 f u
  )

abstract
let modifies_loc_refines
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level1_: nat)
  (#ty1_: Type u#b)
  (c1_: class root_class level1_ ty1_)
  (o1_: ty1_)
  (h h': heap)
  (f0: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o: ty) ->
    (f: (
      (i: nat { i < Class?.ancestor_count c1_ o1_ } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) (loc_of_object (Class?.ancestor_classes c1_ o1_ i) (Class?.ancestor_objects c1_ o1_ i)))
    )) ->
    Lemma
    (Class?.preserved c o h h')
  ))
  (f1: (
    (o1': ty1_) ->
    squash (Class?.disjoint c1_ o1_ o1') ->
    Lemma
    (Class?.preserved c1_ o1' h h')
  ))
  (#level_: nat)
  (#ty_: Type u#b)
  (c_: class root_class level_ ty_)
  (o_: ty_)
  (f: squash (loc_disjoint (loc_of_object c_ o_) (loc_of_object c1_ o1_)))
: Lemma
  (Class?.preserved c_ o_ h h')
= let p
    (l1: loc root_class)
    (l2: loc root_class)
  : Tot Type0
  = squash (modifies_loc_refines_p_t c1_ o1_ h h' l1 l2)
  in
  let h_object
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty)
    (o2: ty)
    (g: squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)))
  : Lemma
    (p (loc_of_object c o1) (loc_of_object c o2))
  = let q
      (g': squash (loc_of_object c o2 == loc_of_object c1_ o1_))
    : Lemma
      (Class?.preserved c o1 h h')
    = f1 o1 ()
    in
    let r : modifies_loc_refines_p_t c1_ o1_ h h' (loc_of_object c o1) (loc_of_object c o2) = q in
    Squash.return_squash (Squash.return_squash r)
  in
  let h_ancestors
    (#level1: nat)
    (#t1: Type u#b)
    (c1: class root_class level1 t1)
    (o1: t1)
    (l2: loc root_class)
    (g: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    ))
    (g': squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)))
  : Lemma
    (p (loc_of_object c1 o1) l2 /\ p l2 (loc_of_object c1 o1))
  = let g1 : modifies_loc_refines_p_t c1_ o1_ h h' (loc_of_object c1 o1) l2 =
      let g1
	(g1': squash (l2 == loc_of_object c1_ o1_))
      : Lemma
	(Class?.preserved c1 o1 h h')
      = let phi
	  (i: nat { i < Class?.ancestor_count c1 o1 } )
	: Lemma
	  (Class?.preserved (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i) h h')
	= modifies_loc_refines_p_elim c1_ o1_ h h' (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 (g i) ()
	in
	preserved_ancestors_preserved c1 o1 h h' phi
      in
      g1
    in
    let g2 : modifies_loc_refines_p_t c1_ o1_ h h' l2 (loc_of_object c1 o1) =
      let g2
	(g2': squash (loc_of_object c1 o1 == loc_of_object c1_ o1_))
      : Lemma
	(Class?.preserved (Location?.class l2) (Location?.obj l2) h h')
      = f0 (Location?.class l2) (Location?.obj l2) g
      in
      g2
    in
    Squash.return_squash (Squash.return_squash g1);
    Squash.return_squash (Squash.return_squash g2)
  in
  let f' : squash (p (loc_of_object c_ o_) (loc_of_object c1_ o1_)) =
    loc_disjoint_ind2 p h_object h_ancestors (loc_of_object c_ o_) (loc_of_object c1_ o1_)
  in
  modifies_loc_refines_p_elim c1_ o1_ h h' (loc_of_object c_ o_) (loc_of_object c1_ o1_) f' ()

(* Special case for level 0 (needed because argument f above is not provable for level 0) *)

let modifies_loc_refines_0
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#ty1_: Type u#b)
  (c1_: class root_class 0 ty1_)
  (o1_: ty1_)
  (h h': heap)
  (f1: (
    (o1': ty1_) ->
    squash (Class?.disjoint c1_ o1_ o1') ->
    Lemma
    (Class?.preserved c1_ o1' h h')
  ))
  (#level_: nat)
  (#ty_: Type u#b)
  (c_: class root_class level_ ty_)
  (o_: ty_)
  (f: squash (loc_disjoint (loc_of_object c_ o_) (loc_of_object c1_ o1_)))
: Lemma
  (Class?.preserved c_ o_ h h')
= let p
    (l1: loc root_class)
    (l2: loc root_class)
  : Tot Type0
  = squash (modifies_loc_refines_p_t c1_ o1_ h h' l1 l2)
  in
  let h_object
    (#level: nat)
    (#ty: Type u#b)
    (c: class root_class level ty)
    (o1: ty)
    (o2: ty)
    (g: squash (Class?.disjoint c o1 o2 /\ Class?.disjoint c o2 o1 /\ loc_disjoint (loc_of_object c o1) (loc_of_object c o2) /\ loc_disjoint (loc_of_object c o2) (loc_of_object c o1)))
  : Lemma
    (p (loc_of_object c o1) (loc_of_object c o2))
  = let q
      (g': squash (loc_of_object c o2 == loc_of_object c1_ o1_))
    : Lemma
      (Class?.preserved c o1 h h')
    = f1 o1 ()
    in
    let r : modifies_loc_refines_p_t c1_ o1_ h h' (loc_of_object c o1) (loc_of_object c o2) = q in
    Squash.return_squash (Squash.return_squash r)
  in
  let h_ancestors
    (#level1: nat)
    (#t1: Type u#b)
    (c1: class root_class level1 t1)
    (o1: t1)
    (l2: loc root_class)
    (g: (
      (i: nat { i < Class?.ancestor_count c1 o1 } ) ->
      Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ loc_disjoint l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) /\ p (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 /\ p l2 (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)))
    ))
    (g': squash (Class?.ancestor_count c1 o1 > 0 /\ loc_disjoint (loc_of_object c1 o1) l2 /\ loc_disjoint l2 (loc_of_object c1 o1)))
  : Lemma
    (p (loc_of_object c1 o1) l2 /\ p l2 (loc_of_object c1 o1))
  =
    let g1 : modifies_loc_refines_p_t c1_ o1_ h h' (loc_of_object c1 o1) l2 =
      let g1
	(g1': squash (l2 == loc_of_object c1_ o1_))
      : Lemma
	(Class?.preserved c1 o1 h h')
      = let phi
	  (i: nat { i < Class?.ancestor_count c1 o1 } )
	: Lemma
	  (Class?.preserved (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i) h h')
	= modifies_loc_refines_p_elim c1_ o1_ h h' (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2 (g i) ()
	in
	preserved_ancestors_preserved c1 o1 h h' phi
      in
      g1
    in
    let g2 : modifies_loc_refines_p_t c1_ o1_ h h' l2 (loc_of_object c1 o1) =
      let g2
	(g2': squash (loc_of_object c1 o1 == loc_of_object c1_ o1_))
      : Lemma
	(Class?.preserved (Location?.class l2) (Location?.obj l2) h h')
      = let (n: nat) = Class?.ancestor_class_levels c1 o1 0 in
	let _ : squash (n < 0) = () in
	assert False
      in
      g2
    in
    Squash.return_squash (Squash.return_squash g1);
    Squash.return_squash (Squash.return_squash g2)
  in
  let f' : squash (p (loc_of_object c_ o_) (loc_of_object c1_ o1_)) =
    loc_disjoint_ind2 p h_object h_ancestors (loc_of_object c_ o_) (loc_of_object c1_ o1_)
  in
  modifies_loc_refines_p_elim c1_ o1_ h h' (loc_of_object c_ o_) (loc_of_object c1_ o1_) f' ()
