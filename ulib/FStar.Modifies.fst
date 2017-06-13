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
  (final: (carrier -> Pure Type0 (requires (level == 0)) (ensures (fun _ -> True)))) ->
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
  [smt_pat (Class?.carrier c)]
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
  [smt_pat (Class?.carrier (Class?.ancestor_classes c x i))]
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
let level_0_live_dead_disjoint_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (oold: ty) ->
  (onew: ty) ->
  (hbefore: heap) ->
  Lemma
  (requires (
    level == 0 /\
    Class?.live c hbefore oold /\
    (~ (Class?.contains c hbefore onew))
  ))
  (ensures (Class?.disjoint c oold onew))

unfold
let live_preserved_preserved_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty)
: Tot (Type u#(max a b))
= (hbefore: heap) ->
  (hafter: heap) ->
  (o: ty) ->
  Lemma
  (requires (
    Class?.live c hbefore o ==> Class?.preserved c o hbefore hafter
  ))
  (ensures (Class?.preserved c o hbefore hafter))

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

let includes_ancestors_t_post
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
  (o1: ty)
  (o2: ty {Class?.includes c o1 o2 } )
  (i2: nat {i2 < Class?.ancestor_count c o2 } )
: Tot Type0
= exists (i1: nat { i1 < Class?.ancestor_count c o1 } ) .
  includes_ancestors_t_prop c o1 o2 i2 i1

let includes_ancestors_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
: Tot (Type u#b)
= (o1: ty) ->
  (o2: ty {Class?.includes c o1 o2 } ) ->
  (i2: nat {i2 < Class?.ancestor_count c o2 } ) ->
  Lemma
  (includes_ancestors_t_post c o1 o2 i2)

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

let final_equal_or_disjoint_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
: Tot (Type u#b)
= (x: ty) ->
  (y: ty) ->
  Lemma
  (requires (level == 0 /\ Class?.final c x))
  (ensures (y == x \/ Class?.disjoint c x y))

let ancestor_not_final_t
  (#heap: Type u#a)
  (#level: nat) (#ty: Type u#b) (c: class' heap level ty )
: Tot (Type u#b)
= (x: ty) ->
  (i: nat { i < Class?.ancestor_count c x } ) ->
  Lemma
  (requires (Class?.ancestor_class_levels c x i == 0))
  (ensures (Class?.ancestor_class_levels c x i == 0 /\ ~ (Class?.final (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i))))

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
  level_0_live_dead_disjoint: level_0_live_dead_disjoint_t c;
  live_preserved_preserved: live_preserved_preserved_t c;
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
  disjoint_includes: disjoint_includes_t c;
  final_equal_or_disjoint: final_equal_or_disjoint_t c;
  ancestor_not_final: ancestor_not_final_t c;
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
  [smt_pat (class_invariant root_class (Class?.ancestor_classes c x i))]
= ()

(** FIXME: statements are duplicated here due to the SMT patterns *)

val bind_squash:
  #a:Type -> #b:Type0 -> squash a -> $f:(a -> Lemma b) ->
  Lemma b
let bind_squash #a #b s f = Squash.bind_squash #a #b s (fun x -> f x)

abstract
let preserved_refl
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty)
  (x: ty)
  (h : heap)
: Lemma
  (requires True)
  (ensures (Class?.preserved c x h h))
  [smt_pat (Class?.preserved c x h h)]
= Squash.bind_squash #_ #(Class?.preserved c x h h) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.preserved_refl x h)

abstract
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
  [smt_pat (Class?.preserved c x h1 h2); smt_pat (Class?.preserved c x h2 h3)]
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

abstract
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

abstract
let object_disjoint_sym
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty) 
  (x1: ty)
  (x2: ty)
: Lemma
  (requires (Class?.disjoint c x1 x2))
  (ensures (Class?.disjoint c x2 x1))
  [smt_pat (Class?.disjoint c x2 x1)]
= Squash.bind_squash #_ #(Class?.disjoint c x2 x1) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.disjoint_sym x1 x2)

abstract
let level_0_class_eq_root
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#ty: Type u#b) (c: class root_class 0 ty)
: Lemma
  (ensures (ty == root_type /\ c == root_class))
= Squash.bind_squash #_ #(0 == 0 ==> ty == root_type /\ c == root_class) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.level_0_class_eq_root)

abstract
let level_0_live_dead_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b) (root_class: class' heap 0 root_type { class_invariant root_class root_class } )
  (oold: root_type)
  (onew: root_type)
  (hbefore: heap)
: Lemma
  (requires (
    Class?.live root_class hbefore oold /\
    (~ (Class?.contains root_class hbefore onew))
  ))
  (ensures (Class?.disjoint root_class oold onew))
  [smt_pat (Class?.live root_class hbefore oold); smt_pat (~ (Class?.contains root_class hbefore onew)); ]
= Squash.bind_squash #_ #(Class?.disjoint root_class oold onew) (Squash.join_squash ()) (fun (i: class_invariant_body root_class root_class) -> i.level_0_live_dead_disjoint oold onew hbefore)

abstract
let live_preserved_preserved
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty) 
  (hbefore: heap)
  (hafter: heap)
  (o: ty)
: Lemma
  (requires (
    Class?.live c hbefore o ==> Class?.preserved c o hbefore hafter
  ))
  (ensures (Class?.preserved c o hbefore hafter))
= Squash.bind_squash #_ #(Class?.preserved c o hbefore hafter) (Squash.join_squash ()) (fun (i: class_invariant_body root_class c) -> i.live_preserved_preserved hbefore hafter o)

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
(*   [smt_pat (Class?.preserved c o hbefore hafter); smt_pat (Class?.live c hbefore o)] *)
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
(*   [smt_pat (Class?.preserved c o hbefore hafter); smt_pat (Class?.contains c hbefore o)] *)
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
(*   [smt_pat (Class?.live c h o)] *)
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

abstract
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
  [smt_pat (Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i))]
= Squash.bind_squash #_ #(Class?.live (Class?.ancestor_classes c o i) h (ancestor_objects c o i)) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.live_ancestors h o i)

abstract
let object_includes_refl
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty )
  (o: ty)
: Lemma
  (ensures (Class?.includes c o o))
= Squash.bind_squash #_ #(Class?.includes c o o) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.includes_refl o)

abstract
let object_includes_trans
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type) (c: class root_class level ty )
  (o1 o2 o3: ty)
: Lemma
  (requires (Class?.includes c o1 o2 /\ Class?.includes c o2 o3))
  (ensures (Class?.includes c o1 o3))
= Squash.bind_squash #_ #(Class?.includes c o1 o3) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.includes_trans o1 o2 o3)

abstract
let object_includes_ancestors
  (#heap: Type u#a)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty )
  (o1: ty)
  (o2: ty {Class?.includes c o1 o2 } )
  (i2: nat {i2 < Class?.ancestor_count c o2 } )
: Lemma
  (exists (i1 : nat {i1 < Class?.ancestor_count c o1} ) .
    includes_ancestors_t_prop c o1 o2 i2 i1
  )
= assert_norm (includes_ancestors_t_post c o1 o2 i2 == (
         exists (i1 : nat {i1 < Class?.ancestor_count c o1} ) .
         includes_ancestors_t_prop c o1 o2 i2 i1
  ));
  Squash.bind_squash #_ #(includes_ancestors_t_post c o1 o2 i2)
    (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> (j.includes_ancestors o1 o2 i2))

abstract
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

abstract
let final_equal_or_disjoint
  (#heap: Type u#a)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty )
  (x: ty)
  (y: ty)
: Lemma
  (requires (level == 0 /\ Class?.final c x))
  (ensures (y == x \/ Class?.disjoint c x y))
= Squash.bind_squash #_ #(y == x \/ Class?.disjoint c x y) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.final_equal_or_disjoint x y)

abstract
let ancestor_not_final
  (#heap: Type u#a)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (#level: nat) (#ty: Type u#b) (c: class root_class level ty )
  (x: ty)
  (i: nat { i < Class?.ancestor_count c x } )
: Lemma
  (requires (Class?.ancestor_class_levels c x i == 0))
  (ensures (Class?.ancestor_class_levels c x i == 0 /\ ~ (Class?.final (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i))))
= Squash.bind_squash #_ #(~ (Class?.final (Class?.ancestor_classes c x i) (Class?.ancestor_objects c x i))) (Squash.join_squash ()) (fun (j: class_invariant_body root_class c) -> j.ancestor_not_final x i)

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
  [smt_pat (loc_of_object class1 obj1 == loc_of_object class2 obj2)]
= ()

abstract
let loc_of_object_inj_forall
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (root_class: class' heap 0 root_type)
: Lemma
  (requires True)
  (ensures (forall
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
  ))
  [smt_pat (loc_of_object #_ #_ #root_class)]
= ()

private
let loc_of_object_eq
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (root_class: class' heap 0 root_type)
: Lemma
  (requires True)
  (ensures (forall
    (l: loc root_class)
    .
    l == loc_of_object (Location?.class l) (Location?.obj l)
  ))
  [smt_pat (loc_of_object #_ #_ #root_class)]
= ()

private
noeq type loc_disjoint_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
:
  loc root_class ->
  loc root_class ->
  Tot Type
=
| DisjointObjects:
  (level: nat) ->
  (t: (Type u#b)) ->
  (c: class root_class level t) ->
  (o1: t) ->
  (o2: t) ->
  squash (Class?.disjoint c (hetero_id o1) (hetero_id o2)) ->
  loc_disjoint_t (loc_of_object c o1) (loc_of_object c o2)
| DisjointAncestors:
  (level: (bool -> Tot nat)) ->
  (t: (bool -> Tot (Type u#b))) ->
  (c: ((b: bool) -> Tot (class root_class (level b) (t b)))) ->
  (o: ((b: bool) -> Tot (t b)) { Class?.ancestor_count (c true) (o true) > 0 } ) ->
  (h: (
    (i: nat { i < Class?.ancestor_count (c true) (hetero_id (o true)) } ) ->
    Tot (loc_disjoint_t (loc_of_object (Class?.ancestor_classes (c true) (hetero_id (o true)) i) (Class?.ancestor_objects (c true) (hetero_id (o true)) i)) (loc_of_object (c false) (o false)))
  )) ->
  (b: bool) ->
  loc_disjoint_t (loc_of_object (c b) (o b)) (loc_of_object (c (not b)) (o (not b)))

abstract
let loc_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
: Tot Type0
= squash (loc_disjoint_t l1 l2)

private
let rec loc_disjoint_t_sym
  (#heap: Type)
  (#root_type: Type) (#root_class: class' heap 0 root_type)
  (l1 l2: loc root_class)
  (d: loc_disjoint_t l1 l2)
: Pure (loc_disjoint_t l2 l1)
  (requires True)
  (ensures (fun _ -> True))
  (decreases d)
= match d with
  | DisjointObjects level t c o1 o2 h ->
    let (c: class root_class level t) = c in
    DisjointObjects level t c o2 o1 (object_disjoint_sym c o1 o2)
  | DisjointAncestors level t c o h b ->
    DisjointAncestors level t c o h (not b)

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
  [smt_pat (loc_disjoint l1 l2)]
= Squash.map_squash (Squash.join_squash ()) (fun (d: loc_disjoint_t l1 l2) -> loc_disjoint_t_sym l1 l2 d)

abstract
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
  [smt_pat (Class?.disjoint c o1 o2)]
= Squash.return_squash (DisjointObjects _ _ c o1 o2 ())

abstract
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
  : Tot (squash (loc_disjoint_t (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2))
  = Squash.join_squash (h i)
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c1 o1 } ) -> Tot (loc_disjoint_t (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) l2))) ->
    let d : loc_disjoint_t (loc_of_object c1 o1) l2 = DisjointAncestors (fun b -> if b then level1 else level2) (fun b -> if b then t1 else t2) (fun b -> if b then c1 else c2) (fun b -> if b then o1 else o2) h true in
    Squash.return_squash d
  )

abstract
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
  : Tot (squash (loc_disjoint_t (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)) l1))
  = let _ : squash (loc_disjoint_t l1 (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i))) = Squash.join_squash (h i) in
    Squash.join_squash (loc_disjoint_sym (loc_of_object c1 o1) (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)))
  in
  let g = SquashProperties.squash_arrow f in
  Squash.bind_squash g (fun (h: ((i: nat { i < Class?.ancestor_count c2 o2 } ) -> Tot (loc_disjoint_t (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)) l1))) ->
    let d : loc_disjoint_t l1 (loc_of_object c2 o2) = DisjointAncestors (fun b -> if b then level2 else level1) (fun b -> if b then t2 else t1) (fun b -> if b then c2 else c1) (fun b -> if b then o2 else o1) h false in
    Squash.return_squash d
  )

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
  [smt_pat (modifies s h h')]
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
  [smt_pat (modifies s h h)]
= ()

let modifies_trans
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s: locset root_class )
  (h1 h2 h3: heap)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
//  [smt_pat (modifies s h1 h2); smt_pat (modifies s h2 h3)]
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
  [smt_pat (modifies s1 h h'); smt_pat (TSet.subset s1 s2)]
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

let rec dead
  (#heap: Type u#a)
  (#level: nat)
  (#ty: Type u#b)
  (c: class' heap level ty)
  (h: heap)
  (o: ty)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases level)
= (~ ( Class?.contains c h o )) /\ (
    forall (i: nat {i < Class?.ancestor_count c o}) . dead (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)
  )

let dead_ancestor
  (#heap: Type u#a)
  (#level: nat)
  (#ty: Type u#b)
  (c: class' heap level ty)
  (o: ty)
  (h: heap)
  (i: nat {i < Class?.ancestor_count c o})
: Lemma
  (requires (dead c h o))
  (ensures (dead (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i)))
  [smt_pat (dead (Class?.ancestor_classes c o i) h (Class?.ancestor_objects c o i))]
= ()

abstract
let rec live_dead_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (#levelold: nat) (#tyold: Type u#b)
  (#levelnew: nat) (#tynew: Type u#b)
  (cold: class root_class levelold tyold)
  (cnew: class root_class levelnew tynew)
  (oold: tyold)
  (onew: tynew)
  (hbefore: heap)
:  Lemma
  (requires (
    Class?.live cold hbefore oold /\
    dead cnew hbefore onew
  ))
  (ensures (loc_disjoint (loc_of_object cold oold) (loc_of_object cnew onew)))
  (decreases (levelold + levelnew))
  [smt_pat (Class?.live cold hbefore oold); smt_pat (dead cnew onew hbefore)]
= if
    levelold = 0
  then
    let _ : squash (tyold == root_type /\ cold == root_class) = level_0_class_eq_root #heap #root_type #root_class #tyold cold in
    if
      levelnew = 0
    then
      let _ : squash (tynew == root_type /\ cnew == root_class) = level_0_class_eq_root #heap #root_type #root_class #tynew cnew in
      level_0_live_dead_disjoint cold oold onew hbefore
    else
      let f
	(i: nat { i < Class?.ancestor_count cnew onew } )
      : Lemma
	(loc_disjoint (loc_of_object cold oold) (loc_of_object (Class?.ancestor_classes cnew onew i) (Class?.ancestor_objects cnew onew i)))
      = let cnew' = Class?.ancestor_classes cnew onew i in
	let onew' = Class?.ancestor_objects cnew onew i in
	live_dead_disjoint cold cnew' oold onew' hbefore
      in
      loc_disjoint_ancestors_right (loc_of_object cold oold) cnew onew f
  else
    let f
      (i: nat { i < Class?.ancestor_count cold oold } )
    : Lemma
      (loc_disjoint (loc_of_object (Class?.ancestor_classes cold oold i) (Class?.ancestor_objects cold oold i)) (loc_of_object cnew onew))
    = let cold' = Class?.ancestor_classes cold oold i in
      let oold' = Class?.ancestor_objects cold oold i in
      live_dead_disjoint cold' cnew oold' onew hbefore
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

abstract
let locset_disjoint_sym
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls1 ls2: locset root_class)
: Lemma
  (requires (locset_disjoint ls1 ls2))
  (ensures (locset_disjoint ls2 ls1))
  [smt_pat (locset_disjoint ls1 ls2)]
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
  [smt_pat (locset_disjoint (TSet.singleton l1) (TSet.singleton l2))]
= ()

let locset_disjoint_union
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls ls1 ls2: locset root_class)
: Lemma
  (requires (locset_disjoint ls ls1 /\ locset_disjoint ls ls2))
  (ensures (locset_disjoint ls (TSet.union ls1 ls2)))
  [smt_pat (locset_disjoint ls (TSet.union ls1 ls2))]
= ()

let locset_live
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (h: heap)
  (ls: locset root_class)
: Tot Type0
= forall (level: nat) (ty: Type u#b) (c: class root_class level ty) (o: ty) .
  TSet.mem (loc_of_object c o) ls ==>
  Class?.live c h o

let locset_dead
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (h: heap)
  (ls: locset root_class)
: Tot Type0
= forall (level: nat) (ty: Type u#b) (c: class root_class level ty) (o: ty) .
  TSet.mem (loc_of_object c o) ls ==>
  dead c h o

abstract
let locset_live_locset_dead_locset_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (lsold lsnew: locset root_class)
  (hbefore: heap)
: Lemma
  (requires (
    locset_live hbefore lsold /\
    locset_dead hbefore lsnew
  ))
  (ensures (locset_disjoint lsold lsnew))
= let f
    (lold: loc root_class { TSet.mem lold lsold } )
    (lnew: loc root_class { TSet.mem lnew lsnew } )
  : Lemma
    (loc_disjoint lold lnew)
  = live_dead_disjoint (Location?.class lold) (Location?.class lnew) (Location?.obj lold) (Location?.obj lnew) hbefore
  in
  Classical.forall_intro_2 f

let modifies_locset_dead
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (lsold lsnew: locset root_class)
  (hbefore: heap)
  (hafter: heap)
: Lemma
  (requires (modifies (TSet.union lsold lsnew) hbefore hafter /\ locset_dead hbefore lsnew))
  (ensures (modifies lsold hbefore hafter))
= let f'
    (ty: Type u#b)
    (l: nat)
    (c: class root_class l ty )
    (o: ty)
    (g: (
      (o' : loc root_class { TSet.mem o' lsold } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) o')
    ))
  : Lemma
    (requires (Class?.live c hbefore o))
    (ensures (Class?.preserved c o hbefore hafter))
  = let g'
      (o' : loc root_class { TSet.mem o' (TSet.union lsold lsnew) } )
    : Lemma
      (loc_disjoint (loc_of_object c o) o')
    = Classical.or_elim
        #(TSet.mem o' lsold)
        #(TSet.mem o' lsnew)
        #(fun _ -> loc_disjoint (loc_of_object c o) o')
        (fun _ -> g o')
        (fun _ ->
          let (Location _ _ cnew onew) = o' in
          live_dead_disjoint c cnew o onew hbefore
        )
    in
    modifies_elim (TSet.union lsold lsnew) hbefore hafter () c o g'
  in
  modifies_intro lsold hbefore hafter (fun ty l c o g ->
    Classical.move_requires (f' ty l c o) g;
    live_preserved_preserved c hbefore hafter o
  )

noeq
private
type locset_includes_loc_t
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
: (l: loc root_class) ->
  Type u#(1 + max a b)
=
| LocsetIncludesObject:
    (level: nat) ->
    (ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o1: ty { TSet.mem (loc_of_object c o1) ls } ) ->
    (o2: ty { Class?.includes c o1 o2 } ) ->
    locset_includes_loc_t ls (loc_of_object c o2)
| LocsetIncludesAncestors:
    (level: nat) ->
    (ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o: ty { Class?.ancestor_count c o > 0 } ) ->
    (f: (
      (i: nat {i < Class?.ancestor_count c o } ) ->
      Tot (locset_includes_loc_t ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
    )) ->
    locset_includes_loc_t ls (loc_of_object c o)

abstract
let locset_includes_loc
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class)
: Tot Type0
= squash (locset_includes_loc_t ls l)

abstract
let mem_locset_includes_loc
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class)
: Lemma
  (requires (TSet.mem l ls))
  (ensures (locset_includes_loc ls l))
  [smt_pat (TSet.mem l ls)]
= let (Location _ _ c o) = l in
  object_includes_refl c o;
  let k : locset_includes_loc_t ls l = LocsetIncludesObject _ _ c o o in
  Squash.return_squash k

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
  [smt_pat_or [ [smt_pat (TSet.subset ls_small ls_big)] ; [ smt_pat (locset_includes ls_big ls_small) ] ] ]
= ()

let locset_includes_union
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls_big ls_small_1 ls_small_2: locset root_class)
: Lemma
  (requires (locset_includes ls_big ls_small_1 /\ locset_includes ls_big ls_small_2))
  (ensures (locset_includes ls_big (TSet.union ls_small_1 ls_small_2)))
  [smt_pat (locset_includes ls_big (TSet.union ls_small_1 ls_small_2))]
= ()

abstract
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
  [smt_pat (TSet.mem (loc_of_object c o1)); smt_pat (Class?.includes c o1 o2)]
= let k : locset_includes_loc_t ls (loc_of_object c o2) = LocsetIncludesObject _ _ c o1 o2 in
  Squash.return_squash k

abstract
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
  [smt_pat_or [ [ smt_pat (locset_includes (locset_of_object c o1) (locset_of_object c o2))] ; [ smt_pat (Class?.includes c o1 o2) ] ] ]
= locset_includes_loc_object (locset_of_object c o1) c o1 o2

abstract
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
  : Tot (squash (locset_includes_loc_t ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i))))
  = Squash.join_squash (f i)
  in
  let g = SquashProperties.squash_arrow g in
  Squash.bind_squash g (fun (h: ((i: nat {i < Class?.ancestor_count c o } ) -> Tot (locset_includes_loc_t ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i))))) -> Squash.return_squash (LocsetIncludesAncestors _ _ c o h))

private
let rec locset_includes_loc_t_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls: locset root_class)
  (l: loc root_class)
  (o: Location?.ty l { Class?.includes (Location?.class l) (Location?.obj l) o } )
  (d: locset_includes_loc_t ls l)
: Pure (squash (locset_includes_loc_t ls (Location _ _ (Location?.class l) o)))
  (requires True)
  (ensures (fun _ -> True))
  (decreases d)
= match d with
  | LocsetIncludesObject level ty c o1 o2 ->
    object_includes_trans c o1 o2 o;
    Squash.return_squash (LocsetIncludesObject level ty c o1 o)
  | LocsetIncludesAncestors level ty c2 o2 f ->
    let (o3: ty { Class?.includes c2 o2 o3 } ) = o in
    let _ : squash (Class?.ancestor_count c2 o3 > 0) =
      if Class?.level c2 = 0
      then
        let (n: nat) = Class?.ancestor_class_levels c2 o2 0 in
        let _ = assert (n < 0) in
	false_elim ()
      else ()
    in
    let f1
      (i3: nat {i3 < Class?.ancestor_count c2 o3 } )
    : Lemma (squash (locset_includes_loc_t ls (Location _ _ (Class?.ancestor_classes c2 o3 i3) (Class?.ancestor_objects c2 o3 i3))))
    = let f2
        (i2: nat {i2 < Class?.ancestor_count c2 o2 } )
      : Lemma
        (requires (includes_ancestors_t_prop c2 o2 o3 i3 i2))
        (ensures (squash (locset_includes_loc_t ls (Location _ _ (Class?.ancestor_classes c2 o3 i3) (Class?.ancestor_objects c2 o3 i3)))))
      = let _ : squash (f i2 << d) = WellFounded.axiom1_dep f i2 in
        locset_includes_loc_t_includes ls (Location _ _ (Class?.ancestor_classes c2 o2 i2) (Class?.ancestor_objects c2 o2 i2)) (Class?.ancestor_objects c2 o3 i3) (f i2)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires f2);
      object_includes_ancestors c2 o2 o3 i3;
      ()
    in
    let f1'
      (i3: nat {i3 < Class?.ancestor_count c2 o3 } )
    : Tot (squash (locset_includes_loc_t ls (Location _ _ (Class?.ancestor_classes c2 o3 i3) (Class?.ancestor_objects c2 o3 i3))))
    = Squash.join_squash (f1 i3)
    in
    let f2 = SquashProperties.squash_arrow f1' in
    Squash.map_squash f2 (fun
      (f3: (
        (i3: nat {i3 < Class?.ancestor_count c2 o3 } ) ->
        Tot (locset_includes_loc_t ls (Location _ _ (Class?.ancestor_classes c2 o3 i3) (Class?.ancestor_objects c2 o3 i3)))
      )) ->
      LocsetIncludesAncestors level ty c2 o3 f3
    )

private
let rec locset_includes_loc_t_trans
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls0: locset root_class)
  (ls: locset root_class { locset_includes ls0 ls } )
  (l: loc root_class)
  (d: locset_includes_loc_t ls l)
: Pure (squash (locset_includes_loc_t ls0 l))
  (requires True)
  (ensures (fun _ -> True))
  (decreases d)
= match d with
  | LocsetIncludesObject level ty c o1 o2 ->
    assert (locset_includes_loc ls0 (loc_of_object c o1));
    let h : squash (locset_includes_loc_t ls0 (loc_of_object c o1)) = Squash.join_squash () in
    Squash.bind_squash #(locset_includes_loc_t ls0 (loc_of_object c o1)) #(locset_includes_loc_t ls0 l) h (fun (d' : locset_includes_loc_t ls0 (loc_of_object c o1)) ->
      locset_includes_loc_t_includes ls0 (loc_of_object c o1) o2 d'
    )
  | LocsetIncludesAncestors level ty c o f ->
    let g
      (i: nat {i < Class?.ancestor_count c o } )
    : Tot (squash (locset_includes_loc_t ls0 (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i))))
    = WellFounded.axiom1_dep f i;
      locset_includes_loc_t_trans ls0 ls (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)) (f i);
      Squash.join_squash ()
    in
    locset_includes_loc_ancestors ls0 c o g;
    Squash.join_squash ()

abstract
let locset_includes_loc_trans
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls0: locset root_class)
  (ls: locset root_class { locset_includes ls0 ls } )
  (l: loc root_class { locset_includes_loc ls l } )
: Lemma
  (locset_includes_loc ls0 l)
= Squash.bind_squash #(locset_includes_loc_t ls l) #(locset_includes_loc_t ls0 l) (Squash.join_squash ()) (locset_includes_loc_t_trans ls0 ls l)

abstract
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
  [smt_pat (locset_includes ls0 ls1); smt_pat (locset_includes ls1 ls2)]
= let f
    (l: loc root_class { TSet.mem l ls2 } )
  : Lemma
    (locset_includes_loc ls0 l)
  = locset_includes_loc_trans ls0 ls1 l
  in
  Classical.forall_intro f

(* Same thing, to provide the witness *)

abstract
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
  [smt_pat (locset_includes ls0 ls0)]
= ()
*)

// #reset-options "--z3rlimit 32"

private
let rec loc_disjoint_t_object_includes
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1: loc root_class)
  (l2: loc root_class)
  (d: loc_disjoint_t l1 l2)
: Lemma
  (ensures (forall
    (o1: _ { Class?.includes (Location?.class l1) (Location?.obj l1) o1 } )
    (o2: _ { Class?.includes (Location?.class l2) (Location?.obj l2) o2 } )
  .
    (loc_disjoint (loc_of_object (Location?.class l1) o1) (loc_of_object (Location?.class l2) o2))
  ))
  (decreases d)
= match d with
  | DisjointObjects level t c o1 o2 _ ->
    Classical.forall_intro_2 (fun (o1' : t) -> Classical.move_requires (object_disjoint_includes c o1 o2 o1'))
  | DisjointAncestors level t c o h b ->
    let f
      (o_t: t true { Class?.includes (c true) (o true) o_t } )
      (o_f: t false { Class?.includes (c false) (o false) o_f })
    : Lemma
      (loc_disjoint (loc_of_object (c true) o_t) (loc_of_object (c false) o_f))
    = let g1
	(i: nat { i < Class?.ancestor_count (c true) (o true) } )
      : Lemma (forall
	  (o1: Class?.ancestor_types (c true) (o true) i { Class?.includes (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i) o1})
	.
	  loc_disjoint (loc_of_object (Class?.ancestor_classes (c true) (o true) i) o1) (loc_of_object (c false) o_f)
        )
      = let _ : squash (h i << d) = WellFounded.axiom1_dep h i in
	let l1 : loc root_class = loc_of_object (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i) in
        let l2 : loc root_class = (loc_of_object (c false) (o false)) in
        loc_disjoint_t_object_includes l1 l2 (h i)
      in
      Classical.forall_intro g1;
      let _ : squash (Class?.ancestor_count (c true) o_t > 0) =
	if level true = 0
	then assert (Class?.ancestor_class_levels (c true) (o true) 0 < 0)
	else ()
      in
      let g
	(i_t: nat { i_t < Class?.ancestor_count (c true) (o_t) } )
      : Lemma
	(loc_disjoint (loc_of_object (Class?.ancestor_classes (c true) (o_t) i_t) (Class?.ancestor_objects (c true) (o_t) i_t)) (loc_of_object (c false) o_f))
      = object_includes_ancestors (c true) (o true) o_t i_t
      in
      loc_disjoint_ancestors_left (c true) o_t (loc_of_object (c false) o_f) g
    in
    let g
      (o1: t b { Class?.includes (c b) (o b) o1 })
      (o2: t (not b) { Class?.includes (c (not b)) (o (not b)) o2 } )
    : Lemma
      (loc_disjoint (loc_of_object (c b) o1) (loc_of_object (c (not b)) o2))
    = if b
      then f o1 o2
      else f o2 o1
    in
    Classical.forall_intro_2 g

private
let rec loc_disjoint_locset_includes_loc_t
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
  (l2: loc root_class)
  (d:  locset_includes_loc_t ls l2)
: Lemma
  (requires True)
  (ensures (loc_disjoint l l2))
  (decreases d)
= match d with
  | LocsetIncludesObject level ty c o1 o2 ->
      h (loc_of_object c o1);
      object_includes_refl (Location?.class l) (Location?.obj l);
      bind_squash (Squash.join_squash ()) (loc_disjoint_t_object_includes l (loc_of_object c o1))
  | LocsetIncludesAncestors level ty c o f ->
    let g
      (i: nat { i < Class?.ancestor_count c o } )
    : Lemma
      (loc_disjoint l (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)))
    = WellFounded.axiom1_dep f i;
      loc_disjoint_locset_includes_loc_t l ls h (loc_of_object (Class?.ancestor_classes c o i) (Class?.ancestor_objects c o i)) (f i)
    in
    loc_disjoint_ancestors_right l c o g

abstract
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
  [smt_pat_or [
    [smt_pat (locset_disjoint ls1 ls2); smt_pat (locset_includes ls2 ls2')];
    [smt_pat (locset_disjoint ls1 ls2'); smt_pat (locset_includes ls2 ls2')]
  ]]  
= let f
    (l1: loc root_class { TSet.mem l1 ls1 } )
  : Lemma
    (forall (l2' : loc root_class { TSet.mem l2' ls2' } ) . loc_disjoint l1 l2' )
  = let g
      (l2' : loc root_class { TSet.mem l2' ls2' } )
    : Lemma
      (loc_disjoint l1 l2')
    = bind_squash (Squash.join_squash ()) (loc_disjoint_locset_includes_loc_t l1 ls2 (fun _ -> ()) l2')
    in
    Classical.forall_intro g
  in
  Classical.forall_intro f

abstract
let modifies_locset_includes
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s1 s2: locset root_class)
  (h h': heap)
: Lemma
  (requires (modifies s2 h h' /\ locset_includes s1 s2))
  (ensures (modifies s1 h h'))
  [ smt_pat_or [  [smt_pat (modifies s2 h h'); smt_pat (locset_includes s1 s2)] ;   [smt_pat (modifies s2 h h'); smt_pat (modifies s1 h h')] ] ]
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
    = bind_squash (Squash.join_squash ()) (loc_disjoint_locset_includes_loc_t (loc_of_object c o) s1 g o')
    in
    Classical.forall_intro k
  in
  modifies_intro s1 h h' f

abstract
let modifies_trans_gen
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: class' heap 0 root_type)
  (s12 s23: locset root_class )
  (h1 h2 h3: heap)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (TSet.union s12 s23) h1 h3))
  [smt_pat (modifies s12 h1 h2); smt_pat (modifies s23 h2 h3)]
= assert (locset_includes (TSet.union s12 s23) s12);
  assert (locset_includes (TSet.union s12 s23) s23);
  modifies_trans (TSet.union s12 s23) h1 h2 h3
  
(* How to refine ancestors with
their immediate child if we know that all siblings of the child (in the
same class) are preserved. *)

private
let rec modifies_loc_refines'
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (l1_: loc root_class)
  (h h': heap)
  (f0: (
    (#level: nat) ->
    (#ty: Type u#b) ->
    (c: class root_class level ty) ->
    (o: ty) ->
    (f: (
      (i: nat { i < Class?.ancestor_count (Location?.class l1_) (Location?.obj l1_) } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) (loc_of_object (Class?.ancestor_classes (Location?.class l1_) (Location?.obj l1_) i) (Class?.ancestor_objects (Location?.class l1_) (Location?.obj l1_) i)))
    )) ->
    Lemma
    (Class?.preserved c o h h')
  ))
  (f1: (
    (o1': Location?.ty l1_) ->
    squash (Class?.disjoint (Location?.class l1_) (Location?.obj l1_) o1') ->
    Lemma
    (Class?.preserved (Location?.class l1_) o1' h h')
  ))
  (l_: loc root_class)
  (d: loc_disjoint_t l_ l1_)
: Lemma
  (ensures (Class?.preserved (Location?.class l_) (Location?.obj l_) h h'))
  (decreases d)
= match d with
  | DisjointObjects level t c o1 o2 _ ->
    f1 o1 ()
  | DisjointAncestors level t c o k b ->
    if b
    then
      let phi
	(i: nat { i < Class?.ancestor_count (c true) (o true) } )
      : Lemma
	(Class?.preserved (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i) h h')
      = WellFounded.axiom1_dep k i;
	modifies_loc_refines' l1_ h h' f0 f1 (loc_of_object (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i)) (k i)
      in
      preserved_ancestors_preserved (c true) (o true) h h' phi
    else
      let f
	(i: nat { i < Class?.ancestor_count (c true) (o true) } )
      : Lemma
        (loc_disjoint (loc_of_object (c false) (o false)) (loc_of_object (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i)))
      = Squash.return_squash (Squash.return_squash (k i));
	loc_disjoint_sym (loc_of_object (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i)) (loc_of_object (c false) (o false)) // TODO: WHY WHY WHY is this necessary? WHY does the pattern NOT trigger here?
      in
      f0 (c false) (o false) f

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
= bind_squash (Squash.join_squash f) (modifies_loc_refines' (loc_of_object c1_ o1_) h h' f0 f1 (loc_of_object c_ o_))

abstract
let level_0_no_ancestors
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (#level: nat)
  (#t: Type u#b)
  (c: class root_class level t)
  (o: t)
: Lemma
  (requires (level == 0))
  (ensures (Class?.ancestor_count c o == 0))
= if Class?.ancestor_count c o = 0
  then ()
  else let j : nat = Class?.ancestor_class_levels c o 0 in
       assert False

private
let loc_disjoint_t_level_zero
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1 #level2: nat)
  (#t1 #t2: Type u#b)
  (c1: class root_class level1 t1)
  (c2: class root_class level2 t2)
  (o1: t1)
  (o2: t2)
  (h: loc_disjoint_t (loc_of_object c1 o1) (loc_of_object c2 o2))
: Tot (squash (level2 == 0 ==> (forall (i: nat { i < Class?.ancestor_count c1 o1 } ) . squash (loc_disjoint_t (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) (loc_of_object c2 o2)))))
  (decreases h)
= match h with
  | DisjointObjects level t c o1 o2 k ->
    let c: class root_class level t = c in
    Classical.move_requires (level_0_no_ancestors c) o2
  | DisjointAncestors level t c o h b ->
    if b
    then
      let f
        (i: nat { i < Class?.ancestor_count (c true) (o true) } ) 
      : Lemma (squash (loc_disjoint_t (loc_of_object (Class?.ancestor_classes (c true) (o true) i) (Class?.ancestor_objects (c true) (o true) i)) (loc_of_object (c false) (o false))))
      = Squash.return_squash (h i)
      in
      Classical.forall_intro f
    else
      let ct: class root_class (level true) (t true) = c true in
      Classical.move_requires (level_0_no_ancestors ct) (o true)

abstract
let loc_disjoint_level_zero
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1 #level2: nat)
  (#t1 #t2: Type u#b)
  (c1: class root_class level1 t1)
  (c2: class root_class level2 t2)
  (o1: t1)
  (o2: t2)
: Lemma
  (requires (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2)))
  (ensures (level2 == 0 ==> (forall (i: nat { i < Class?.ancestor_count c1 o1 } ) . loc_disjoint (loc_of_object (Class?.ancestor_classes c1 o1 i) (Class?.ancestor_objects c1 o1 i)) (loc_of_object c2 o2))))
= Squash.bind_squash (Squash.join_squash ()) (fun (h: loc_disjoint_t (loc_of_object c1 o1) (loc_of_object c2 o2)) -> loc_disjoint_t_level_zero c1 c2 o1 o2 h)

private
let loc_disjoint_t_level_zero_same
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1 #level2: nat)
  (#t1 #t2: Type u#b)
  (c1: class root_class level1 t1)
  (c2: class root_class level2 t2)
  (o1: t1)
  (o2: t2)
  (h: loc_disjoint_t (loc_of_object c1 o1) (loc_of_object c2 o2))
: Tot (squash ((level1 == 0 /\ level2 == 0) ==> (t1 == t2 /\ c1 == hetero_id c2 /\ Class?.disjoint c1 o1 o2)))
  (decreases h)
= match h with
  | DisjointObjects level t c o1 o2 k ->
    ()
  | DisjointAncestors level t c o h b ->
    let ct: class root_class (level true) (t true) = c true in
    Classical.move_requires (level_0_no_ancestors ct) (o true)

abstract
let loc_disjoint_level_zero_same
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1 #level2: nat)
  (#t1 #t2: Type u#b)
  (c1: class root_class level1 t1)
  (c2: class root_class level2 t2)
  (o1: t1)
  (o2: t2)
: Lemma
  (requires (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2)))
  (ensures ((level1 == 0 /\ level2 == 0) ==> (t1 == t2 /\ c1 == hetero_id c2 /\ Class?.disjoint c1 o1 o2)))
= Squash.bind_squash (Squash.join_squash ()) (fun (h: loc_disjoint_t (loc_of_object c1 o1) (loc_of_object c2 o2)) -> loc_disjoint_t_level_zero_same c1 c2 o1 o2 h)

abstract
let rec modifies_loc_refines_0
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
  (ensures (Class?.preserved c_ o_ h h'))
  (decreases level_)
= level_0_class_eq_root c1_;
  if level_ = 0
  then begin
    level_0_class_eq_root c_;
    loc_disjoint_level_zero_same c_ c1_ o_ o1_;
    f1 o_ ()
  end else begin
    loc_disjoint_level_zero c_ c1_ o_ o1_;
    let phi
      (i: nat { i < Class?.ancestor_count c_ o_ })
    : Lemma
      (Class?.preserved (Class?.ancestor_classes c_ o_ i) (Class?.ancestor_objects c_ o_ i) h h')
    = modifies_loc_refines_0 c1_ o1_ h h' f1 (Class?.ancestor_classes c_ o_ i) (Class?.ancestor_objects c_ o_ i) ()
    in
    preserved_ancestors_preserved c_ o_ h h' phi
  end

abstract
let rec final_disjoint
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1 #level2: nat)
  (#t1 #t2: Type u#b)
  (c1: class root_class level1 t1)
  (c2: class root_class level2 t2)
  (o1: t1)
  (o2: t2)
: Lemma
  (requires (level1 == 0 /\ Class?.final c1 o1 /\ level2 > 0))
  (ensures (loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2)))
  (decreases level2)
= level_0_class_eq_root c1;
  let f
    (i: nat { i < Class?.ancestor_count c2 o2 } )
  : Lemma
    (loc_disjoint (loc_of_object c1 o1) (loc_of_object (Class?.ancestor_classes c2 o2 i) (Class?.ancestor_objects c2 o2 i)))
  = if Class?.ancestor_class_levels c2 o2 i = 0
    then begin
      let c2_ : class root_class 0 (Class?.ancestor_types c2 o2 i) = Class?.ancestor_classes c2 o2 i in
      level_0_class_eq_root c2_;
      ancestor_not_final c2 o2 i;
      final_equal_or_disjoint c1 o1 (Class?.ancestor_objects c2 o2 i)
    end else
      final_disjoint c1 (Class?.ancestor_classes c2 o2 i) o1 (Class?.ancestor_objects c2 o2 i)
  in
  loc_disjoint_ancestors_right (loc_of_object c1 o1) c2 o2 f

abstract
let final_equal_or_disjoint_gen
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type )
  (#level1: nat)
  (#t1: Type u#b)
  (c1: class root_class level1 t1)
  (o1: t1)
  (l2: loc root_class)
: Lemma
  (requires (level1 == 0 /\ Class?.final c1 o1))
  (ensures (loc_of_object c1 o1 == l2 \/ loc_disjoint (loc_of_object c1 o1) l2))
= let (Location _ level2 c2 o2) = l2 in
  if level2 = 0
  then begin
    level_0_class_eq_root c1;
    level_0_class_eq_root c2;
    let _ : squash (loc_of_object c1 o1 == loc_of_object c2 o2 \/ loc_disjoint (loc_of_object c1 o1) (loc_of_object c2 o2)) =
      final_equal_or_disjoint c1 o1 o2
    in
    ()
  end else
    final_disjoint c1 c2 o1 o2

abstract
let modifies_final
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: class' heap 0 root_type)
  (ls_final ls: locset root_class)
  (h h': heap)
: Lemma
  (requires (
    modifies (TSet.union ls_final ls) h h' /\ (
    forall
      (level: nat)
      (t: Type u#b)
      (c: class root_class level t)
      (o: t)
    .
      TSet.mem (loc_of_object c o) ls_final ==> (
      level == 0 /\
      Class?.final c o /\
      Class?.preserved c o h h'
  ))))
  (ensures (modifies ls h h'))
= let f
    (ty: Type u#b)
    (l: nat)
    (c: class root_class l ty )
    (o: ty)
    (g: (
      (o' : loc root_class { TSet.mem o' ls } ) ->
      Lemma
      (loc_disjoint (loc_of_object c o) o')
    ))
  : Lemma
    (Class?.preserved c o h h')
  = Classical.excluded_middle (TSet.mem (loc_of_object c o) ls_final);
    Classical.or_elim
      #(TSet.mem (loc_of_object c o) ls_final)
      #(~ (TSet.mem (loc_of_object c o) ls_final))
      #(fun _ -> Class?.preserved c o h h')
      (fun _ -> ())
      (fun _ ->
	let g'
	  (o': loc root_class { TSet.mem o' (TSet.union ls_final ls) } )
	: Lemma
	  (loc_disjoint (loc_of_object c o) o')
	= Classical.or_elim
	    #(TSet.mem o' ls_final)
	    #(TSet.mem o' ls)
	    #(fun _ -> loc_disjoint (loc_of_object c o) o')
	    (fun _ ->
	      let (Location _ _ c' o') = o' in
	      final_equal_or_disjoint_gen c' o' (loc_of_object c o)
	    )
	    (fun _ -> g o')
	in
	modifies_elim (TSet.union ls_final ls) h h' () c o g'
      )
  in
  modifies_intro ls h h' f
