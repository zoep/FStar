module FStar.STNG
include FStar.ST
module HH = FStar.HyperHeap
module HS = FStar.HyperStackNG

(* Stack allocation *)

abstract
let salloc_post_modifies
  (#a:Type)
  (init:a)
  (m0: HS.mem)
  (s: HS.reference a{HS.is_stack_region s.HS.id})
  (m1: HS.mem)
: Lemma
  (requires (salloc_post init m0 s m1))
  (ensures (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) m0 m1 /\ Modifies.locset_dead m0 (HS.locset_of_reference s)))
= (* for Modifies.locset_dead: *)
  Modifies.loc_of_object_inj_forall HS.root_class;
  (* for Modifies.modifies: 
     1. first prove that s is modified *)
  (* TODO: this is the same proof as HyperStackNG.modifies_locset_of_reference_intro,
     except that HyperStack.contains does not hold;
     so it would be nice to try to weaken the hypotheses of that lemma accordingly *)
  Modifies.modifies_intro (HS.locset_of_reference s) m0 (HS.upd m0 s init) (fun ty l c o g ->
    Modifies.modifies_loc_refines_0 HS.class (HS.ObjectReference _ s) m0 (HS.upd m0 s init) (fun o' _ -> ()) c o (g (Modifies.loc_of_object HS.class (HS.ObjectReference _ s)))
  );
  (* 2. then remove it thanks to the fact that it was dead before *)
  Modifies.modifies_locset_dead TSet.empty (HS.locset_of_reference s) m0 m1

(* Same proof as HyperStackNG.fresh_frame_modifies, except that tip does not change *)

let new_region_modifies
  (r0:HH.rid { HS.is_eternal_region r0 } )
  (m0: HS.mem)
  (m1: HS.mem)
  (r1: HH.rid)
: Lemma
  (requires (
    r1 `HH.extends` r0 /\
    HH.fresh_region r1 m0.HS.h m1.HS.h /\
    m1.HS.h == Map.upd m0.HS.h r1 Heap.emp /\
    m1.HS.tip = m0.HS.tip
  ))
  (ensures (
    Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) m0 m1 
  ))
= let _ : squash (~ (HS.live_region m0 r1)) =
    if Map.contains m0.HS.h r1 then () else ()
  in
  let _ : squash (m1.HS.h == Map.upd m0.HS.h r1 Heap.emp) = () in
  let _ : squash (m1.HS.tip == m0.HS.tip) = () in
  let rec f'
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class HS.root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc HS.root_class { TSet.mem o' TSet.empty } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
    ()
  : Lemma
    (requires (Modifies.Class?.live c m0 o))
    (ensures (Modifies.Class?.preserved c o m0 m1))
    (decreases l)
  = if l = 0
    then begin
      Modifies.level_0_class_eq_root c
    end else begin
      let k
        (i: nat { i < Modifies.Class?.ancestor_count c o } )
      : Lemma
        (Modifies.Class?.preserved (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) m0 m1)
      = Modifies.live_ancestors c m0 o i;
        f' _ _ (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) (fun _ -> ()) ()
      in
      Modifies.preserved_ancestors_preserved c o m0 m1 k
    end
  in
  let f
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class HS.root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc HS.root_class { TSet.mem o' TSet.empty } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
  : Lemma
    (Modifies.Class?.preserved c o m0 m1)
  = Classical.move_requires (f' ty l c o g) ();
    Modifies.live_preserved_preserved c m0 m1 o    
  in
  let _ = Modifies.modifies_intro TSet.empty m0 m1 f in
  ()

let remove_reference_modifies
  (#a:Type)
  (r: HS.reference a{r.HS.mm})
  (m: HS.mem{r.HS.id `HS.is_in` m.HS.h})
: Lemma
  (ensures (
    Modifies.modifies (HS.locset_of_reference r) m (remove_reference r m) /\
    (~ ((remove_reference r m) `HS.contains` r)) /\
    Modifies.locset_dead (remove_reference r m) (HS.locset_of_reference r)
  ))
= (* for locset_dead: *)
  Modifies.loc_of_object_inj_forall HS.root_class;
  (* for modifies: *)
  let m0 = m in
  let m1 = remove_reference r m in
  let rec f'
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class HS.root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc HS.root_class { TSet.mem o' (HS.locset_of_reference r) } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
    ()
  : Lemma
    (requires (Modifies.Class?.live c m0 o))
    (ensures (Modifies.Class?.preserved c o m0 m1))
    (decreases l)
  = g (Modifies.loc_of_object HS.class (HS.ObjectReference _ r));
    if l = 0
    then begin
      Modifies.level_0_class_eq_root c;
      Modifies.loc_disjoint_level_zero_same c HS.class o (HS.ObjectReference _ r)
    end else begin
      Modifies.loc_disjoint_level_zero c HS.class o (HS.ObjectReference _ r);
      let k
        (i: nat { i < Modifies.Class?.ancestor_count c o } )
      : Lemma
        (Modifies.Class?.preserved (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) m0 m1)
      = Modifies.live_ancestors c m0 o i;
        f' _ _ (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) (fun _ -> ()) ()
      in
      Modifies.preserved_ancestors_preserved c o m0 m1 k
    end
  in
  let f
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class HS.root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc HS.root_class { TSet.mem o' (HS.locset_of_reference r) } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
  : Lemma
    (Modifies.Class?.preserved c o m0 m1)
  = Classical.move_requires (f' ty l c o g) ();
    Modifies.live_preserved_preserved c m0 m1 o    
  in
  let _ = Modifies.modifies_intro (HS.locset_of_reference r) m0 m1 f in
  ()

let new_region'
  (r0:HH.rid)
: ST HH.rid
  (requires (fun m -> HS.is_eternal_region r0))
  (ensures (fun (m0: HS.mem) (r1:HH.rid) (m1: HS.mem) ->
    r1 `HH.extends` r0 /\
    HH.fresh_region r1 m0.HS.h m1.HS.h /\
    HH.color r1 = HH.color r0 /\
    m1.HS.h == Map.upd m0.HS.h r1 Heap.emp /\
    m1.HS.tip = m0.HS.tip /\
    Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) m0 m1
  ))
= let m0 = ST.get () in
  let r1 = new_region r0 in
  let m1 = ST.get () in
  new_region_modifies r0 m0 m1 r1;
  r1

let new_colored_region'
  (r0:HH.rid)
  (c:int)
: ST HH.rid
  (requires (fun m -> is_eternal_color c /\ HS.is_eternal_region r0))
  (ensures (fun (m0: HS.mem) (r1:HH.rid) (m1: HS.mem) ->
    r1 `HH.extends` r0 /\
    HH.fresh_region r1 m0.HS.h m1.HS.h /\
    HH.color r1 = c /\
    m1.HS.h == Map.upd m0.HS.h r1 Heap.emp /\
    m1.HS.tip = m0.HS.tip /\
    Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) m0 m1
  ))
= let m0 = ST.get () in
  let r1 = new_colored_region r0 c in
  let m1 = ST.get () in
  new_region_modifies r0 m0 m1 r1;
  r1

(* Allocation in eternal region: same proof as salloc_post *)

abstract
let ralloc_post_modifies
  (i: HH.rid)
  (#a:Type)
  (init:a)
  (m0: HS.mem)
  (s: HS.reference a{HS.is_eternal_region s.HS.id})
  (m1: HS.mem)
: Lemma
  (requires (ralloc_post i init m0 s m1))
  (ensures (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) m0 m1 /\ Modifies.locset_dead m0 (HS.locset_of_reference s)))
= (* for Modifies.locset_dead: *)
  Modifies.loc_of_object_inj_forall HS.root_class;
  (* for Modifies.modifies: 
     1. first prove that s is modified *)
  (* TODO: this is the same proof as HyperStackNG.modifies_locset_of_reference_intro,
     except that HyperStack.contains does not hold;
     so it would be nice to try to weaken the hypotheses of that lemma accordingly *)
  Modifies.modifies_intro (HS.locset_of_reference s) m0 (HS.upd m0 s init) (fun ty l c o g ->
    Modifies.modifies_loc_refines_0 HS.class (HS.ObjectReference _ s) m0 (HS.upd m0 s init) (fun o' _ -> ()) c o (g (Modifies.loc_of_object HS.class (HS.ObjectReference _ s)))
  );
  (* 2. then remove it thanks to the fact that it was dead before *)
  Modifies.modifies_locset_dead TSet.empty (HS.locset_of_reference s) m0 m1
