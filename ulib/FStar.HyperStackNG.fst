module FStar.HyperStackNG
include FStar.HyperStack

module HH = FStar.HyperHeap

noeq type object : Type =
| ObjectReference:
    (ty: Type) ->
    (r: reference ty) ->
    object
| ObjectRegionLiveness (* change "live_region" *) :
    (r: HH.rid) ->
    object
| ObjectTip

unfold
let objects_disjoint (o1 o2: object): Tot Type0 =
  match o1 with
  | ObjectReference _ r1 ->
    begin match o2 with
    | ObjectReference _ r2 ->
      frameOf r1 <> frameOf r2 \/
      (
	frameOf r1 == frameOf r2 /\
	~ (as_ref r1 === as_ref r2)
      )
    | _ -> True
    end
  | ObjectRegionLiveness r1 ->
    begin match o2 with
    | ObjectRegionLiveness r2 -> r1 <> r2
    | _ -> True
    end
  | ObjectTip -> ~ (o2 == ObjectTip)

unfold
let object_live (m: mem) (o: object): Tot Type0 =
  match o with
  | ObjectReference _ r -> contains m r
  | ObjectRegionLiveness r -> live_region m r
  | ObjectTip -> True

unfold
let object_contains = object_live

unfold
let object_preserved (o: object) (m m': mem): Tot Type0 =
  match o with
  | ObjectReference _ r ->
    contains m r ==> (contains m' r /\ sel m' r == sel m r)
  | ObjectRegionLiveness r ->
    live_region m r ==> live_region m' r
  | ObjectTip ->
    m'.tip == m.tip

unfold
let object_includes (o1 o2: object) : Tot Type0 = o1 == o2

unfold
let object_final (o: object): Tot Type0 = ObjectTip? o

let root_class: Modifies.class' u#0 u#1 mem 0 object =
  Modifies.Class
    (* heap  *)                 mem
    (* level *)                 0
    (* carrier *)               object
    (* disjoint *)              objects_disjoint
    (* live *)                  object_live
    (* contains *)              object_contains
    (* preserved *)             object_preserved
    (* includes *)              object_includes
    (* final *)                 object_final
    (* ancestor_count *)        (fun x -> 0)
    (* ancestor_types *)        (fun x y -> false_elim ())
    (* ancestor_class_levels *) (fun x y -> false_elim ())
    (* ancestor_classes *)      (fun x y -> false_elim ())
    (* ancestor_objects *)      (fun x y -> false_elim ())

abstract
let class_invariant
  ()
: Lemma
  (requires True)
  (ensures (Modifies.class_invariant root_class root_class))
//  [SMTPat (Modifies.class_invariant root_class root_class)]
= let s: Modifies.class_invariant_body u#0 u#1 root_class root_class = {
    Modifies.preserved_refl =  (fun _ _ -> ());
    Modifies.preserved_trans = (fun _ _ _ _ -> ());
    Modifies.preserved_ancestors_preserved = begin
      let g
        (x: object)
	(h: mem)
	(h' : mem)
	(s: squash (Modifies.Class?.ancestor_count root_class x > 0))
	(f: (
	  (i: nat { i < Modifies.Class?.ancestor_count root_class x } ) ->
	  Lemma
	  (Modifies.Class?.preserved (Modifies.Class?.ancestor_classes root_class x i) (Modifies.ancestor_objects root_class x i) h h')
	))
      : Lemma
	(ensures (Modifies.Class?.preserved root_class x h h'))
      = ()
      in
      g
    end;
    Modifies.disjoint_sym = (fun _ _ -> ());
    Modifies.level_0_class_eq_root = ();
    Modifies.level_0_fresh_disjoint = (fun _ _ _ _ -> ());
    Modifies.live_preserved_preserved = (fun _ _ _ -> ());
    Modifies.preserved_live = (fun _ _ _ -> ());
    Modifies.preserved_contains = (fun _ _ _ -> ());
    Modifies.live_contains = (fun _ _ -> ());
    Modifies.ancestors_contains = begin
      let g
	(h: mem)
	(o: object)
	(s: squash (Modifies.Class?.ancestor_count root_class o > 0))
	(f: (
	  (i: nat {i < Modifies.Class?.ancestor_count root_class o } ) ->
	  Lemma
	  (Modifies.Class?.contains (Modifies.Class?.ancestor_classes root_class o i) h (Modifies.ancestor_objects root_class o i))
	))
      : Lemma
	(ensures (Modifies.Class?.contains root_class h o))
      = ()
      in
      g
    end;
    Modifies.live_ancestors = (fun _ _ _ -> ());
    Modifies.includes_refl = (fun _ -> ());
    Modifies.includes_trans = (fun _ _ _ -> ());
    Modifies.preserved_includes = (fun _ _ _ _ -> ());
    Modifies.includes_contains = (fun _ _ _ -> ());
    Modifies.contains_live = (fun _ _ _ -> ());
    Modifies.includes_ancestors = (fun _ _ _ -> ());
    Modifies.disjoint_includes = (fun _ _ _ -> ());
    Modifies.final_equal_or_disjoint = (fun _ _ -> ());
    Modifies.ancestor_not_final = (fun _ _ -> ());
  }
  in
  (Modifies.class_invariant_intro s)

let class: Modifies.class root_class 0 object = class_invariant () ; root_class

(*
let class_eq
  ()
: Lemma
  (requires True)
  (ensures (class == root_class))
  [SMTPatOr [[SMTPat class]; [SMTPat root_class]]]
= ()
*)

let locset_of_reference
  (#t: Type)
  (r: reference t)
: Tot (Modifies.locset u#0 u#1 root_class)
= Modifies.locset_of_object class (ObjectReference t r)

unfold
let object_is_reference_of_region
  (o': object)
  (r: HH.rid)
: Tot Type0
= match o' with
  | ObjectReference _ re -> frameOf re == r
  | _ -> False

assume val locset_of_region (r: HH.rid): Tot (Modifies.locset u#0 u#1 root_class)

assume val mem_locset_of_region
  (r: HH.rid)
  (o: Modifies.loc root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (locset_of_region r) <==> (
    exists (o' : object) .
      o == Modifies.loc_of_object class o' /\
      o' `object_is_reference_of_region` r
  )))
//  [SMTPat (TSet.mem o (locset_of_region r))]

let locset_of_reference_subset_locset_of_region
  (#t: Type)
  (reg: HH.rid)
  (ref: reference t)
: Lemma
  (requires (frameOf ref == reg))
  (ensures (locset_of_reference ref `TSet.subset` locset_of_region reg))
  [SMTPatOr [[SMTPatT (frameOf ref == reg)]; [SMTPat (locset_of_reference ref `TSet.subset` locset_of_region reg)]]]
= Classical.forall_intro (mem_locset_of_region reg)

let locset_of_region_liveness_tag
  (r: HH.rid)
: Tot (Modifies.locset u#0 u#1 root_class)
= Modifies.locset_of_object class (ObjectRegionLiveness r)

let locset_of_region_with_liveness
  (r: HH.rid)
: Tot (Modifies.locset u#0 u#1 root_class)
= TSet.union (locset_of_region r) (locset_of_region_liveness_tag r)

let locset_of_region_subset_locset_of_region_with_liveness
  (r: HH.rid)
: Lemma
  (requires True)
  (ensures (locset_of_region r `TSet.subset` locset_of_region_with_liveness r))
= ()

let locset_of_region_with_liveness_disjoint
  (#t: Type)
  (reg1 reg2: HH.rid)
: Lemma
  (requires (reg1 <> reg2))
  (ensures (Modifies.locset_disjoint u#0 u#1 (locset_of_region_with_liveness reg1) (locset_of_region_with_liveness reg2)))
  [SMTPat (reg1 <> reg2)]
= Classical.forall_intro (mem_locset_of_region reg1);
  Classical.forall_intro (mem_locset_of_region reg2)

let locset_of_region_liveness_tag_subset_locset_of_region_with_liveness
  (r: HH.rid)
: Lemma
  (requires True)
  (ensures (locset_of_region_liveness_tag r `TSet.subset` locset_of_region_with_liveness r))
  [SMTPat (locset_of_region_liveness_tag r `TSet.subset` locset_of_region_with_liveness r)]
= ()

let locset_of_region_liveness_tag_disjoint_locset_of_region
  (r1 r2: HH.rid)
: Lemma
  (requires True)
  (ensures (locset_of_region_liveness_tag r1 `Modifies.locset_disjoint` locset_of_region r2))
  [SMTPat (locset_of_region_liveness_tag r1 `Modifies.locset_disjoint` locset_of_region r2)]
= Classical.forall_intro (mem_locset_of_region r2)

private let test_1
  (#t1 #t2: Type)
  (reg: HH.rid)
  (r1: reference t1)
  (r2: reference t2)
  (h1 h2 h3: mem)
: Lemma
  (requires (Modifies.modifies (locset_of_reference r1) h1 h2 /\ Modifies.modifies (locset_of_reference r2) h2 h3 /\ frameOf r1 == reg /\ frameOf r2 == reg))
  (ensures (Modifies.modifies (locset_of_region reg) h1 h3))
= ()

let modifies_locset_of_reference_intro #a (h:mem) (x:reference a) (v:a) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ Modifies.modifies (locset_of_reference x) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (contains h x)]
  = Modifies.modifies_intro (locset_of_reference x) h (upd h x v) (fun ty l c o g ->
      Modifies.modifies_loc_refines_0 class (ObjectReference _ x) h (upd h x v) (fun o' _ -> ()) c o (g (Modifies.loc_of_object class (ObjectReference _ x)))
    )

let modifies_locset_of_reference_elim
  #a
  (x: reference a)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint (locset_of_reference x) s))
  (ensures (contains h x ==> (contains h' x /\ sel h' x == sel h x)))
= ()

let modifies_locset_of_region_liveness_tag_elim
  (x: HH.rid)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint (locset_of_region_liveness_tag x) s))
  (ensures (live_region h x ==> live_region h' x))
= ()

let modifies_reference_elim
  (#t: Type)
  (r: reference t)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint (locset_of_reference r) s))
  (ensures (contains h r ==> (contains h' r /\ sel h' r == sel h r)))
  [SMTPatT (Modifies.modifies s h h'); SMTPatT (Modifies.locset_disjoint (locset_of_reference r) s)]
= ()

(* The tip as a memory location *)

let locset_of_tip : Modifies.locset root_class = Modifies.locset_of_object class ObjectTip

let locset_disjoint_locset_of_tip_locset_of_reference
  (#t: Type)
  (r: reference t)
: Lemma
  (requires True)
  (ensures (Modifies.locset_disjoint locset_of_tip (locset_of_reference r)))
  [SMTPat (Modifies.locset_disjoint locset_of_tip (locset_of_reference r))]
= ()

let locset_disjoint_locset_of_tip_locset_of_region
  (r: HH.rid)
: Lemma
  (requires True)
  (ensures (Modifies.locset_disjoint locset_of_tip (locset_of_region r)))
  [SMTPat (Modifies.locset_disjoint locset_of_tip (locset_of_region r))]
= Classical.forall_intro (mem_locset_of_region r)

let locset_disjoint_locset_of_tip_locset_of_region_liveness_tag
  (r: HH.rid)
: Lemma
  (requires True)
  (ensures (Modifies.locset_disjoint locset_of_tip (locset_of_region_liveness_tag r)))
  [SMTPat (Modifies.locset_disjoint locset_of_tip (locset_of_region_liveness_tag r))]
= ()

let locset_disjoint_locset_of_tip_locset_of_region_with_liveness
  (r: HH.rid)
: Lemma
  (requires True)
  (ensures (Modifies.locset_disjoint locset_of_tip (locset_of_region_with_liveness r)))
  [SMTPat (Modifies.locset_disjoint locset_of_tip (locset_of_region_with_liveness r))]
= ()

let modifies_tip_elim
  (#t: Type)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint locset_of_tip s))
  (ensures (h'.tip == h.tip))
  [SMTPatT (Modifies.modifies s h h'); SMTPatT (Modifies.locset_disjoint locset_of_tip s)]
= ()

(* Prove that regions that were not live before and are not live after can be ignored by modifies. *)

abstract
let rec live_not_live_region_loc_disjoint
  (r: HH.rid)
  (h: mem)
  (#t: Type u#1)
  (#l: nat)
  (c: Modifies.class root_class l t)
  (o: t)
  (lo: Modifies.loc root_class { TSet.mem lo (locset_of_region_with_liveness r) } )
: Lemma
  (requires (Modifies.Class?.live c h o /\ (~ (live_region h r))))
  (ensures (Modifies.loc_disjoint (Modifies.loc_of_object c o) lo))
  (decreases l)
= if l = 0
  then
    let _ = Modifies.level_0_class_eq_root c in
    let c: Modifies.class root_class 0 object = c in
    let o: object = o in
    if ObjectTip? o
    then locset_disjoint_locset_of_tip_locset_of_region_with_liveness r
    else
      let rg = match o with
      | ObjectReference _ rf -> frameOf rf
      | ObjectRegionLiveness rg -> rg
      in
      let _ = assert (Modifies.locset_disjoint (locset_of_region_with_liveness rg) (locset_of_region_with_liveness r)) in // TODO: WHY needed?
      let _ : squash (TSet.mem (Modifies.loc_of_object c o) (locset_of_region_with_liveness rg)) = match o with
      | ObjectReference _ rf ->
        locset_of_reference_subset_locset_of_region rg rf // TODO: WHY not triggered?
      | _ -> ()
      in
      ()
  else
    let k
      (i: nat { i < Modifies.Class?.ancestor_count c o } )
    : Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i)) lo)
    = Modifies.live_ancestors c h o i;
      live_not_live_region_loc_disjoint r h (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) lo
    in
    Modifies.loc_disjoint_ancestors_left c o lo k

abstract
let modifies_not_live_region
  (r: HH.rid)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies u#0 u#1 (TSet.union s (locset_of_region_with_liveness r)) h h' /\ (~ (live_region h r))))
  (ensures (Modifies.modifies s h h'))
= let z : squash (Modifies.modifies u#0 u#1 (TSet.union s (locset_of_region_with_liveness r)) h h') = () in
  let f'
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' s } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
    ()
  : Lemma
    (requires (Modifies.Class?.live c h o))
    (ensures (Modifies.Class?.preserved c o h h'))
  = let g'
      (o': Modifies.loc root_class { TSet.mem o' (TSet.union s (locset_of_region_with_liveness r)) } )
    : Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    = Classical.or_elim
        #(TSet.mem o' s)
        #(TSet.mem o' (locset_of_region_with_liveness r))
        #(fun _ -> Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
        (fun _ -> g o')
        (fun _ -> live_not_live_region_loc_disjoint r h c o o')
    in
    Modifies.modifies_elim (TSet.union s (locset_of_region_with_liveness r)) h h' () c o g'
  in
  let f
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' s } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
  : Lemma
    (requires True)
    (ensures (Modifies.Class?.preserved c o h h'))
  = Classical.move_requires (f' ty l c o g) ();
    Modifies.live_preserved_preserved c h h' o
  in
  Modifies.modifies_intro s h h' f

(* For the purpose of universe resolution, etc. *)

let modifies'
  (s: Modifies.locset root_class)
  (h h': mem)
: Tot Type0
= Modifies.modifies s h h'


(* Allocators and deallocators for regions and references fit into the general modifies clause *)

abstract
let fresh_frame_modifies
  (m0 m1: mem)
: Lemma
  (requires (fresh_frame m0 m1))
  (ensures (Modifies.modifies locset_of_tip m0 m1))
= let _ : squash (~ (live_region m0 m1.tip)) =
    if Map.contains m0.h m1.tip then () else ()
  in
  let _ : squash (m1.h == Map.upd m0.h m1.tip Heap.emp) = () in
  let rec f'
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' locset_of_tip } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
    ()
  : Lemma
    (requires (Modifies.Class?.live c m0 o))
    (ensures (Modifies.Class?.preserved c o m0 m1))
    (decreases l)
  = g (Modifies.loc_of_object class ObjectTip);
    if l = 0
    then begin
      Modifies.level_0_class_eq_root c;
      Modifies.loc_disjoint_level_zero_same c class o ObjectTip
    end else begin
      Modifies.loc_disjoint_level_zero c class o ObjectTip;
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
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' locset_of_tip } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
  : Lemma
    (Modifies.Class?.preserved c o m0 m1)
  = Classical.move_requires (f' ty l c o g) ();
    Modifies.live_preserved_preserved c m0 m1 o    
  in
  Modifies.modifies_intro locset_of_tip m0 m1 f

let locset_of_region_with_liveness_mem_elim
  (r: HH.rid)
  (o: Modifies.loc root_class)
: Lemma
  (requires (TSet.mem o (locset_of_region_with_liveness r)))
  (ensures (exists (o' : object) . (
    o == Modifies.loc_of_object class o' /\ (
    match o' with
    | ObjectReference _ rf -> frameOf rf == r
    | ObjectRegionLiveness rg -> r == rg
    | ObjectTip -> False
  ))))
= Classical.or_elim
    #(TSet.mem o (locset_of_region r))
    #(TSet.mem o (locset_of_region_liveness_tag r))
    #(fun _ -> exists (o' : object) . (
      o == Modifies.loc_of_object class o' /\ (
      match o' with
      | ObjectReference _ rf -> frameOf rf == r
      | ObjectRegionLiveness rg -> r == rg
      | ObjectTip -> False
    )))
    (fun _ -> mem_locset_of_region r o)
    (fun _ -> ())

let locset_of_region_with_liveness_mem_object_elim
  (r: HH.rid)
  (o': object)
: Lemma
  (requires (TSet.mem (Modifies.loc_of_object class o') (locset_of_region_with_liveness r)))
  (ensures (match o' with
    | ObjectReference _ rf -> frameOf rf == r
    | ObjectRegionLiveness rg -> r == rg
    | ObjectTip -> False
  ))
= Modifies.loc_of_object_inj_forall root_class;
  locset_of_region_with_liveness_mem_elim r (Modifies.loc_of_object class o')

let modifies_pop
  (m0: mem)
: Lemma
  (requires (poppable m0))
  (ensures (poppable m0 /\ Modifies.modifies u#0 u#1 (TSet.union locset_of_tip (locset_of_region_with_liveness m0.tip)) m0 (pop m0)))
= let s : Modifies.locset root_class = TSet.union locset_of_tip (locset_of_region_with_liveness m0.tip) in
  let m1 : mem = pop m0 in
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let _ : squash (m1.h == Map.restrict dom m0.h) = () in
  let _ : squash (~ (live_region m1 m0.tip)) = () in
  let rec f'
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' s } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
    ()
  : Lemma
    (requires (Modifies.Class?.live c m0 o))
    (ensures (Modifies.Class?.preserved c o m0 m1))
    (decreases l)
  = g (Modifies.loc_of_object class ObjectTip);
    if l = 0
    then begin
      Modifies.level_0_class_eq_root c;
      match o with
        | ObjectReference _ rf ->
          if frameOf rf = m0.tip
          then begin
            mem_locset_of_region m0.tip (Modifies.loc_of_object c o);
            g (Modifies.loc_of_object c o);
            Modifies.loc_disjoint_level_zero_same c c o o
          end else
            ()
        | ObjectRegionLiveness _ ->
          g (Modifies.loc_of_object class (ObjectRegionLiveness m0.tip));
          Modifies.loc_disjoint_level_zero_same c class o (ObjectRegionLiveness m0.tip)
        | ObjectTip -> 
          Modifies.loc_disjoint_level_zero_same c class o ObjectTip
    end else begin
      Modifies.loc_disjoint_level_zero c class o ObjectTip;
      let k
        (i: nat { i < Modifies.Class?.ancestor_count c o } )
      : Lemma
        (Modifies.Class?.preserved (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) m0 m1)
      = Modifies.live_ancestors c m0 o i;
        let g'
          (o' : Modifies.loc root_class { TSet.mem o' s } )
        : Lemma
          (Modifies.loc_disjoint (Modifies.loc_of_object (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i)) o')
        = Classical.or_elim
            #(TSet.mem o' locset_of_tip)
            #(TSet.mem o' (locset_of_region_with_liveness m0.tip))
            #(fun _ -> Modifies.loc_disjoint (Modifies.loc_of_object (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i)) o')
            (fun _ -> ())
            (fun _ -> begin
              locset_of_region_with_liveness_mem_elim m0.tip o';
              let f
                (o': object { TSet.mem (Modifies.loc_of_object class o') s } )
              : Lemma
                (Modifies.loc_disjoint (Modifies.loc_of_object (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i)) (Modifies.loc_of_object class o'))
              = g (Modifies.loc_of_object class o');
                Modifies.loc_disjoint_level_zero c class o o'
              in
              Classical.forall_intro f
            end)
        in
        f' _ _ (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i) g' ()
      in
      Modifies.preserved_ancestors_preserved c o m0 m1 k
    end
  in
  let f
    (ty: Type u#1)
    (l: nat)
    (c: Modifies.class root_class l ty )
    (o: ty)
    (g: (
      (o' : Modifies.loc root_class { TSet.mem o' s } ) ->
      Lemma
      (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
    ))
  : Lemma
    (Modifies.Class?.preserved c o m0 m1)
  = Classical.move_requires (f' ty l c o g) ();
    Modifies.live_preserved_preserved c m0 m1 o    
  in
  Modifies.modifies_intro s m0 m1 f

let modifies_equal_tip
  (ls: Modifies.locset root_class)
  (h h' : mem)
: Lemma
  (requires (
    Modifies.modifies u#0 u#1 (TSet.union locset_of_tip ls) h h' /\
    h'.tip == h.tip
  ))
  (ensures (Modifies.modifies ls h h'))
= Modifies.loc_of_object_inj_forall root_class;
  Modifies.modifies_final locset_of_tip ls h h'
