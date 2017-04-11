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

unfold
let object_live (m: mem) (o: object): Tot Type0 =
  match o with
  | ObjectReference _ r -> contains m r
  | ObjectRegionLiveness r -> live_region m r

unfold
let object_contains = object_live

unfold
let object_preserved (o: object) (m m': mem): Tot Type0 =
  match o with
  | ObjectReference _ r ->
    contains m r ==> (contains m' r /\ sel m' r == sel m r)
  | ObjectRegionLiveness r ->
    live_region m r ==> live_region m' r

unfold
let object_includes (o1 o2: object) : Tot Type0 = o1 == o2

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

(* Prove that regions that were not live before and are not live after can be ignored by modifies. *)


#reset-options "--z3rlimit 32"

let modifies_not_live_region
  (r: HH.rid)
  (s: Modifies.locset root_class)
  (h h': mem)
: Lemma
  (requires (Modifies.modifies u#0 u#1 (TSet.union s (locset_of_region_with_liveness r)) h h' /\ (~ (live_region h r)) /\ (~ (live_region h' r))))
  (ensures (Modifies.modifies s h h'))
= let z : squash (Modifies.modifies u#0 u#1 (TSet.union s (locset_of_region_with_liveness r)) h h') = () in
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
    (decreases l)
  = if l = 0
    then begin
      Modifies.level_0_class_eq_root c;
      let c: Modifies.class root_class 0 object = c in
      let o: object = o in
      match o with
      | ObjectReference _ rf ->
        let k
          ()
        : Lemma
          (requires (contains h rf))
          (ensures (contains h' rf /\ sel h' rf == sel h rf))
        = let rg = frameOf rf in
          assert (Modifies.locset_disjoint (locset_of_region_with_liveness rg) (locset_of_region_with_liveness r)); // TODO: WHY needed?
          locset_of_reference_subset_locset_of_region rg rf; // TODO: WHY not triggered?
          let g'
            (o': Modifies.loc root_class { TSet.mem o' (TSet.union s (locset_of_region_with_liveness r)) } )
          : Lemma
            (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
          = Classical.or_elim
              #(TSet.mem o' s)
              #(TSet.mem o' (locset_of_region_with_liveness r))
              #(fun _ -> Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
              (fun _ -> g o')
              (fun _ -> ())
          in
          Modifies.modifies_elim (TSet.union s (locset_of_region_with_liveness r)) h h' () c o g'
        in
        let v : squash (Modifies.Class?.preserved c o h h') =
          Classical.move_requires k ()
        in
        v
      | ObjectRegionLiveness rg ->
        let k
          ()
        : Lemma
          (requires (live_region h rg))
          (ensures (live_region h' rg))
        = assert (Modifies.locset_disjoint (locset_of_region_with_liveness rg) (locset_of_region_with_liveness r)); // TODO: WHY WHY WHY is this assert needed?
          let g'
            (o': Modifies.loc root_class { TSet.mem o' (TSet.union s (locset_of_region_with_liveness r)) } )
          : Lemma
            (Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
          = Classical.or_elim
              #(TSet.mem o' s)
              #(TSet.mem o' (locset_of_region_with_liveness r))
              #(fun _ -> Modifies.loc_disjoint (Modifies.loc_of_object c o) o')
              (fun _ -> g o')
              (fun _ -> ())
          in
          Modifies.modifies_elim (TSet.union s (locset_of_region_with_liveness r)) h h' z c o g'
        in
        let v : squash (Modifies.Class?.preserved c o h h') =
          Classical.move_requires k ()
        in
        v
    end else begin
    (*
      let g'
        (i: nat { i < Modifies.Class?.ancestor_count c o } )
        (o' : Modifies.loc root_class { TSet.mem o' s } )
      : Lemma
        (Modifies.loc_disjoint (Modifies.loc_of_object (Modifies.Class?.ancestor_classes c o i) (Modifies.Class?.ancestor_objects c o i)) o')
      =        
      in
      *)
      assume (Modifies.Class?.preserved c o h h')
    end
  in
  Modifies.modifies_intro s h h' f

(* For the purpose of universe resolution, etc. *)

let modifies'
  (s: Modifies.locset root_class)
  (h h': mem)
: Tot Type0
= Modifies.modifies s h h'
