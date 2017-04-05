// with: --include ulib --include ulib/hyperstack

module FStar.BufferNG

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.ST
module P = FStar.Pointer

(* Definition of the buffer type *)

noeq private type buffer_root (t: Type) =
| BufferRootSingleton:
  (p: P.pointer t) ->
  buffer_root t
| BufferRootArray:
  (#max_length: UInt32.t) ->
  (p: P.pointer (P.array max_length t)) ->
  buffer_root t

private let buffer_root_length (#t: Type) (b: buffer_root t): Tot UInt32.t = match b with
| BufferRootSingleton _ -> 1ul
| BufferRootArray #t #len _ -> len

noeq private type _buffer (t: Type) =
| Buffer:
  (broot: buffer_root t) ->
  (bidx: UInt32.t) ->
  (blength: UInt32.t { UInt32.v bidx + UInt32.v blength <= UInt32.v (buffer_root_length broot) } ) ->
  _buffer t
abstract let buffer (t: Type): Tot Type = _buffer t

(* Constructors *)

abstract let singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Tot (buffer t)
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Tot (buffer t)
= Buffer (BufferRootArray p) 0ul length

(* Ghost operations *)

abstract let length
  (#t: Type)
  (b: buffer t)
: GTot UInt32.t
= Buffer?.blength b

abstract let length_singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (length (singleton_buffer_of_pointer p) == 1ul))
  [SMTPat (length (singleton_buffer_of_pointer p))]
= ()

abstract let length_buffer_of_array_pointer
  (#t: Type)
  (#len: UInt32.t)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (length (buffer_of_array_pointer p) == len))
  [SMTPat (length (buffer_of_array_pointer p))]
= ()

abstract let gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: GTot (P.pointer t)
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let gpointer_of_buffer_cell_singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (i: UInt32.t { UInt32.v i < 1 } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (singleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (singleton_buffer_of_pointer p) i)]
= ()

abstract let gpointer_of_buffer_cell_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t: Type)
  (p: P.pointer (P.array len t))
  (i: UInt32.t { UInt32.v i < UInt32.v len } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (buffer_of_array_pointer p) i == P.gcell p i))
  [SMTPat (gpointer_of_buffer_cell (buffer_of_array_pointer p) i)]
= ()

abstract let live
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= match b.broot with
  | BufferRootSingleton p -> P.live h p
  | BufferRootArray p -> P.live h p

abstract
let live_singleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (live h (singleton_buffer_of_pointer p) == P.live h p))
  [SMTPat (live h (singleton_buffer_of_pointer p))]
= ()

abstract
let live_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (live h (buffer_of_array_pointer p) == P.live h p))
  [SMTPat (live h (buffer_of_array_pointer p))]
= ()

abstract
let live_gpointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (P.live h (gpointer_of_buffer_cell b i) <==> live h b))
  [SMTPat (P.live h (gpointer_of_buffer_cell b i))]
= ()

abstract let contains
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= match b.broot with
  | BufferRootSingleton p -> P.contains h p
  | BufferRootArray p -> P.contains h p

abstract
let contains_singleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (contains h (singleton_buffer_of_pointer p) == P.contains h p))
  [SMTPat (contains h (singleton_buffer_of_pointer p))]
= ()

abstract
let contains_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (contains h (buffer_of_array_pointer p) == P.contains h p))
  [SMTPat (contains h (buffer_of_array_pointer p))]
= ()

abstract
let contains_gpointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (P.contains h (gpointer_of_buffer_cell b i) <==> contains h b))
  [SMTPat (P.contains h (gpointer_of_buffer_cell b i))]
= ()

abstract let gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: GTot (buffer t)
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let length_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (length (gsub b i len) == len))
  [SMTPat (length (gsub b i len))]
= ()

abstract let gsub_gsub
  (#a: Type)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t{UInt32.v i1 + UInt32.v len1 <= UInt32.v (length b)})
  (i2: UInt32.t)
  (len2: UInt32.t {UInt32.v i2 + UInt32.v len2 <= UInt32.v len1})
: Lemma
  (ensures (gsub (gsub b i1 len1) i2 len2 == gsub b FStar.UInt32.(i1 +^ i2) len2))
= ()

abstract let gsub_zero_length
  (#a: Type)
  (b: buffer a)
: Lemma
  (ensures (gsub b 0ul (length b) == b))
= ()

private let buffer_root_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: GTot (Seq.seq t)
= match b with
  | BufferRootSingleton p ->
    Seq.create 1 (P.gread h p)
  | BufferRootArray p ->
    P.gread h p

private let length_buffer_root_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_root_as_seq h b) == UInt32.v (buffer_root_length b)))
  [SMTPat (Seq.length (buffer_root_as_seq h b))]
= ()

abstract let as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq t)
= let i = UInt32.v (Buffer?.bidx b) in
  Seq.slice (buffer_root_as_seq h (Buffer?.broot b)) i (i + UInt32.v (Buffer?.blength b))

abstract let length_as_seq
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (Seq.length (as_seq h b) == UInt32.v (length b)))
  [SMTPat (Seq.length (as_seq h b))]
= ()

abstract let as_seq_singleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (as_seq h (singleton_buffer_of_pointer p) == Seq.create 1 (P.gread h p)))
  [SMTPat (as_seq h (singleton_buffer_of_pointer p))]
= Seq.slice_length (Seq.create 1 (P.gread h p))

abstract let as_seq_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (as_seq h (buffer_of_array_pointer p) == P.gread h p))
  [SMTPat (as_seq h (buffer_of_array_pointer p))]
= Seq.slice_length (P.gread h p)

abstract let as_seq_gsub
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (as_seq h (gsub b i len) == Seq.slice (as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)))
  [SMTPat (as_seq h (gsub b i len))]
= Seq.slice_slice (buffer_root_as_seq h (Buffer?.broot b)) (UInt32.v (Buffer?.bidx b)) (UInt32.v (Buffer?.bidx b) + UInt32.v (Buffer?.blength b)) (UInt32.v i) (UInt32.v i + UInt32.v len)

abstract let gpointer_of_buffer_cell_gsub
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t { UInt32.v i1 + UInt32.v len <= UInt32.v (length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v len } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsub b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)))
  [SMTPat (gpointer_of_buffer_cell (gsub b i1 len) i2)]
= ()

let gindex
  (#a: Type)
  (h: HS.mem)
  (b: buffer a)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: GTot a
= Seq.index (as_seq h b) (UInt32.v i)

abstract let gread_gpointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (P.gread h (gpointer_of_buffer_cell b i) == gindex h b i))
  [SMTPat (gindex h b i)]
= ()

(* Effectful operations, memory unchanged. All effectful operations need the buffer to be live *)

abstract let pointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: HST.Stack (P.pointer t)
  (requires (fun h -> live h b))
  (ensures (fun h v h' -> h == h' /\ v == gpointer_of_buffer_cell b i))
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let sub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: HST.Stack (buffer t)
  (requires (fun h -> live h b))
  (ensures (fun h v h' -> h == h' /\ v == gsub b i len))
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let index
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: HST.Stack t
  (requires (fun h -> live h b))
  (ensures (fun h v h' -> h' == h /\ v == gindex h b i))
= P.read (pointer_of_buffer_cell b i)

(* buffer write: needs clearer "modifies" clauses. We could, at first, say that the only memory that is modified is the memory location of the sole cell being modified: *)

abstract
let upd'
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  (v: t)
: HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h _ h' ->
    live h b /\    
    Modifies.modifies (P.locset_of_pointer (gpointer_of_buffer_cell b i)) h h' /\
    gindex h' b i == v
  ))
 = P.write' (pointer_of_buffer_cell b i) v

(* Or, we can also define: *)

abstract
let rec locset_of_buffer
  (#t: Type)
  (b: buffer t)
: Ghost (Modifies.locset HS.root_class)
  (requires True)
  (ensures (fun _ -> True))
  (decreases (UInt32.v (length b)))
= let l = length b in
  if l = 0ul
  then TSet.empty
  else 
    let l' = FStar.UInt32.(l -^ 1ul) in
    TSet.union (P.locset_of_pointer (gpointer_of_buffer_cell b 0ul)) (locset_of_buffer (gsub b 1ul l'))

private
let rec mem_locset_of_buffer_elim
  (#t: Type)
  (b: buffer t)
  (o: Modifies.loc HS.root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (locset_of_buffer b) ==> (
    exists i . TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i))
  )))
  (decreases (UInt32.v (length b)))
= let l = length b in
  if l = 0ul
  then ()
  else
    let l' = FStar.UInt32.(l -^ 1ul) in
    mem_locset_of_buffer_elim (gsub b 1ul l') o

private
let rec mem_locset_of_buffer_intro
  (#t: Type)
  (b: buffer t)
  (o: Modifies.loc HS.root_class)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i)) ==> TSet.mem o (locset_of_buffer b)))
  (decreases (UInt32.v (length b)))
= let l = length b in
  if l = 0ul
  then ()
  else if i = 0ul
  then ()
  else mem_locset_of_buffer_intro (gsub b 1ul (FStar.UInt32.(l -^ 1ul))) o (FStar.UInt32.(i -^ 1ul))

abstract
let mem_locset_of_buffer
  (#t: Type)
  (b: buffer t)
  (o: Modifies.loc HS.root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (locset_of_buffer b) <==> (
    exists i . TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i))
  )))
  [SMTPat (TSet.mem o (locset_of_buffer b))]
= mem_locset_of_buffer_elim b o;
  Classical.forall_intro (mem_locset_of_buffer_intro b o)

abstract
let upd''
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  (v: t)
: HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h _ h' ->
    live h b /\    
    Modifies.modifies (locset_of_buffer b) h h' /\
    gindex h' b i == v /\ (
      forall (i': UInt32.t { UInt32.v i' < UInt32.v (length b) } ) .
      i' <> i ==> gindex h' b i' == gindex h b i'
  )))
 = upd' b i v

(*
abstract let pointer_of_buffer_cell_disjoint
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t { UInt32.v i1 < UInt32.v (buffer_length b) } )
  (i2: UInt32.t { UInt32.v i2 < UInt32.v (buffer_length b) } )
: Lemma
  (requires ( UInt32.v i1 <> UInt32.v i2 ) )
  (ensures (disjoint (pointer_of_buffer_cell b i1) (pointer_of_buffer_cell b i2)))
  [SMTPat (disjoint (pointer_of_buffer_cell b i1) (pointer_of_buffer_cell b i2))]
= ()

(* For a "disjoint" clause on buffers, we could use the following definitions: *)

abstract
let disjoint_buffer_vs_pointer
  (#t1 #t2: Type)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= forall (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } ) . disjoint (pointer_of_buffer_cell b i) p

abstract
let disjoint_buffer_vs_buffer
  (#t1 #t2: Type)
  (b1: buffer t1)
  (b2: buffer t2)
: GTot Type0
= forall
    (i1: UInt32.t { UInt32.v i1 < UInt32.v (buffer_length b1) } )
    (i2: UInt32.t { UInt32.v i2 < UInt32.v (buffer_length b2) } )
  . 
    disjoint (pointer_of_buffer_cell b1 i1) (pointer_of_buffer_cell b2 i2) 

let disjoint_buffer_vs_buffer_sym
  (#t1 #t2: Type)
  (b1: buffer t1)
  (b2: buffer t2)
: Lemma
  (requires True)
  (ensures (disjoint_buffer_vs_buffer b1 b2 <==> disjoint_buffer_vs_buffer b2 b1))
  [SMTPat (disjoint_buffer_vs_buffer b1 b2)]
= ()

let disjoint_buffer_vs_pointer_singleton_buffer_of_pointer
  (#t1 #t2: Type)
  (b: pointer t1)
  (p: pointer t2)
: Lemma
  (requires (disjoint b p))
  (ensures (disjoint_buffer_vs_pointer (singleton_buffer_of_pointer b) p))
  [SMTPat (disjoint_buffer_vs_pointer (singleton_buffer_of_pointer b) p)]
= ()

let disjoint_buffer_vs_buffer_singleton_buffer_of_pointer
  (#t1 #t2: Type)
  (b: buffer t1)
  (p: pointer t2)
: Lemma
  (requires (disjoint_buffer_vs_pointer b p))
  (ensures (disjoint_buffer_vs_buffer b (singleton_buffer_of_pointer p)))
  [SMTPat (disjoint_buffer_vs_buffer b (singleton_buffer_of_pointer p))]
= ()

let disjoint_buffer_vs_pointer_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t1 #t2: Type)
  (b: pointer (array len t1))
  (p: pointer t2)
: Lemma
  (requires (disjoint b p))
  (ensures (disjoint_buffer_vs_pointer (buffer_of_array_pointer b) p))
  [SMTPat (disjoint_buffer_vs_pointer (buffer_of_array_pointer b) p)]
= assert (forall i . includes b (gcell b i))

let disjoint_buffer_vs_buffer_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t1 #t2: Type)
  (b: buffer t1)
  (p: pointer (array len t2))
: Lemma
  (requires (disjoint_buffer_vs_pointer b p))
  (ensures (disjoint_buffer_vs_buffer b (buffer_of_array_pointer p)))
  [SMTPat (disjoint_buffer_vs_buffer b (buffer_of_array_pointer p))]
= assert (forall i . includes p (gcell p i))

let disjoint_buffer_vs_buffer_pointer_of_buffer_cell
  (#t1 #t2: Type)
  (b1: buffer t1)
  (b2: buffer t2)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b2) } )
: Lemma
  (requires (disjoint_buffer_vs_buffer b1 b2))
  (ensures (disjoint_buffer_vs_pointer b1 (pointer_of_buffer_cell b2 i)))
  [SMTPat (disjoint_buffer_vs_pointer b1 (pointer_of_buffer_cell b2 i))]
= ()

let disjoint_buffer_vs_pointer_pointer_of_buffer_cell
  (#t1 #t2: Type)
  (b: buffer t1)
  (p: pointer t2)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (requires (disjoint_buffer_vs_pointer b p))
  (ensures (disjoint (pointer_of_buffer_cell b i) p))
  [SMTPat (disjoint (pointer_of_buffer_cell b i) p)]
= ()

let bwrite
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
  (v: t)
: HST.Stack unit
  (requires (fun h -> live h (pointer_of_buffer_cell b i)))
  (ensures (fun h _ h' -> 
    modifies_1 (pointer_of_buffer_cell b i) h h' /\
    Seq.index (buffer_as_seq h' b) (UInt32.v i) == v /\ (
      forall (j: UInt32.t {UInt32.v j < UInt32.v (buffer_length b) /\ UInt32.v j <> UInt32.v i }) .
        Seq.index (buffer_as_seq h' b) (UInt32.v j) == Seq.index (buffer_as_seq h b) (UInt32.v j)    
  )))
= write (pointer_of_buffer_cell b i) v

(* The modifies class *)

noeq type object =
| ObjectBuffer:
    (#t: Type) ->
    (obj: buffer t) ->
    object
| ObjectPointer:
    (#t: Type) ->
    (obj: pointer t) ->
    object

abstract
let pointer_ancestor
  (#t: Type)
  (p: pointer t)
: Tot HyperStack.object
= HyperStack.Object _ (Pointer?.content p)

let as_aref_object_pointer_ancestor
  (#t: Type)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (HyperStack.as_aref (HyperStack.Object?.r (pointer_ancestor p)) == as_aref p))
= ()

let pointer_ancestor_gfield
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: pointer (DM.t key value))
  (fd: key)
: Lemma
  (requires True)
  (ensures (pointer_ancestor (gfield p fd) == pointer_ancestor p))
  [SMTPat (pointer_ancestor (gfield p fd))]
= ()

let pointer_ancestor_gcell
  (#length: UInt32.t)
  (#value: Type)
  (p: pointer (array length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Lemma
  (requires True)
  (ensures (pointer_ancestor (gcell p i) == pointer_ancestor p))
  [SMTPat (pointer_ancestor (gcell p i))]
= ()

private
let buffer_root_ancestor
  (#t: Type)
  (b: buffer_root t)
: Tot HyperStack.object
= match b with
  | BufferRootSingleton p -> pointer_ancestor p
  | BufferRootArray p -> pointer_ancestor p

abstract
let buffer_ancestor
  (#t: Type)
  (b: buffer t)
: Tot HyperStack.object
= buffer_root_ancestor (Buffer?.broot b)

let ancestor_singleton_buffer_of_pointer
  (#t: Type)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_ancestor (singleton_buffer_of_pointer p) == pointer_ancestor p))
  [SMTPat (buffer_ancestor (singleton_buffer_of_pointer p))]
= ()

let ancestor_buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: pointer (array length t))
: Lemma
  (requires True)
  (ensures (buffer_ancestor (buffer_of_array_pointer p) == pointer_ancestor p))
  [SMTPat (buffer_ancestor (buffer_of_array_pointer p) == pointer_ancestor p)]
= ()

let ancestor_pointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (requires True)
  (ensures (pointer_ancestor (pointer_of_buffer_cell b i) == buffer_ancestor b))
  [SMTPat (pointer_ancestor (pointer_of_buffer_cell b i))]
= ()

let object_ancestor
  (o: object)
: Tot HyperStack.object
= match o with
  | ObjectBuffer b -> buffer_ancestor b
  | ObjectPointer p -> pointer_ancestor p

let objects_disjoint
  (o1 o2: object)
: Tot Type0
= match o1 with
  | ObjectBuffer b1 ->
    begin match o2 with
    | ObjectBuffer b2 -> disjoint_buffer_vs_buffer b1 b2
    | ObjectPointer p2 -> disjoint_buffer_vs_pointer b1 p2
    end
  | ObjectPointer p1 ->
    begin match o2 with
    | ObjectBuffer b2 -> disjoint_buffer_vs_pointer b2 p1
    | ObjectPointer p2 -> disjoint p1 p2
    end

private
let buffer_root_live
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: Tot Type0
= match b with
  | BufferRootSingleton p -> live h p
  | BufferRootArray p -> live h p

abstract
let buffer_live
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Tot Type0
= buffer_root_live h (Buffer?.broot b)

let object_live
  (h: HS.mem)
  (o: object)
= match o with
  | ObjectBuffer b -> buffer_live h b
  | ObjectPointer p -> live h p

private
let buffer_root_contains
  (#t: Type)
  (h: HS.mem)
  (b: buffer_root t)
: Tot Type0
= match b with
  | BufferRootSingleton p -> contains h p
  | BufferRootArray p -> contains h p

abstract
let buffer_contains
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Tot Type0
= buffer_root_contains h (Buffer?.broot b)

abstract
let buffer_contains_singleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_contains h (singleton_buffer_of_pointer p) == contains h p))
  [SMTPat (buffer_contains h (singleton_buffer_of_pointer p))]
= ()

abstract
let buffer_contains_buffer_of_array_pointer
  (#len: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: pointer (array len t))
: Lemma
  (requires True)
  (ensures (buffer_contains h (buffer_of_array_pointer p) == contains h p))
  [SMTPat (buffer_contains h (buffer_of_array_pointer p))]
= ()

abstract
let contains_pointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (buffer_length b) } )
: Lemma
  (requires True)
  (ensures (contains h (pointer_of_buffer_cell b i) == buffer_contains h b))
  [SMTPat (contains h (pointer_of_buffer_cell b i))]
= ()

let object_contains
  (h: HS.mem)
  (o: object)
= match o with
  | ObjectBuffer b -> buffer_contains h b
  | ObjectPointer p -> contains h p

abstract
let pointer_preserved
  (#t: Type)
  (p: pointer t)
  (h1 h2: HS.mem)
: Tot Type0
= (live h1 p ==> (live h2 p /\ gread h2 p == gread h1 p))

abstract
let buffer_preserved
  (#t: Type)
  (p: buffer t)
  (h1 h2: HS.mem)
: Tot Type0
= (buffer_live h1 p ==> (buffer_live h2 p /\ buffer_as_seq h2 p == buffer_as_seq h1 p))

let object_preserved
  (o: object)
  (h1 h2: HS.mem)
: Tot Type0
= match o with
  | ObjectBuffer b -> buffer_preserved b h1 h2
  | ObjectPointer p -> pointer_preserved p h1 h2

let class': Modifies.class' HS.mem 1 object =
  Modifies.Class
    (* heap  *)                 HS.mem
    (* level *)                 1
    (* carrier *)               object
    (* disjoint *)              objects_disjoint
    (* live *)                  object_live
    (* contains *)              object_contains
    (* preserved *)             object_preserved
    (* ancestor_count *)        (fun x -> 1)
    (* ancestor_types *)        (fun x y -> HS.object)
    (* ancestor_class_levels *) (fun x y -> 0)
    (* ancestor_classes *)      (fun x y -> HS.class)
    (* ancestor_objects *)      (fun x y -> object_ancestor x)

abstract
let class_invariant ()
: Lemma 
  (requires True)
  (ensures (Modifies.class_invariant HS.class class'))
  [SMTPat (Modifies.class_invariant HS.class class')]
= let s: Modifies.class_invariant_body u#0 u#1 HS.class class' = {
    Modifies.preserved_refl = (let f _ _ = () in f);
    Modifies.preserved_trans = (let f _ _ _ _ = () in f);
    Modifies.preserved_ancestors_preserved = begin
      let g
	(x: object)
	(h: HS.mem)
	(h' : HS.mem)
	(s: squash (Modifies.Class?.ancestor_count class' x > 0))
	(f: (
	  (i: nat { i < Modifies.Class?.ancestor_count class' x } ) ->
	  Lemma
	  (Modifies.Class?.preserved (Modifies.Class?.ancestor_classes class' x i) (Modifies.ancestor_objects class' x i) h h')
	))
      : Lemma
	(ensures (Modifies.Class?.preserved class' x h h'))
      = f 0
      in
      g
    end;
    Modifies.class_disjoint_sym = (let f _ _ = () in f);
    Modifies.level_0_class_eq_root = ();
    Modifies.level_0_fresh_disjoint = (let f _ _ _ _ = () in f);
    Modifies.preserved_live = (let f _ _ _ = () in f);
    Modifies.preserved_contains = (let f _ _ _ = () in f);
    Modifies.live_contains = (let f _ _ = () in f);
    Modifies.ancestors_contains = begin
      let g
	(h: HS.mem)
	(o: object)
	(s: squash (Modifies.Class?.ancestor_count class' o > 0))
	(f: (
	  (i: nat {i < Modifies.Class?.ancestor_count class' o } ) ->
	  Lemma
	  (Modifies.Class?.contains (Modifies.Class?.ancestor_classes class' o i) h (Modifies.ancestor_objects class' o i))
        ))
      : Lemma
	(ensures (Modifies.Class?.contains class' h o))
      = f 0
      in
      g
    end;
    Modifies.live_ancestors = (let f _ _ _ = () in f)
  }
  in
  (Modifies.class_invariant_intro s)

let class: Modifies.class HS.class 1 object = class'

let class_eq
  ()
: Lemma
  (requires True)
  (ensures (class == class'))
  [SMTPatOr [[SMTPat class]; [SMTPat class']]]
= ()

let singleton_pointer
  (#t: Type)
  (p: pointer t)
: Tot (TSet.set (Modifies.object HS.class))
= Modifies.singleton class (ObjectPointer p)

let singleton_buffer
  (#t: Type)
  (b: buffer t)
: Tot (TSet.set (Modifies.object HS.class))
= Modifies.singleton class (ObjectBuffer b)
