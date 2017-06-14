// with: --include ulib --include ulib/hyperstack

module FStar.BufferNG
module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStackNG
module HST = FStar.STNG
module P = FStar.Pointer

(* Buffers *)

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

abstract let gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: GTot (buffer t)
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gsingleton_buffer_of_pointer p))
= Buffer (BufferRootSingleton p) 0ul 1ul

abstract let gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: GTot (buffer t)
= Buffer (BufferRootArray p) 0ul length

abstract let buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Stack (buffer t)
  (requires (fun h -> P.live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))
= Buffer (BufferRootArray p) 0ul length

abstract let length
  (#t: Type)
  (b: buffer t)
: GTot UInt32.t
= Buffer?.blength b

abstract let length_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (length (gsingleton_buffer_of_pointer p))]
= ()

abstract let length_gbuffer_of_array_pointer
  (#t: Type)
  (#len: UInt32.t)
  (p: P.pointer (P.array len t))
: Lemma
  (requires True)
  (ensures (length (gbuffer_of_array_pointer p) == len))
  [SMTPat (length (gbuffer_of_array_pointer p))]
= ()

abstract let live
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= match b.broot with
  | BufferRootSingleton p -> P.live h p
  | BufferRootArray #mlen p -> P.live h p

abstract let live_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (h: HS.mem)
: Lemma
  (ensures (live h (gsingleton_buffer_of_pointer p) <==> P.live h p ))
  [SMTPat (live h (gsingleton_buffer_of_pointer p))]
= ()

abstract let live_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (live h (gbuffer_of_array_pointer p) <==> P.live h p))
  [SMTPat (live h (gbuffer_of_array_pointer p))]
= ()

abstract let unused_in
  (#t: Type)
  (b: buffer t)
  (h: HS.mem)
: GTot Type0
= match b.broot with
  | BufferRootSingleton p -> P.unused_in p h
  | BufferRootArray #mlen p -> P.unused_in p h

abstract let unused_in_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (h: HS.mem)
: Lemma
  (ensures (unused_in (gsingleton_buffer_of_pointer p) h <==> P.unused_in p h))
  [SMTPat (unused_in (gsingleton_buffer_of_pointer p) h)]
= ()

abstract let unused_in_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (unused_in (gbuffer_of_array_pointer p) h <==> P.unused_in p h))
  [SMTPat (unused_in (gbuffer_of_array_pointer p) h)]
= ()

abstract let frameOf
  (#t: Type)
  (b: buffer t)
: GTot HH.rid
= match b.broot with
  | BufferRootSingleton p -> P.frameOf p
  | BufferRootArray #mlen p -> P.frameOf p

abstract let frameOf_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (ensures (frameOf (gsingleton_buffer_of_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gsingleton_buffer_of_pointer p))]
= ()

abstract let frameOf_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Lemma
  (ensures (frameOf (gbuffer_of_array_pointer p) == P.frameOf p))
  [SMTPat (frameOf (gbuffer_of_array_pointer p))]
= ()

abstract let memory_managed
  (#t: Type)
  (b: buffer t)
: GTot bool
= match b.broot with
  | BufferRootSingleton p -> P.memory_managed p
  | BufferRootArray #mlen p -> P.memory_managed p

abstract let memory_managed_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (ensures (memory_managed (gsingleton_buffer_of_pointer p) == P.memory_managed p))
  [SMTPat (memory_managed (gsingleton_buffer_of_pointer p))]
= ()

abstract let memory_managed_gbuffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Lemma
  (ensures (memory_managed (gbuffer_of_array_pointer p) == P.memory_managed p))
  [SMTPat (memory_managed (gbuffer_of_array_pointer p))]
= ()

abstract let gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: GTot (buffer t)
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

abstract let sub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Stack (buffer t)
  (requires (fun h -> live h b))
  (ensures (fun h b' h' -> h' == h /\ b' == gsub b i len ))
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

abstract let live_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPat (live h (gsub b i len))]
= ()

abstract let unused_in_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (unused_in (gsub b i len) h <==> unused_in b h))
  [SMTPat (unused_in (gsub b i len) h)]
= ()

abstract let frameOf_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (frameOf (gsub b i len) == frameOf b))
  [SMTPat (frameOf (gsub b i len))]
= ()

abstract let memory_managed_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t {  UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (memory_managed (gsub b i len) == memory_managed b))
  [SMTPat (frameOf (gsub b i len))]
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
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]
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

abstract let as_seq_gsingleton_buffer_of_pointer
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (as_seq h (gsingleton_buffer_of_pointer p) == Seq.create 1 (P.gread h p)))
  [SMTPat (as_seq h (gsingleton_buffer_of_pointer p))]
= Seq.slice_length (Seq.create 1 (P.gread h p))

abstract let as_seq_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: Type)
  (h: HS.mem)
  (p: P.pointer (P.array length t))
: Lemma
  (requires True)
  (ensures (as_seq h (gbuffer_of_array_pointer p) == P.gread h p))
  [SMTPat (as_seq h (gbuffer_of_array_pointer p))]
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

abstract let gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: GTot (P.pointer t)
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

abstract let pointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: Stack (P.pointer t)
  (requires (fun h -> live h b))
  (ensures (fun h p h' -> h' == h /\ p == gpointer_of_buffer_cell b i))
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    P.cell p FStar.UInt32.(Buffer?.bidx b +^ i)

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

abstract let live_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
  (h: HS.mem)
: Lemma
  (ensures (P.live h (gpointer_of_buffer_cell b i) <==> live h b))
  [SMTPat (P.live h (gpointer_of_buffer_cell b i))]
= ()

abstract let unused_in_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
  (h: HS.mem)
: Lemma
  (ensures (P.unused_in (gpointer_of_buffer_cell b i) h <==> unused_in b h))
  [SMTPat (P.unused_in (gpointer_of_buffer_cell b i) h)]
= ()

abstract let frameOf_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: Lemma
  (ensures (P.frameOf (gpointer_of_buffer_cell b i) == frameOf b))
  [SMTPat (P.frameOf (gpointer_of_buffer_cell b i))]
= ()

abstract let memory_managed_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: Lemma
  (ensures (P.memory_managed (gpointer_of_buffer_cell b i) == memory_managed b))
  [SMTPat (P.memory_managed (gpointer_of_buffer_cell b i))]
= ()

abstract let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
  (i: UInt32.t { UInt32.v i < 1 } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i)]
= ()

abstract let gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: UInt32.t)
  (#t: Type)
  (p: P.pointer (P.array length t))
  (i: UInt32.t { UInt32.v i < UInt32.v length } )
: Lemma
  (requires True)
  (ensures (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i == P.gcell p i))
  [SMTPat (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i)]
= ()

abstract let gread_gpointer_of_buffer_cell
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (ensures (P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
  [SMTPat (P.gread h (gpointer_of_buffer_cell b i))]
= ()

abstract let gread_gpointer_of_buffer_cell'
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (ensures (P.gread h (gpointer_of_buffer_cell b i) == Seq.index (as_seq h b) (UInt32.v i)))
= ()

abstract let gread_pointer_of_buffer_cell'
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (Seq.index (as_seq h b) (UInt32.v i) == P.gread h (gpointer_of_buffer_cell b i)))
  [SMTPat (Seq.index (as_seq h b) (UInt32.v i))]
= ()

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)

let read
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: HST.Stack t
  (requires (fun h -> live h b))
  (ensures (fun h v h' -> h' == h /\ v == Seq.index (as_seq h b) (UInt32.v i)))
= P.read (pointer_of_buffer_cell b i)

(* buffer write: needs clearer "modifies" clauses. We could, at first, say that the only memory that is modified is the memory location of the sole cell being modified: *)

let gread
  (#a: Type)
  (h: HS.mem)
  (b: buffer a)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) })
: GTot a
= Seq.index (as_seq h b) (UInt32.v i)

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
    gread h' b i == v
  ))
 = P.write' (pointer_of_buffer_cell b i) v

(* Or, we can also define: *)

abstract
let rec locset_of_buffer_contents
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
    TSet.union (P.locset_of_pointer (gpointer_of_buffer_cell b 0ul)) (locset_of_buffer_contents (gsub b 1ul l'))

private
let rec mem_locset_of_buffer_contents_elim
  (#t: Type)
  (b: buffer t)
  (o: Modifies.loc HS.root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (locset_of_buffer_contents b) ==> (
    exists i . TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i))
  )))
  (decreases (UInt32.v (length b)))
= let l = length b in
  if l = 0ul
  then ()
  else
    let l' = FStar.UInt32.(l -^ 1ul) in
    mem_locset_of_buffer_contents_elim (gsub b 1ul l') o

private
let rec mem_locset_of_buffer_contents_intro
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  (o: Modifies.loc HS.root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i)) ==> TSet.mem o (locset_of_buffer_contents b)))
  (decreases (UInt32.v (length b)))
= let l = length b in
  if l = 0ul
  then ()
  else if i = 0ul
  then ()
  else mem_locset_of_buffer_contents_intro (gsub b 1ul (FStar.UInt32.(l -^ 1ul))) (FStar.UInt32.(i -^ 1ul)) o

abstract
let mem_locset_of_buffer_contents
  (#t: Type)
  (b: buffer t)
  (o: Modifies.loc HS.root_class)
: Lemma
  (requires True)
  (ensures (TSet.mem o (locset_of_buffer_contents b) <==> (
    exists i . TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i))
  )))
  [SMTPat (TSet.mem o (locset_of_buffer_contents b))]
= mem_locset_of_buffer_contents_elim b o;
  Classical.forall_intro (let f i : Lemma (ensures (
    TSet.mem o (P.locset_of_pointer (gpointer_of_buffer_cell b i)) ==> TSet.mem o (locset_of_buffer_contents b)
  ))
  = mem_locset_of_buffer_contents_intro b i o in f)

abstract
let locset_of_buffer_contents_includes_locset_of_pointer_gpointer_of_buffer_cell
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (locset_of_buffer_contents b) (P.locset_of_pointer (gpointer_of_buffer_cell b i))))
  [SMTPat (Modifies.locset_includes (locset_of_buffer_contents b) (P.locset_of_pointer (gpointer_of_buffer_cell b i)))]
= Classical.forall_intro (mem_locset_of_buffer_contents_intro b i)

#reset-options "--z3rlimit 32"

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
    Modifies.modifies (locset_of_buffer_contents b) h h' /\
    gread h' b i == v /\ (
      forall (i': UInt32.t { UInt32.v i' < UInt32.v (length b) } ) .
      i' <> i ==> gread h' b i' == gread h b i'
  )))
 = upd' b i v

abstract
let locset_includes_locset_of_buffer_contents_singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (P.locset_of_pointer p) (locset_of_buffer_contents (gsingleton_buffer_of_pointer p))))
  [SMTPat (Modifies.locset_includes (P.locset_of_pointer p) (locset_of_buffer_contents (gsingleton_buffer_of_pointer p)))]
= ()

private
let rec locset_includes_locset_of_buffer_contents_buffer_of_array_pointer_aux
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
  (i' : UInt32.t)
  (len' : UInt32.t { UInt32.v i' + UInt32.v len' <= UInt32.v length } )
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (P.locset_of_pointer p) (locset_of_buffer_contents (gsub (gbuffer_of_array_pointer p) i' len'))))
  (decreases (UInt32.v len'))
= if len' = 0ul
  then ()
  else let len'' = FStar.UInt32.(len' -^ 1ul) in
       let i'' = FStar.UInt32.(i' +^ 1ul) in
       locset_includes_locset_of_buffer_contents_buffer_of_array_pointer_aux p i'' len''

abstract
let locset_includes_locset_of_buffer_contents_buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (P.locset_of_pointer p) (locset_of_buffer_contents (gbuffer_of_array_pointer p))))
  [SMTPat (Modifies.locset_includes  (P.locset_of_pointer p) (locset_of_buffer_contents (gbuffer_of_array_pointer p)))]
= locset_includes_locset_of_buffer_contents_buffer_of_array_pointer_aux p 0ul length  

abstract
let locset_of_buffer_liveness_tag
  (#t: Type)
  (b: buffer t)
: GTot (Modifies.locset HS.root_class)
= match b.broot with
  | BufferRootSingleton p -> P.locset_of_pointer_liveness_tag p
  | BufferRootArray p -> P.locset_of_pointer_liveness_tag p

abstract
let locset_disjoint_locset_of_buffer_liveness_tag_locset_of_buffer_contents
  (#t1: Type)
  (b1: buffer t1)
  (#t2: Type)
  (b2: buffer t2)
: Lemma
  (requires True)
  (ensures (Modifies.locset_disjoint (locset_of_buffer_contents b1) (locset_of_buffer_liveness_tag b2)))
  [SMTPat (Modifies.locset_disjoint (locset_of_buffer_contents b1) (locset_of_buffer_liveness_tag b2))]
= ()

abstract
let locset_of_buffer_liveness_tag_singleton_buffer_of_pointer
  (#t: Type)
  (p: P.pointer t)
: Lemma
  (requires True)
  (ensures (locset_of_buffer_liveness_tag (gsingleton_buffer_of_pointer p) == P.locset_of_pointer_liveness_tag p))
  [SMTPat (locset_of_buffer_liveness_tag (gsingleton_buffer_of_pointer p))]
= ()

abstract
let locset_of_buffer_liveness_tag_buffer_of_array_pointer
  (#t: Type)
  (#length: UInt32.t)
  (p: P.pointer (P.array length t))
: Lemma
  (requires True)
  (ensures (locset_of_buffer_liveness_tag (gbuffer_of_array_pointer p) == P.locset_of_pointer_liveness_tag p))
  [SMTPat (locset_of_buffer_liveness_tag (gbuffer_of_array_pointer p))]
= ()

abstract
let locset_of_buffer_liveness_tag_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t { UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (locset_of_buffer_liveness_tag (gsub b i len) == locset_of_buffer_liveness_tag b))
  [SMTPat (locset_of_buffer_liveness_tag (gsub b i len))]
= ()

let locset_of_buffer
  (#t: Type)
  (b: buffer t)
: GTot (Modifies.locset HS.root_class)
= TSet.union (locset_of_buffer_contents b) (locset_of_buffer_liveness_tag b)

abstract
let includes
  (#t: Type)
  (b_big b_small: buffer t)
: Tot Type0
= b_big.broot == b_small.broot /\ (
    let b_big_idx = UInt32.v b_big.bidx in
    let b_small_idx = UInt32.v b_small.bidx in (
      b_big_idx <= b_small_idx /\
      b_small_idx + UInt32.v b_small.blength <= b_big_idx + UInt32.v b_big.blength
  ))

let includes_refl
  (#t: Type)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (includes b b))
  [SMTPat (includes b b)]
= ()

let includes_trans
  (#t: Type)
  (b1 b2 b3: buffer t)
: Lemma
  (requires (includes b1 b2 /\ includes b2 b3))
  (ensures (includes b1 b3))
  [SMTPatT (includes b1 b2); SMTPatT (includes b2 b3)]
= ()

let includes_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t { UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (includes b (gsub b i len)))
= ()

abstract
let includes_elim
  (#t: Type)
  (b_big b_small: buffer t)
: Lemma
  (requires (includes b_big b_small))
  (ensures (exists i len . b_small == gsub b_big i len))
= assert (b_small == gsub b_big FStar.UInt32.(b_small.bidx -^ b_big.bidx) b_small.blength)

private
let rec locset_includes_locset_of_buffer_contents_gsub_aux
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t { UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (locset_of_buffer_contents b) (locset_of_buffer_contents (gsub b i len))))
  (decreases (UInt32.v len))
= if len = 0ul
  then ()
  else locset_includes_locset_of_buffer_contents_gsub_aux b FStar.UInt32.(i +^ 1ul) FStar.UInt32.(len -^ 1ul)

abstract
let locset_includes_locset_of_buffer_contents_gsub
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t { UInt32.v i + UInt32.v len <= UInt32.v (length b) } )
: Lemma
  (requires True)
  (ensures (Modifies.locset_includes (locset_of_buffer_contents b) (locset_of_buffer_contents (gsub b i len))))
  [SMTPat (Modifies.locset_includes (locset_of_buffer_contents b) (locset_of_buffer_contents (gsub b i len)))]
= locset_includes_locset_of_buffer_contents_gsub_aux b i len

abstract
let includes_locset_includes_locset_of_buffer_contents
  (#t: Type)
  (b_big b_small: buffer t)
: Lemma
  (requires (includes b_big b_small))
  (ensures (Modifies.locset_includes (locset_of_buffer_contents b_big) (locset_of_buffer_contents b_small)))
  [SMTPatOr [ [ SMTPat (Modifies.locset_includes (locset_of_buffer_contents b_big) (locset_of_buffer_contents b_small)) ] ; [ SMTPatT (includes b_big b_small) ] ] ]
= includes_elim b_big b_small

abstract
let includes_locset_includes_locset_of_buffer
  (#t: Type)
  (b_big b_small: buffer t)
: Lemma
  (requires (includes b_big b_small))
  (ensures (Modifies.locset_includes (locset_of_buffer b_big) (locset_of_buffer b_small)))
//  [SMTPat (Modifies.locset_includes (locset_of_buffer b_big) (locset_of_buffer b_small))]
= assert (Modifies.locset_includes (locset_of_buffer b_big) (locset_of_buffer_contents b_big));
  assert (Modifies.locset_includes (locset_of_buffer b_big) (locset_of_buffer_liveness_tag b_big))
  // FIXME: WHY WHY WHY not automatic?

(* Let's not define disjointness, and use the general definition instead. *)

// FIXME: WHY WHY WHY does the following take SO long to verify?

private
let rec locset_disjoint_gpointer_of_buffer_cell_locset_of_buffer_contents_gsub
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 /\ UInt32.v i2 < UInt32.v (length b)))
  (ensures (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 /\ UInt32.v i2 < UInt32.v (length b)) /\ Modifies.locset_disjoint (P.locset_of_pointer (gpointer_of_buffer_cell b i2)) (locset_of_buffer_contents (gsub b i1 len1)))
  (decreases (UInt32.v len1))
= if len1 = 0ul
  then ()
  else locset_disjoint_gpointer_of_buffer_cell_locset_of_buffer_contents_gsub b FStar.UInt32.(i1 +^ 1ul) FStar.UInt32.(len1 -^ 1ul) i2

private
let rec locset_disjoint_locset_of_buffer_contents_gsub_aux
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v (length b)))
  (ensures (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v (length b) /\ Modifies.locset_disjoint (locset_of_buffer_contents (gsub b i1 len1)) (locset_of_buffer_contents (gsub b i2 len2))))
  (decreases (UInt32.v len2))
= if len2 = 0ul
  then ()
  else let _ = locset_disjoint_gpointer_of_buffer_cell_locset_of_buffer_contents_gsub b i1 len1 i2 in
       locset_disjoint_locset_of_buffer_contents_gsub_aux b i1 len1 (FStar.UInt32.(i2 +^ 1ul)) (FStar.UInt32.(len2 -^ 1ul))
  
abstract
let rec locset_disjoint_locset_of_buffer_contents_gsub
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t { UInt32.v i1 + UInt32.v len1 <= UInt32.v (length b) } )
  (i2: UInt32.t)
  (len2: UInt32.t { UInt32.v i2 + UInt32.v len2 <= UInt32.v (length b) })
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1))
  (ensures (Modifies.locset_disjoint (locset_of_buffer_contents (gsub b i1 len1)) (locset_of_buffer_contents (gsub b i2 len2))))
  [SMTPat (Modifies.locset_disjoint (locset_of_buffer_contents (gsub b i1 len1)) (locset_of_buffer_contents (gsub b i2 len2)))]
= Classical.move_requires (locset_disjoint_locset_of_buffer_contents_gsub_aux b i1 len1 i2) len2;
  Classical.move_requires (locset_disjoint_locset_of_buffer_contents_gsub_aux b i2 len2 i1) len1

let modifies_gread
  (#t: Type)
  (b: buffer t)
  (s: Modifies.locset HS.root_class)
  (h h': HS.mem)
  (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint (locset_of_buffer_contents b) s))
  (ensures (live h b ==> live h' b /\ gread h' b i == gread h b i))
  [ SMTPatT (Modifies.modifies s h h') ; SMTPat (gread h' b i) ] // inspired froj no_upd_lemma_1
= ()

abstract
let modifies_as_seq
  (#t: Type)
  (b: buffer t)
  (s: Modifies.locset HS.root_class)
  (h h': HS.mem)
: Lemma
  (requires (Modifies.modifies s h h' /\ Modifies.locset_disjoint (locset_of_buffer b) s))
  (ensures (live h b ==> live h' b /\ as_seq h' b == as_seq h b))
  [ SMTPatT (Modifies.modifies s h h') ; SMTPat (as_seq h' b) ] // inspired froj no_upd_lemma_1
= assert (Modifies.locset_disjoint (locset_of_buffer_contents b) s);
  let g
    (i: UInt32.t { UInt32.v i < UInt32.v (length b) } )
  : Lemma
    (live h b ==> live h' b /\ gread h' b i == gread h b i)
  = modifies_gread b s h h' i
  in
  let f
    ()
  : Lemma
    (requires (live h b))
    (ensures (live h' b /\ as_seq h' b == as_seq h b))
  =
    assert (live h' b);
    let u : squash (forall (i: UInt32.t { UInt32.v i < UInt32.v (length b) } ) . gread h' b i == gread h b i) =
      Classical.forall_intro g
    in
    let v : squash (forall (i: nat { i < UInt32.v (length b) } ) . Seq.index (as_seq h' b) i == Seq.index (as_seq h b) i) =
      assert (forall (i: nat { i < UInt32.v (length b) } ) . Seq.index (as_seq h' b) i == gread h' b (UInt32.uint_to_t i));
      assert (forall (i: nat { i < UInt32.v (length b) } ) . Seq.index (as_seq h b) i == gread h b (UInt32.uint_to_t i));
      ()
    in
    Seq.lemma_eq_intro (as_seq h' b) (as_seq h b);
    Seq.lemma_eq_elim (as_seq h' b) (as_seq h b)
  in
  Classical.move_requires f ()

abstract
let locset_live_locset_of_buffer_liveness_tag
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (ensures (Modifies.locset_live h (locset_of_buffer_liveness_tag b) <==> live h b))
= ()

abstract
let locset_live_locset_of_buffer
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (ensures (Modifies.locset_live h (locset_of_buffer b) <==> live h b))
= ()

abstract
let locset_live_locset_of_buffer_contents
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (live h b))
  (ensures (Modifies.locset_live h (locset_of_buffer_contents b)))
= ()

abstract
let locset_dead_locset_of_buffer_liveness_tag
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (ensures (Modifies.locset_dead h (locset_of_buffer_liveness_tag b) <==> b `unused_in` h))
= Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer_liveness_tag #t)

abstract
let locset_dead_locset_of_buffer
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (ensures (Modifies.locset_dead h (locset_of_buffer b) <==> b `unused_in` h))
= Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer_liveness_tag #t);
  Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer #t)

abstract
let locset_dead_locset_of_buffer_contents
  (#t: Type)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (b `unused_in` h))
  (ensures (Modifies.locset_dead h (locset_of_buffer_contents b)))
= Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer #t)

(* Allocators *)

abstract
val create: #a:Type -> init:a -> len:UInt32.t -> StackInline (buffer a)
  (requires (fun h -> True))
  (ensures (fun (h0: HS.mem) b h1 -> b `unused_in` h0
     /\ live h1 b /\ length b = len
     /\ frameOf b = h0.HS.tip
     /\ Modifies.modifies u#1 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h0 h1
     /\ Modifies.locset_dead h0 (locset_of_buffer b)
     /\ as_seq h1 b == Seq.create (UInt32.v len) init))
let create #a init len =
  let h0 = HST.get () in
  let content: Pointer.pointer (Pointer.array len a) =
    Pointer.screate' (Seq.create (UInt32.v len) init)
  in
  let b = buffer_of_array_pointer content in  
  let _ : squash (Modifies.locset_dead h0 (locset_of_buffer b)) =
    Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer_with_liveness #t)
  in
  b

abstract
val rcreate: #a:Type -> r:HH.rid -> init:a -> len:UInt32.t -> ST (buffer a)
  (requires (fun h -> HS.is_eternal_region r))
  (ensures (fun (h0: HS.mem) b h1 -> b `unused_in` h0
    /\ live h1 b /\ length b = len
    /\ Modifies.modifies u#1 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h0 h1
    /\ Modifies.locset_dead h0 (locset_of_buffer b)
    /\ as_seq h1 b == Seq.create (UInt32.v len) init
    /\ ~ (memory_managed b)
  ))
let rcreate #a r init len =
  let h0 = HST.get() in
  let s = Seq.create (UInt32.v len) init in
  let content: Pointer.pointer (Pointer.array len a) =
    Pointer.ecreate' r s
  in
  let b = buffer_of_array_pointer content in
  let _ : squash (Modifies.locset_dead h0 (locset_of_buffer b)) =
    Classical.forall_intro_3 (fun t -> Pointer.locset_dead_locset_of_pointer_with_liveness #t)
  in
  b
