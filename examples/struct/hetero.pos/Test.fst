module Test

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HS = FStar.HyperStackNG
module HST = FStar.ST

#reset-options "--z3rlimit 32"

let test0
  (r: HS.reference int)
: Stack unit
  (requires (fun h ->
    HS.contains h r
  ))
  (ensures (fun h _ h' ->
    HS.modifies' (HS.locset_of_reference r) h h' /\
    HS.contains h' r /\
    HS.sel h' r == 18
  ))
= r := 18

let test
  (r: HS.reference int)
  (p: S.pointer bool)
: Stack unit
  (requires (fun h ->
    Modifies.locset_disjoint (S.locset_of_pointer p) (HS.locset_of_reference r) /\
    HS.contains h r /\
    S.live h p
  ))
  (ensures (fun h _ h' ->
    HS.modifies' (TSet.union (S.locset_of_pointer p) (HS.locset_of_reference r)) h h' /\
    HS.contains h' r /\
    S.live h' p /\
    S.gread h' p == true /\
    HS.sel h' r == 18
  ))
= S.write' p true;
  r := 18;
  ()
