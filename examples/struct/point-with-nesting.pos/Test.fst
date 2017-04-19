module Test

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HST = FStar.ST

type point_fd =
| X
| Y

let point_struct = DM.t point_fd (function
| X -> int
| Y -> int
)

let point = S.pointer point_struct

type colored_object_fd =
| Carrier
| Color

let colored_object_struct (t: Type) = DM.t colored_object_fd (function
| Carrier -> t
| Color -> bool
)

let colored_object (t: Type) = S.pointer (colored_object_struct t)

let colored_point = colored_object point_struct

// The following is necessary for Z3 4.5.0, but not for Z3 trunk
// (0c4b792dac261faa3b28f30193afc4b8700e4435) which only needs 32
#reset-options "--z3rlimit 64"

let flip
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ Modifies.modifies (S.locset_of_pointer p) h0 h1
    /\ S.gread h1 (S.gfield (S.gfield p Carrier) X) == S.gread h0 (S.gfield (S.gfield p Carrier) Y)
    /\ S.gread h1 (S.gfield (S.gfield p Carrier) Y) == S.gread h0 (S.gfield (S.gfield p Carrier) X)
    /\ S.gread h1 (S.gfield p Color) == not (S.gread h0 (S.gfield p Color))
    ))
= let pt = S.field p Carrier in
  let x = S.read (S.field pt X) in
  let y = S.read (S.field pt Y) in
  let color = S.read (S.field p Color) in
  S.write' (S.field pt X) y;
  S.write' (S.field pt Y) x;
  S.write' (S.field p Color) (not color)

// The following is necessary for Z3 4.5.0, but not for Z3 trunk
// (0c4b792dac261faa3b28f30193afc4b8700e4435)
#reset-options "--z3rlimit 256"

let flip'
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ Modifies.modifies (S.locset_of_pointer p) h0 h1
    /\ S.gread h1 (S.gfield (S.gfield p Carrier) X) == S.gread h0 (S.gfield (S.gfield p Carrier) Y)
    /\ S.gread h1 (S.gfield (S.gfield p Carrier) Y) == S.gread h0 (S.gfield (S.gfield p Carrier) X)
    /\ S.gread h1 (S.gfield p Color) == not (S.gread h0 (S.gfield p Color))
    ))
= let pt = S.field p Carrier in
  let x = S.read (S.field pt X) in
  let y = S.read (S.field pt Y) in
  S.write' (S.field pt X) y;
  S.write' (S.field pt Y) x;
  let color = S.read (S.field p Color) in
  S.write' (S.field p Color) (not color)
