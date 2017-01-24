module FStar.Integers
#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"

open FStar.Mul
open FStar.BitVector
open FStar.Math.Lemmas

type signed = 
  | Signed
  | Unsigned

let max_int (s: signed) (n: pos): Tot int =
  match s with
  | Signed -> pow2 (n - 1) - 1
  | Unsigned -> pow2 n - 1

let min_int (s: signed) (n: pos): Tot int =
  match s with
  | Signed -> - (pow2 (n - 1))
  | Unsigned -> 0

let fits (s: signed) (n: pos) (x: int) = min_int s n <= x && x <= max_int s n

let size (s:signed) (n: nat) (x:int) = 
  match  n with 
  | 0 -> True
  | _ -> b2t (fits s n x)

private type boxed_int (s: signed) (n: pos) = | Mk : v : (x : int {size s n x}) -> boxed_int s n

val int_t (s: signed) (n: nat) : Tot Type0
let int_t s n =
  match s, n with
  | Signed, 0 -> int
  | Unsigned, 0 -> nat
  | _, _ -> boxed_int s n

let v (#s:signed) (#n:nat) (x:int_t s n) : Tot (y:int_t Signed 0{size s n y}) =
  match s, n with
  | Signed, 0 -> x
  | Unsigned, 0 -> (x <: nat)
  | _, _ -> Mk?.v #s #n x

let v_inj (#s : signed) (#n : nat) (x y : int_t s n) : Lemma
  (requires (v x = v y))
  (ensures (x = y))
  = ()

unfold let ok (s:signed) (n:nat) (x:int) =
  match s, n with
  | Signed, 0 -> True
  | Unsigned, 0 -> b2t (x >= 0)
  | _, _ -> size s n x

private let mk (s: signed) (n: nat) (x: int) : Pure (int_t s n)
  (requires (ok s n x))
  (ensures  (fun y -> v y = x))
  = match n with
    | 0 -> x
    | _ -> Mk #s #n x

private unfold let underspec (s: signed) (n: pos) (c: int) : Tot (boxed_int s n) =
   if fits s n c then Mk c else magic ()
  
let op_Plus_Question (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n)
  : Pure (int_t s n)
    (requires True)
    (ensures (fun z -> ok s n (v x + v y) ==> v z = v x + v y))
  = match n with
    | 0 -> x + y
    | _ -> underspec s n (v x + v y)

let op_Plus (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n)
  : Pure (int_t s n)
    (requires (ok s n (v x + v y)))
    (ensures (fun z -> v z = v x + v y))
  = mk s n (v x + v y)

// 'Circular modulo operator : wraps into [-p/2; p/2[
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m

let modulo (s:signed) (x:int) (y:pos{s=Signed ==> y%2=0}) =
  match s with 
  | Unsigned ->  x % y
  | _ -> x @% y

#reset-options "--max_fuel 20"

let op_Plus_Percent (#s:signed) (#n:pos) (x:int_t s n) (y:int_t s n)
  : Tot (z:int_t s n  {v z = modulo s (v x + v y) (pow2 n)}  )
  =
    Mk #s #n (modulo s (v x + v y) (pow2 n))

let op_Subtraction_Question (#s:signed) (#n:nat) (x:int_t s n) (y:int_t s n)
  : Tot (z:int_t s n{ok s n (v x - v y) ==> v z = v x - v y})
  =
    match s, n with
    | Signed, 0 -> x - y
    | Unsigned, 0 -> if x - y >= 0 then x - y else 0
    | _, _ -> underspec s n (v x - v y)

let op_Subtraction (#s:signed) (#n:nat) (x y:int_t s n) :
  Pure (int_t s n)
  (requires (ok s n (v x - v y)))
  (ensures (fun z -> v z = v x - v y))
  = mk s n (v x - v y)

let op_Subtraction_Percent (#s:signed) (#n:pos) (x:int_t s n) (y:int_t s n)
  : Tot (z:int_t s n{v z = modulo s (v x - v y) (pow2 n)})
  = Mk #s #n (modulo s (v x - v y) (pow2 n))

let op_Star_Question (#s: signed) (#n: nat) (x y: int_t s n)
  : Tot (z: int_t s n { ok s n (v x * v y) ==> v z = v x * v y } )
  =
   match n with
   | 0 -> x * y
   | _ -> underspec s n (v x * v y)

let op_Star (#s : signed) (#n : nat) (x y : int_t s n)
  : Pure (int_t s n)
    (requires (ok s n (v x * v y)))
    (ensures (fun z -> v z = v x * v y))
  = mk s n (v x * v y)

let op_Star_Percent (#s:signed) (#n:pos) (x:int_t s n) (y:int_t s n)
  : Tot (z:int_t s n{v z = modulo s (v x * v y) (pow2 n)})
  = Mk #s #n (modulo s (v x * v y) (pow2 n))

#reset-options "--z3rlimit 100  --max_fuel 10 --max_ifuel 10"

let plus_assoc_l (#s: signed) (#n: nat) (x y z : int_t s n) : Pure (int_t s n)
  (requires (ok s n (v x + v y) /\ ok s n (v (x + y) + v z)))
  (ensures (fun _ -> True))
  = (x + y) + z

let plus_assoc_r (#s: signed) (#n: nat) (x y z : int_t s n) : Pure (int_t s n)
  (requires (ok s n (v y + v z) /\ ok s n (v x + v (y + z))))
  (ensures (fun _ -> True))
  = x + (y + z)

let plus_assoc_precond  (#s: signed) (#n: nat) (x y z : int_t s n) : Tot Type0 =
  (ok s n (v x + v y) /\ ok s n (v (x + y) + v z) /\ ok s n (v y + v z) /\ ok s n (v x + v (y + z)))

let plus_assoc_stmt  (#s: signed) (#n: nat) (x y z : int_t s n) : Pure Type0
  (requires (plus_assoc_precond x y z))
  (ensures (fun _ -> True))
  = (plus_assoc_l x y z = plus_assoc_r x y z)

(* NOTE: the following fails to typecheck:

assume val plus_assoc (#s: signed) (#n: nat) (x y z : int_t s n) : Lemma
  (requires (plus_assoc_precond x y z))
  (ensures (plus_assoc_stmt x y z))

However, the following works:
*)

let plus_assoc (#s: signed) (#n: nat) (x y z : int_t s n) (u : unit {(plus_assoc_precond x y z) } ) : Lemma
  (ensures (plus_assoc_stmt x y z))
  =
  ()


(*
#reset-options "--z3rlimit 5"

#reset-options "--z3rlimit 20"

#reset-options "--z3rlimit 5"

#reset-options "--z3rlimit 20"

#reset-options "--z3rlimit 5"
*)

unfold let nat      = int_t Unsigned 0
unfold let uint_8   = int_t Unsigned 8
unfold let uint_16  = int_t Unsigned 16
unfold let uint_31  = int_t Unsigned 31
unfold let uint_32  = int_t Unsigned 32
unfold let uint_63  = int_t Unsigned 63
unfold let uint_64  = int_t Unsigned 64
unfold let uint_128 = int_t Unsigned 128

unfold let int      = int_t Signed 0
unfold let int_8   = int_t Signed 8
unfold let int_16  = int_t Signed 16
unfold let int_31  = int_t Signed 31
unfold let int_32  = int_t Signed 32
unfold let int_63  = int_t Signed 63
unfold let int_64  = int_t Signed 64
unfold let int_128 = int_t Signed 128
let ok_for (#s:signed) (#n:nat) ($x:int_t s n) (i:int) = ok s n i
////////////////////////////////////////////////////////////////////////////////
//Test
////////////////////////////////////////////////////////////////////////////////
let f_int (x:int) (y:int) = x + y
let f_nat (x:nat) (y:nat) = x + y
let f_uint_8 (x:uint_8) (y:uint_8{ok_for x (v x + v y)}) = x + y
let f_int_16 (x:int_16) (y:int_16{ok_for x (v x + v y)}) = x + y
let g (x:uint_32) (y:uint_32{ok_for x (v y * v y) /\ ok_for x (v x + v y * v y)}) = x + y * y

(* TODO: A bit boring ... *)
(* let op_Slash_Hat = div *)
(* let op_Percent_Hat = rem *)
(* let op_Hat_Hat = logxor *)
(* let op_Amp_Hat = logand *)
(* let op_Bar_Hat = logor *)
(* let op_Less_Less_Hat = shift_left *)
(* let op_Greater_Greater_Hat = shift_right *)
(* let op_Equals_Hat = eq *)
(* let op_Greater_Hat = gt *)
(* let op_Greater_Equals_Hat = gte *)
(* let op_Less_Hat = lt *)
(* let op_Less_Equals_Hat = lte *)
