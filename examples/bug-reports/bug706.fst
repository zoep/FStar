module FStar.Bug706

(* NOTE: Move the file to FStar.Bug706.fst before running, or
 * you will hit bug #705 *)

(* Define an effect via DM4F *)
let exnst h a = h -> M (option (a * h))

val return : (h:Type) -> (a:Type) -> (x:a) -> exnst h a
let return h a x = fun s -> Some (x, s)

val bind : (h:Type) -> (a:Type) -> (b:Type) ->
           (f:exnst h a) -> (g:a -> exnst h b) -> exnst h b
let bind h a b f g =
  fun s0 ->
    let res = f s0 in
    match res with
    | None -> None
    | Some (ret, s1) -> g ret s1

reifiable reflectable new_effect_for_free {
  EXNST (h:Type): a:Type -> Effect with
    repr    = exnst h;
    bind    = bind h;
    return  = return h
}

(* This fails *)
new_effect EXNST_int = EXNST int

(* This works *)
// reifiable reflectable new_effect_for_free {
//   EXNST_int : a:Type -> Effect with
//     repr    = exnst int;
//     bind    = bind int;
//     return  = return int 
// }
