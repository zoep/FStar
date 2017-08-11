(* We give an implementation here using OCaml's BatList,
   which provide tail-recursive versions of most functions *)
let isEmpty l = l = []
let hd = BatList.hd
let tail = BatList.tl
let tl = BatList.tl
let length l = Z.of_int (BatList.length l)
let nth l i = try Some (BatList.nth l (Z.to_int i)) with _ -> None
let index l i = BatList.nth l (Z.to_int i)
let count _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: count"
let rev_acc _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: rev_acc"
let rev = BatList.rev
let append = BatList.append
let op_At = append
let flatten = BatList.flatten
let map = BatList.map
let mapi_init _ _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: mapi_init"
let mapi f l = BatList.mapi (fun i x -> f (Z.of_int i) x) l
let concatMap f l = BatList.concat (List.map f l)
let fold_left = BatList.fold_left
let fold_right = BatList.fold_right
let fold_left2 = BatList.fold_left2
let mem = BatList.mem
type ('a, 'b, 'c) memP = unit
let contains x l = BatList.exists (fun y -> x = y) l
let existsb f l = BatList.exists f l
let find f l = try Some (BatList.find f l) with | Not_found -> None
let filter = BatList.filter
let for_all = BatList.for_all
let collect f l = BatList.flatten (BatList.map f l)
let tryFind = find
let tryPick f l = try f (BatList.find (fun x -> f x <> None) l) with | Not_found -> None
let choose = BatList.filter_map
let partition = BatList.partition
let subset _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: subset"
let noRepeats _ = failwith "FStar_List_Tot_Base.ml: Not implemented: noRepeats"
let assoc _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: assoc"
let split = BatList.split
let unzip = split
let rec unzip3 = function
  | [] -> ([],[],[])
  | (x,y,z)::xyzs ->
     let (xs,ys,zs) = unzip3 xyzs in
     (x::xs,y::ys,z::zs)
let bool_of_compare _ _ _ = failwith "FStar_List.Tot.Base.ml: Not implemented: bool_of_compare"
let compare_of_bool _ _ _ = failwith "FStar_List.Tot.Base.ml: Not implemented: compare_of_bool"
let sortWith f l = BatList.sort (fun x y -> Z.to_int (f x y)) l
