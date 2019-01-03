module type memset = sig
    type elt (* type of values stored in the set *)
    type t (* abstract type used to represent a set *)
    val mem : elt -> t -> bool
    val empty : t
    val is_empty : t -> bool
    val add : elt -> t -> t
    val from_list : elt list -> t
    val union : t -> t -> t
    val inter : t -> t -> t
  end

(* Define the hashparam signature here *)
(* Adding a signature to provide an element type t and function hashes : t -> int list *)
module type hashparam = sig
  type t
  val hashes : t -> int list
end

(* Define SparseSet module here, using the Set.Make functor *)
(* Defining a module SparseSet that use the Set.Make to implement the memset interface which type is int. *)
module SparseSet : memset with type elt = int = struct
  include (Set.Make (struct type t = int
  let compare = Pervasives.compare end))
  let from_list l = (List.fold_left (fun acc x -> add x acc) empty l)
end

(* Fill in the implementation of the memset signature here.  You'll need to expose the elt type *)
(* BoolSet module. I changed the module declaration to impose the memset signature and expose to elt type. And added helper function for &@. And than aonther helper function, make_arr_t which type is int -> bool array. And than I wrote all definitions of the memset signature, which is empty, is_empty, mem, add, union, inter, from_list. *)
module BoolSet : memset with type elt = int and type t = bool array = struct
    type elt = int
    type t = bool array
    (* element-wise or of two arrays: *)
    let rec (|@) s1 s2 = let (short,long) =
      if (Array.length s1 < Array.length s2) then (s1,s2) else (s2,s1) in
      Array.mapi (fun i li -> if i < (Array.length short) then li || short.(i) else li) long
    let rec (&@) s1 s2 = let (short, long) =
      if (Array.length s1 < Array.length s2) then (s1,s2) else (s2,s1) in
      Array.mapi (fun i li -> if i < (Array.length short) then li && short.(i) else li) long
    let rec make_arr_t i = Array.append (Array.make i false) [|true|]
    let rec mem i s = if (i > Array.length s) then (false) else s.(i)
    let empty = Array.make 0 false
    let is_empty s = s = Array.make 0 false
    let add i s = (make_arr_t i) |@ s
    let from_list l = (List.fold_left (fun acc x -> add x acc) empty l)
    let union s1 s2 = s1 |@ s2
    let inter s1 s2 = s1 &@ s2
  end


(* Fill in the implementation of a BloomFilter, matching the memset signature, here. *)
(* You will need to add some sharing constraints to the signature below. *)
(* BloomFilter module. I made the module declaration to impose the memset signature and expose to elt type. *)
module BloomFilter(S : memset with type elt = int)(H : hashparam) : memset with type elt = H.t and type t = S.t = struct
    type elt = H.t
    type t = S.t
    (* Implement the memset signature: *)
    let mem h s = List.fold_left (fun r x -> (S.mem x s) && r) true (H.hashes h)
    let empty = S.empty
    let is_empty s = S.is_empty s
    let add h s = List.fold_left (fun r x -> S.add x r) s (H.hashes h)
    let from_list l = (List.fold_left (fun acc x -> add x acc) empty l)
    let union s1 s2 = S.union s1 s2
    let inter s1 s2 = S.inter s1 s2
  end

(* A hashparam module for strings... *)
module StringHash = struct
    type t = string (* I hash values of type string *)
    let hlen = 15
    let mask = (1 lsl hlen) - 1
    let hashes s =
      let rec hlist n h = if n = 0 then [] else (h land mask)::(hlist (n-1) (h lsr hlen)) in
      hlist 4 (Hashtbl.hash s)
  end

(* Add the IntHash module here *)
(* IntHash module, satisfying the hashparam. type t in int and listing h1 h2 h3. I listed all of the h1 h2 h3 defined in the instruction and made let expression to make it evaluate. *)
module IntHash = struct
  type t = int
  let h_1 n = (795*n + 962) mod 1031
  let h_2 n = (386*n + 517) mod 1031
  let h_3 n = (937*n + 693) mod 1031
  let hashes n = [h_1 n; h_2 n; h_3 n]
end
