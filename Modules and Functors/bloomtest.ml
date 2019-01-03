open Bloom
(* Instantiate a BloomFilter module, BloomSparseInt by using SparseSet and IntHash from the bloom.ml *)
module BloomSparseInt = BloomFilter (SparseSet) (IntHash)
(* Instantiate a BloomFilter module, BloomBoolInt by using BoolSet and IntHash from the bloom.ml *)
module BloomBoolInt = BloomFilter (BoolSet) (IntHash)

(* Creating a list of 200 random integers. The range of the integers is 0 to 2^30 - 1. To get the random integers in the given range, I used the Random.int to make it work. *)
let insert_ilist =
  let rec create i lst = match i with
  | 0 -> lst
  | n -> create (n-1) (Random.int (1 lsl 30 -1)::lst)
  in create 200 []

(* Creating sparseInt using the module BloomSparseInt. *)
let create_sparseInt lst =
  let rec h1 r lst = match lst with
  | [] -> r
  | h::t -> h1 (BloomSparseInt.add h r) t
  in h1 BloomSparseInt.empty lst

(* Getting the time for creation of sparseInt. I used the Sys.time () to get the time for it *)
let sparseInt_t, bloomSparseInt =
  let t1 = Sys.time () in let x = create_sparseInt insert_ilist in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating boolInt using the module BloomBoolInt *)
let create_boolInt lst =
  let rec h2 r lst = match lst with
  | [] -> r
  | h::t -> h2 (BloomBoolInt.add h r) t
  in h2 BloomBoolInt.empty lst

(* Getting the time for creation of boolInt. I used the Sys.time () to get the time for it *)
let boolInt_t, bloomBoolInt =
  let t1 = Sys.time () in let x = create_boolInt insert_ilist in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating a list of 1000000 random integers. The range of the integers is 0 to 2^30 - 1. To get the random integers in the given range, I used the Random.int to make it work. *)
let test_ilist =
  let rec create i lst = match i with
  | 0 -> lst
  | n -> create (n-1) (Random.int (1 lsl 30 -1)::lst)
  in create 1000000 []

(* Creating the test_sparseInt using BloomSparseInt.mem while counting false positives as well. *)
let test_sparseInt lst bloom =
  let rec h1 r lst = match lst with
  | [] -> r
  | h::t -> if (BloomSparseInt.mem h bloom) then h1 (r+1) t else h1 r t
  in h1 0 lst

(* Getting the time for testing each element of test_ilist. I used the Sys.time () to get the time for it. This case is time for the sparseInt *)
let sparseInt_test_t, false_sparseInt =
  let t1 = Sys.time () in let x = test_sparseInt test_ilist bloomSparseInt in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating the test_boolInt using BloomBoolInt.mem while counting false positives as well. *)
let test_boolInt lst bloom =
  let rec h1 r lst = match lst with
  | [] -> r
  | h::t -> if (BloomBoolInt.mem h bloom) then h1 (r+1) t else h1 r t
  in h1 0 lst

(* Getting the time for testing each element of test_ilist. I used the Sys.time () to get the time for it. This case is time for the boolInt *)
let boolInt_test_t, false_boolInt =
  let t1 = Sys.time () in let x = test_boolInt test_ilist bloomBoolInt in
  let t2 = Sys.time () in t2 -. t1, x

(* Instantiate BloomFilter module, BloomSparseString by using SparseSet and StringHash from the bloom.ml *)
module BloomSparseString = BloomFilter (SparseSet) (StringHash)
(* Instantiate BloomFilter module, BloomBoolString by using BoolSet and StringHash from the bloom.ml *)
module BloomBoolString = BloomFilter (BoolSet) (StringHash)

(* insert_slist, which read the list of 2048 most visited website from the file top-2k.txt. I used the similar format from the previous homework for reading, opening the file *)
let insert_slist =
  let in_file = open_in "top-2k.txt" in
  let rec loop acc =
    let next_line = try Some(input_line in_file) with End_of_file -> None in
    match next_line with
    | (Some l) -> loop (l::acc)
    | (None) -> acc
    in
    let lines = try List.rev (loop []) with _ -> [] in
    let () = close_in in_file in
    lines

(* test_slist, which read the list of top 1000000 - 2048 most visited webstie from the file top-1m.txt. I used the similar format from the previous homework for reading, opening the file *)
let test_slist =
  let in_file = open_in "top-1m.txt" in
  let rec loop acc =
    let next_line = try Some(input_line in_file) with End_of_file -> None in
    match next_line with
    | (Some l) -> loop (l::acc)
    | (None) -> acc
    in
    let lines = try List.rev (loop []) with _ -> [] in
    let () = close_in in_file in
    lines

(* Creating the sparseString by using module BloomSparseString and calling from_list from there *)
let create_sparseString = BloomSparseString.from_list

(* Getting the time for creation of sparseString from insert_slist. I used the Sys.time () to get the time for it.  *)
let sparseString_t, bloomSparseString =
  let t1 = Sys.time () in let x = create_sparseString insert_slist in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating the boolString by using module BloomBoolString and calling from_list from there *)
let create_boolString = BloomBoolString.from_list

(* Getting the time for creation of boolString from insert_slist. I used the Sys.time () to get the time for it *)
let boolString_t, bloomBoolString =
  let t1 = Sys.time () in let x = create_boolString insert_slist in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating test_sparseString by using BloomSparseString.mem and counting the number of false positives as well. *)
let test_sparseString lst bloom =
  let rec h1 r lst = match lst with
  | [] -> r
  | h::t -> if (BloomSparseString.mem h bloom) then h1 (r+1) t else h1 r t
  in h1 0 lst

(* Getting the time for testing each string in test_slist. I used the Sys.time () to get the time for it. This case is for sparseString. *)
let sparseString_test_t, false_SparseString =
  let t1 = Sys.time () in let x = test_sparseString test_slist bloomSparseString in
  let t2 = Sys.time () in t2 -. t1, x

(* Creating test_boolString by using BloomBoolString.mem and counting the number of false positives as well. *)
let test_boolString lst bloom =
  let rec h1 r lst = match lst with
  | [] -> r
  | h::t -> if (BloomBoolString.mem h bloom) then h1 (r+1) t else h1 r t
  in h1 0 lst

(* Getting the time for testing each string in test_slist. I used the Sys.time () to get the time for it. This cas is for boolString. *)
let boolString_test_t, false_BoolString =
  let t1 = Sys.time () in let x = test_boolString test_slist bloomBoolString in
  let t2 = Sys.time () in t2 -. t1, x;;

(* For formatting, I used the sample example from the instruction, such as spacing, and printing out the name. *)
(* Printing out the build time, test time, false positive counts by using the Printf. This case is time for SparseInt *)
Printf.printf "SparseInt      : build time =   %fs test time =   %fs false positives = %d\n" sparseInt_t  sparseInt_test_t  false_sparseInt;;
(* Printing out the build time, test time, false positive counts by using the Printf. This case is time for BoolInt *)
Printf.printf "BoolInt        : build tile =   %fs test time =   %fs false positives = %d\n" boolInt_t 	 boolInt_test_t  false_boolInt;;
(* Printing out the build time, test time, false positive counts by using the Printf. This case is time for SparseString *)
Printf.printf "SparseString   : build time =   %fs test time =   %fs false positives = %d\n" sparseString_t  sparseString_test_t  false_SparseString;;
(* Printing out the build time, test time, false potitive counts by using the Printf. This case is time for BoolString *)
Printf.printf "BoolString     : build time =   %fs test time=    %fs false positives = %d\n" boolString_t  boolString_test_t  false_BoolString;;
