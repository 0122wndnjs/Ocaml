open SimUtil

(* Your code goes here: *)

(* Define the function that filters out non-alphabetic characters *)
let filter_chars s = String.map(fun character -> 
if ((character >= 'a' && character <= 'z') || (character >= 'A' && character <= 'Z')) then character else ' ') s
(* by using the String.map, this will detect the non-alphabetic characters, such as numbers or
some symbols as given in the feedback file, this will turn those to the space.*)

(* Define the function that converts a string into a list of words *)
let words s =
  let s0 = filter_chars s in
  let s1 = split_words s0 in
  let s2 = List.fold_left (fun accum x -> if not (String.contains x ' ') then x::accum else accum) [] s1 in
  List.rev(s2)
(* This will call the filter_chars and the split_words that was written before and use the List.fold_left tp define the function to
convert a string into a list of words. *)

(* Define the function that converts a list of strings into a list of word lists*)
let wordlists ls= List.map(words) ls
(* This is the function that has bytes list -> bytes list list and it converts the string list to list of the wordlist. It use the
List.map function and calls the words function that I used in previous step.*)

(* Use Stemmer.stem to convert a list of words into a list of stems *)
let stemlist ws = List.map (Stemmer.stem) ws
(* This is the function that has the type bytes list -> bytes list and it converts a list of words in to stem list by using 
Stemmer.stem. I simply used the List.map and called the Stemmer.stem to make utilize of Stemmer.stem.*)

(* Define a function to convert a list into a set *)
let to_set lst =
  let set = List.fold_left (fun accum x -> if List.mem x accum then accum else x::accum) [] lst in
  List.rev(set)
(* This is the function that has 'a list -> 'a list and it convert a list to a set. I used List.fold_left and in the function,
I used List.mem to see if it's a member. So by using this function, to_set ["a"; "b"; "a" ; "b"], it will show 
["a"; "b"] as you can see in the feedback file.*)

(* Define the similarity function between two sets: size of intersection / size of union *)
let intersection_size s1 s2 = List.fold_left(fun accum x -> if List.mem x s1 then accum+1 else accum) 0 s2
(* This function has the type 'a list -> 'a list -> int and it gets the size of the intersection. I used the List.fold_left and
by following the code, this will get the intersection size of the two sets of list. So as the shown example, if I type 
intersection_size ["a"; "b"] ["a"], than it will show 1, which is the int since ["a"; "b"] and ["a"] has common element of ["a"]
and its size is 1. *)

let union_size s1 s2 = (List.length s1) + (List.length s2) - (intersection_size s1 s2)
(* This function has the type 'a list -> 'a list -> int as well as intersection_size and it gets the size of the union. I simply
used the definition of the union, which is adding a set 1 (s1) and set 2 (s2) and subtracting the intersection of s1 and s2. I 
already made the function for getting intersection_size so that made me possible to make this union_size function like this. 
So if I type union_size ["a"; "b"] ["a"], than output will be 2 since add ["a"; "b"] and ["a"] than subtract the intersection part
and it will have 2 size of set that the output would be 2 in int. *)

let similarity s1 s2 = (float_of_int (intersection_size s1 s2)) /. (float_of_int (union_size s1 s2))
(* This is the function that gets the similarity of 2 sets. It has a type of 'a list -> 'a list -> float. To get the function,
I changed int to float by using float_of_int since intersection_size and union_size has type of int and by using those 2 functions,
I divided intersection_size by union_size. If I type similarity ["a"; "b"] ["a"], the output is 0.5 since 1. /. 2. *)

(* Find the most similar representative file *)
let find_max repsims repnames = List.fold_left max (0.,"") (List.combine repsims repnames)
(* This is the function that find the name and similarity of file that is closest to the target document. It has the type of 
float list -> string list -> float*string. I used the List.fold_left and than max, which is the built in function on tuple orders.
And then, I used the List.combine to combine the arguments that is listed. *)

let main all replist_name target_name =
  (* Read the list of representative text files *)
  let repfile_list = file_lines replist_name in
  (* This repfile_list use the file_lines from the simUtil and it gets the list of file name stored in replist_name argument *)

  (* Get the contents of the repfiles and the target file as strings *)
  let rep_contents = List.map (file_as_string) repfile_list in
  (* Thie rep_contents use the List.map and bound to a list of string. And this contains the string contents of the each file. *)
  let target_contents = file_as_string target_name in
  (* This target_contents use the file_as_string since the simUtil is string -> string type that is given. And it is bound to the
  contents of the file that is targeted*)

  (* Compute the list of words from each representative *)
  let rep_words = wordlists rep_contents in
  (* This rep_words is bound to a list of list of words so I used the wordlists and since this is also bounded to a each text files,
  I used the rep_contents that contains the string contents of the file. *)

  (* Convert the target text file into a list of words *)
  let target_words = words target_contents in
  (* This target_words is bound to a list of the words in target file so I used the words and since it is in target file, I used
  target_contents that bounds to contents of the file targeted.*)

  (* Compute the lists of stems in all rep files and the target file *)
  let rep_stemlists = List.map (fun x -> List.map (fun y -> Stemmer.stem y) x) rep_words in
  (* Thie rep_stemlists is bounded to a string list list. I used List.map and also Stemmer.stem to utilize the stem since string list
  is the list of the stems in the file and the rep_stemlists is bounded. *)
  let target_stemlist = List.map (fun x -> Stemmer.stem x) target_words in
  (* This target_stemlist is the target file's stem list. I also used the Stemmer.stem as it works. And this compute the lists of 
  stems in target file*)

  (* Convert all of the stem lists into stem sets *)
  let rep_stemsets = List.map(fun x -> to_set x) rep_stemlists in
  (* Thie rep_stemsets convert the stem lists into the stem sets. I used the List.map function and to_set since to_set convert a list 
  in the rep_stemlists into a set. *)
  let target_stemset = to_set target_stemlist in
  (* Thie target_stemset convert the list from the target document. As I did in rep_stemsets, I used to_set function to convert a list
  and since this is the target, it is in the target_stemlist and this list is converted into a set. *)

  (* Compute the similarities of each rep set with the target set *)
  let repsims = List.map(fun x -> (similarity x target_stemset)) rep_stemsets in
  let (sim,best_rep) = find_max repsims repfile_list in
  let () = if all then
  (*This repsims is the list of similarities between each document and target file. I used List.map function and used the similarity
  function first. And this is the list of similarity that used other let statement and called repsims, which contains the target sets
  and repfile_list which contains a list and apply the find_max function to it. *)

  (* print out similarities to all representative files *)
  let () = print_endline("File\tSimilarity") in 
  (* The first thing to print out is that if every parameters are true, it print out the File Similarity so I used the print_endline
  to print the thing inside the paranthesis and to print out the File Similarity, I wrote "File\tSimilarity" inside. The thing is
  since there is a blank space between File and Similarity in the output of compile, i put \t which means tab. *)
  
  let () = (List.iter2 (fun x y -> print_endline(x ^ "\t" ^ (string_of_float y))) repfile_list repsims) in
  (* This part print out the similarity and file name of each file to the target file. The format is "<repfile name>\t<score>" so that
  I used the function and printed it by using concat and also put \t. And the most tricky part for me was the List.iter2 part and I
  used this function to get 2 same size lists and make it as function to print out the statement inside of my print_endline. And I 
  used string_of_float to convert float to string. *)
  () else begin
  
  (* Print out the winner and similarity *)
  let () = print_endline ("The most similar file to " ^ target_name ^ " was " ^ best_rep ^ "\n") in
  (* This part is printing out the best result. I simply used print_endline and followed the instructions to match the format. *)
  print_endline ("Similarity: " ^ (string_of_float(sim)) ^ "\n")  end in
  (* This part is the printing out the similarity value. Also, I just followed the instructions to match the format. *)
  (* this last line just makes sure the output prints before the program exits *)
  flush stdout
  (* After getting all the pass on the feedback file, I compiled this file in terminal by typing 
  ocamlc -o findsim str.cma simUtil.ml stemmer.ml similar.ml findsim.ml and it is compiled. It has a Warning 3 from the stemmer.ml
  and it asks to change the String.lowercase to String.lowercase_ascii. But since it was just a warning and it still compiles, and 
  stemmer.ml file was given by professor so that I didn't really change that part and ran it. I followed the instructions written 
  in hw3.md file. I ran the exact same thing as the hw3.md file shows and all of the outputs exactly matched with the instructions.*)
