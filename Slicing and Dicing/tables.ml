(* tables.ml - CSci 2041 HW 1 table slicer and dicer *)
(* Joowon Kim *)

(* Free functions, don't question! *)
(* read std input to eof, return list of lines *)
let read_lines () : string list =
  let rec read_help acc =
    try read_help ((read_line ())::acc) with End_of_file -> List.rev acc
  in read_help []

(* separate a string by delim into a list, trimming surrounding whitespace *)
let make_row delim str =
  let rec trim_strings ls acc = match ls with
  | [] -> List.rev acc
  | h::t -> trim_strings t ((String.trim h)::acc) in
  trim_strings (Str.split (Str.regexp delim) str) []

(* print a list of strings to std output, separated by delim string *)
(* avoids nasty quadratic concatenation behavior *)
let rec write_row r delim = match r with
| [] -> ()
| h::[] -> print_endline h
| h::t -> let () = print_string h in
          let () = print_string delim in write_row t delim

(* Output table using write_row, note let () = ... idiom *)
let rec output_table od t = match t with
| [] -> ()
| r::rs -> let () = write_row r od in output_table od rs

(* Now your turn. *)

(* translate a list of rows in string form into a list of *)
(* lists of string entries *)
let rec table_of_stringlist delim rlist = match rlist with
| [] -> []
| h::t -> [make_row delim h]@ table_of_stringlist delim t 

(* translate a string list list into associative form, i.e. *)
(* a list of (row, column, entry) triples *)
let rec get_row lst_row r c acc = match lst_row with
  | [] -> acc
  | []::t -> acc
  | h::t -> [(r,c,h)]@ (get_row t (r+1) c acc)
let rec get_col lst_col r c acc = match lst_col with
  | [] -> acc
  | h::[] -> acc
  | h::t -> (get_row h r c []):: (get_col t r (c+1) acc)
let make_assoc rc_list = get_row rc_list 1 1 []

(* remap the columns of the associative form so that the first column number in clst *)
(* is column 1, the second column 2, ..., and any column not in clst doesn't appear *)
let rec alst_assoc alst idx s acc = match alst with
| [] -> acc
| (a,b,c)::t -> if b = idx then (a,s,c)::alst_assoc t idx s acc 
                else alst_assoc t idx s acc

let rec idx_assoc alst clst k acc = match clst with
| [] -> acc
| h::t -> (alst_assoc alst h k acc) @(idx_assoc alst t (k+1) acc)

let remap_columns clst alst = idx_assoc alst clst 1 []

(* remap the rows of the associative form so that the first row number in rlst *)
(* is row 1, the second is row 2, ..., and any row not in rlist doesn't appear *)
let rec alst_assoc alst idx s acc = match alst with
| [] -> acc
| (a,b,c)::t -> if a = idx then (s,b,c)::alst_assoc t idx s acc 
                else alst_assoc t idx s acc

let rec idx_assoc alst rlst k acc = match rlst with
| [] -> acc
| h::t -> (alst_assoc alst h k acc) @(idx_assoc alst t (k+1) acc)

let remap_rows rlst alst = idx_assoc alst rlst 1 []

(* transpose table works on the associative form *)
let transpose_table alist =
  let rec trans_assoc lst = match lst with	
  | [] -> []
  | h::t -> (match h with | (r,c,h) -> (c,r,h))::(trans_assoc t)
in trans_assoc alist

(* here's a tricky one! *)
let table_of_assoc alist = []

(* OK, more free stuff *)
let main transpose clst rlst id od =
  let sl = read_lines () in
  let rtable = table_of_stringlist id sl in
  let alist = make_assoc rtable in
  let clist = if clst = [] then alist else (remap_columns clst alist) in
  let rlist = if rlst = [] then clist else (remap_rows rlst clist) in
  let tlist = if transpose then transpose_table rlist else rlist in
  let ntable = table_of_assoc tlist in
  output_table od ntable
