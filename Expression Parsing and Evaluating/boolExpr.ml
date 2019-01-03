(* read std input to eof, return list of lines *)
let read_lines () : string list =
  let rec read_help acc =
    try read_help ((read_line ())::acc) with End_of_file -> List.rev acc
  in read_help []

(* split a string at word boundaries and parens *)
let wordlist s : string list =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
			   let t' = (filter_splist t) in
			   if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* is s a legal variable name? *)
let is_varname s =
  let rec checker i =
    if i = 0 then
      'a' <= s.[i] && s.[i] <= 'z'
    else
      (('a' <= s.[i] && s.[i] <= 'z') ||
  	   ('0' <= s.[i] && s.[i] <= '9')) && checker (i-1)
  in checker ((String.length s) - 1)

(* tokens - you need to add some here *)
type bexp_token = OP | CP | NAND | AND | OR | NOT | XOR | EQ | CONST of bool | VAR of string
(*I added | AND | OR | NOT | XOR | EQ  for the type so that each token will support the token_of_string *)

(* convert a string into a token *)
let token_of_string = function
  | "(" -> OP
  | ")" -> CP
  | "nand" -> NAND
  | "and" -> AND
  | "or" -> OR
  | "not" -> NOT
  | "xor" -> XOR
  | "=" -> EQ
  | "T" -> CONST true
  | "F" -> CONST false
  | s -> if (is_varname s) then (VAR s) else (invalid_arg ("Unknown Token: "^s))
  (*I added and, or, not, xor, = that matches the token I added.*)

(* convert a list of strings into a a list of tokens *)
let tokens wl : bexp_token list = List.map token_of_string wl

(* type representing a boolean expression, you need to add variants here *)
type boolExpr = Const of bool
| Id of string
|  Nand of boolExpr * boolExpr
|  And of boolExpr * boolExpr
|  Or of boolExpr * boolExpr
|  Not of boolExpr 
|  Xor of boolExpr * boolExpr
|  Eq of boolExpr * boolExpr
(*I added the boolExpr of And, Or, Not, Xor, Eq. All of them I added are boolExpr * boolExpr 
but for the Not, just boolExpr. The reason can be found in the format*)

(* attempt to turn a list of tokens into a boolean expression tree.
A token list representing a boolean expression is either
 + a CONST token :: <more tokens> or
 + a VAR token :: <more tokens> or
 + an OPEN PAREN token :: a NAND token :: <a token list representing a boolean expression> @
                                          <a token list representing a boolen expression> @ a CLOSE PAREN token :: <more tokens>
 any other list is syntactically incorrect. *)
let parse_bool_exp tok_list =
(* when possibly parsing a sub-expression, return the first legal expression read
   and the list of remaining tokens  *)
  let rec parser tlist = match tlist with
    | (CONST b)::t -> (Const b, t)
    | (VAR s)::t -> (Id s, t)
    | OP::NAND::t -> let (a1, t1) = parser t in
                    let (a2, t2) = parser t1 in
                    (match t2 with 
                     | CP::t' -> ((Nand (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::AND::t -> let (a1, t1) = parser t in
    		    let (a2, t2) = parser t1 in
		    (match t2 with
		    | CP::t' -> ((And (a1,a2)), t')
		    		| _ -> invalid_arg "sexp: missing )" )
    (*I added parser for AND which is the similar format as the NAND. Since AND hold a pair of boolExpr value, I used 2 
    let expression and make it to hold boolExpr * boolExpr.*)
    | OP::OR::t -> let (a1, t1) = parser t in
    		    let (a2, t2) = parser t1 in
		    (match t2 with
		    | CP::t' -> ((Or(a1,a2)), t')
		    		| _ -> invalid_arg "sexp: missing )" )
    (*I added parser for OR which is the similar format as the NAND. Since OR hold a pair of boolExpr value, I used 2 
    let expression and make it to hold boolExpr * boolExpr.*)
    | OP::NOT::t -> let (a1, t1) = parser t in
		   (match t1 with
		   |CP::t' -> (Not a1, t')
		  		 | _ -> invalid_arg "sexp: missing )" )
    (*I added parser for NOT which is the similar format as the NAND. Since NOT hold a single boolExpr value, I only use 1
    let expression and make it to hole boolExpr*)
    | OP::XOR::t -> let (a1, t1) = parser t in
    		    let (a2, t2) = parser t1 in
		    (match t2 with
		    | CP::t' -> ((Xor(a1,a2)), t')
		    		| _ -> invalid_arg "sexp: missing )" )
    (*I added parser for XOR which is the similar format as the NAND. Since XOR hold a pair of boolExpr value, I used 2 
    let expression and make it to hold boolExpr * boolExpr.*)
    | OP::EQ::t -> let (a1, t1) = parser t in
    		    let (a2, t2) = parser t1 in
		    (match t2 with
		    | CP::t' -> ((Eq(a1,a2)), t')
		    		| _ -> invalid_arg "sexp: missing )" )
				
    (*I added parser for EQ which is the similar format as the NAND. Since EQ hold a pair of boolExpr value, I used 2 
    let expression and make it to hold boolExpr * boolExpr.*)
    | _ -> invalid_arg "parse failed."
  in let bx, t = parser tok_list in
     match t with
     | [] -> bx
     | _ -> invalid_arg "parse failed: extra tokens in input."

(* pipeline from s-expression string to boolExpr *)
let bool_exp_of_s_exp s = s |> wordlist |> tokens |> parse_bool_exp

(* evaluate the boolean expression bexp, assuming the variable names
   in the list tru are true, and variables not in the list are false *)
let rec eval_bool_exp bexp tru =
  match bexp with
  | Const b -> b
  | Id s -> List.mem s tru
  | Nand (x1, x2) -> not ((eval_bool_exp x1 tru) && (eval_bool_exp x2 tru))
  | And (x1, x2) ->  ((eval_bool_exp x1 tru) && (eval_bool_exp x2 tru))
  (*I added And evaluation. The output is true only when both x1 and x2 are true so I used && to make it true when both 
  qualify the true value. Otherwise, if one of them are false, it will show as false.*)
  | Or (x1, x2) ->  ((eval_bool_exp x1 tru) || (eval_bool_exp x2 tru))
  (*I added Or evaluation. The output is true when one of x1 or x2 are true so I used || to make it true when at least
  one qualify the truth value. It will show false only when both x1 and x2 are false*)
  | Not x1 -> not (eval_bool_exp x1 tru)
  (*I added Not evaluation. Since Not hold only one boolExpr, and this will show output opposite to the truth value. 
  For example, eval_bool_exp (Not (Const false)) [] will evaluate to true since it holds false and reverse the result*)
  | Xor (x1, x2) ->  ((eval_bool_exp x1 tru) != (eval_bool_exp x2 tru))
  (*I added Xor evaluation. The output is true only when x1 value and x2 hold only one truth value. If x1 and x2 are both
  false, or both true, it will return false*)
  | Eq (x1, x2) ->  ((eval_bool_exp x1 tru) == (eval_bool_exp x2 tru))
  (*I added Eq evaluation. The output is true when both x1 and x2 hold same boolExpr. For example, Eq will make it true when
  x1 and x2 are both true or both false and it will return false when x1 and x2 hold different boolExpr such as true, false
  or false, true*)
(* You need to add some new stuff in here: *)

(* list all the subsets of the list s *)
let rec subsets s = match s with
| [] -> [[]]
| (h::t) -> let sub = subsets t in List.append (List.map (fun x -> h::x) sub) sub
(*This will find all the subset of the lists. The type is 'a list -> 'a list list. *)

(* find all the variable names in a boolExpr *)
let rec var_list bexp =
  let rec helper bexp acc = match bexp with
  | Id s -> if (List.mem s acc) then acc else s::acc
  | Const _ -> acc
  | Not n -> helper n acc
  | Nand (x1, x2) | And (x1, x2) | Or (x1, x2) | Xor (x1, x2) | Eq (x1, x2) -> helper x1 (acc@ (helper x2 acc))
in helper bexp []
(*This will find all the variable names that appears in boolean expression. The type is boolExpr -> string list.*)

(* find a list of variables that when set to true make the expression true *)
let find_sat_set bexp : string list option = 
  let rec helper bexp lst = match lst with
  | [] -> None
  | (h::t) -> if (eval_bool_exp bexp h) then Some h
  	      else helper bexp t 
in helper bexp (subsets (var_list bexp))
(*This will find the subset of variables that satisfies the true. If not, it will show false. Basically, I needed 2 functions
that I used previously, which are eval_bool_exp and subset. Since the type is boolExpr -> string list option, I used None
for the empty list, and used if else statement when calling the eval_bool_exp. And the last step is called subset function
so that the output will show the subset of variables.*)

(* fill this in also *)
let sat_main () =
  let sExpr = String.concat " " (read_lines ()) in
  let bExpr = bool_exp_of_s_exp sExpr in
  let result = match find_sat_set bExpr with
    | None -> "Not satisfiable"
    | Some x -> "Satisfied when the variables {" ^ (String.concat ", " x) ^ "} are set to true" in
  print_endline(result)
(*For this sat_main, it will read the input formula and print the result. it will use the find_sat_set for the result 
and if None, it will print Not satisfiable and if it satisfies, it will print the message "Satisfied when the variable are 
set to true" and it will also print the variable we evaluate.*)

let main true_vars_list =
  let sExpr = String.concat " " (read_lines ()) in
  let bExpr = bool_exp_of_s_exp sExpr in
  let result = eval_bool_exp bExpr true_vars_list in
  let svarlist = " when the variables {" ^ (String.concat ", " true_vars_list) ^"} are set to true." in
  let output = (if result then "True" else "False")^svarlist in
  print_endline output
