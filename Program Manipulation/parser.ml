open Program

(* small example programs:
   Because we're keeping type inference simple, we'll require functions to have a single argument,
   and declare the type of that argument after a colon.
   To simplify parsing function applications, we'll have explicit "app" expressions, so to apply function f to argument x,
   the program will say (app f x).  A multiple argument function will need to be applied to each argument in turn, so the equivalent to the
   Ocaml expression (f x y) will be (app (app f x) y).
*)
let example1 =
  "(let f (fun g : int -> int  (app g 0))
          (print (app f (fun x : int (+ x 2)))))"

let example2 =
  "(let gcd (fun a : int (fun b : int
            (let q (/ a b)
            (let r (- a (* q b))
                   (seq (while (not (= r 0))
                               (seq (set a b)
                                    (set b r)
                                    (set q (/ a b))
                                    (set r (- a (* q b)))))
                         b)))))
            (print (app (app gcd 217) 527)))"

let example3 =
"(let y 0
    (let x (+ 1 2)
        (while (> x 0)
            (seq
                (set x (- x 1))
                (if (> 1 0) x y)
                (if (< 1 0) x y)
                (while (> 1 0) (print y))
                (+ 1 2)
                (seq (let z (+ 2 3) (< 1 2)))
            )
        )
    )
)"

(* the first let z cannot be eliminated here because its definition contains a side effect *)
let example4 =
"(let y (* 0 0)
  (let z (if (> y 4)
           (seq (set y (- y 1)) 1)
           0)
    (seq (print y)
         (if (= (+ 1 0) (- 2 1))
             (let z readint z)
             (+ 42 17)))
  )
)"

(* notice the second z "shadows" the first, so the first let z can be eliminated here *)
(* the second cannot, because of the side effect in the definition and its use of z in the body *)
let example5 =
"(let y (- 0 0)
  (let z (if (> y 4) 1 0)
    (seq (print y)
         (if (= (+ 1 0) (- 2 1))
             (let z readint z)
             (+ 42 17)))
  )
)"
(* Declared the exception to use below SyntaxError, Unused, Unclosed exception.
Those all 3 exceptions gets the int value. *)
exception SyntaxError of int
exception Unused of int
exception Unclosed of int

(* all of the lexical tokens we might encounter in a program *)
type token = OP | CP | AND | OR | NOT | PLUS | MINUS | TIMES | DIV | LET | ID of string | CONST of int | BCONST of bool | LT | GT | EQ | IF |
	     SET | SEQ | WHILE | PRINT |
	     APP | FUN | COLON | ARROW | INT | BOOL | UNIT | READ (* Added new constructor READ to token type *)

(* Split a string into a list of words, delimited by spaces, parens, colons, and -> *)
(* never mind the magic regexp *)
let wordlist s =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)\\|:\\|\\(->\\)") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim "->")::t -> "->" :: (filter_splist t)
    | (Str.Delim ":")::t -> ":"::(filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
                           let t' = (filter_splist t) in
                           if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* turn a word into a token *)
let tokenize_string = function
  | "(" -> OP
  | ")" -> CP
  | "and" -> AND
  | "or" -> OR
  | "not" -> NOT
  | "+" -> PLUS
  | "*" -> TIMES
  | "-" -> MINUS
  | "/" -> DIV
  | "let" -> LET
  | ">" -> GT
  | "<" -> LT
  | "=" -> EQ
  | "if" -> IF
  | "set" -> SET
  | "seq" -> SEQ
  | "while" -> WHILE
  | "app" -> APP
  | "fun" -> FUN
  | ":" -> COLON
  | "->" -> ARROW
  | "int" -> INT
  | "bool" -> BOOL
  | "unit" -> UNIT
  | "print" -> PRINT
  | "readint" -> READ (* Using the READ token, and utilize for Readint keyword *)
  | "true" -> BCONST true
  | "false" -> BCONST false
  | s -> if Str.string_match (Str.regexp "[0-9]+") s 0 then (CONST (int_of_string s))
	 else if Str.string_match (Str.regexp "[a-z]+") s 0 then (ID s) else failwith ("invalid token:"^s)

(* and a list of words into a list of tokens *)
let tokens wl = List.map tokenize_string wl

(* Parse a type expression in a function definition.
   Return the type and the list of unused tokens for further parsing.
   A type expression is either: INT, BOOL, UNIT or  (typeExpr)  or typeExpr -> typeExpr  *)
let rec parse_type_expr tlist =
  let (ty1, tl) =
    match tlist with
    | INT::t -> (Int,t)
    | BOOL::t -> (Bool,t)
    | UNIT::t -> (Unit,t)
    | OP::t -> (* Read up until we find a close paren: covers types like "(int->bool) -> int" *)
       let (ty,t) = parse_type_expr t in
       ( match t with
	 | CP::t' -> (ty,t')
	 | _ -> failwith "imbalanced parentheses in type expression" )
    | _ -> failwith "unexpected token in type expression."
  in match tl with (* peek at tail: is there an arrow (so more type expr to read)? *)
     | ARROW::t1 ->
	let (ty2, t2) = parse_type_expr t1 in (FunType(ty1,ty2),t2)
     | _ -> (ty1,tl) (* No, we're done here. *)

let parse_program tlist =
  (* parse an expression from a list of tokens, returning the expression and the list of unused tokens *)
  let rec parser tlist = match tlist with
    | [] -> failwith "Ran out of tokens without closing parenthesis"
    | (READ)::t -> (Readint, t) (* Parsing the expression readint *)
    | (BCONST b)::t -> (Boolean b,t)
    | (CONST i)::t -> (Const i, t)
    | (ID s)::t -> (Name s, t)
    | OP::PLUS::t -> let (e1,e2,t') = parse_two t in (Add (e1,e2), t')
    | OP::MINUS::t -> let (e1,e2,t') = parse_two t in (Sub (e1,e2), t')
    | OP::TIMES::t -> let (e1,e2,t') = parse_two t in (Mul (e1,e2), t')
    | OP::DIV::t -> let (e1,e2,t') = parse_two t in (Div (e1,e2), t')
    | OP::AND::t -> let (e1,e2,t') = parse_two t in (And (e1,e2), t')
    | OP::OR::t -> let (e1,e2,t') = parse_two t in (Or (e1,e2), t')
    | OP::EQ::t -> let (e1,e2,t') = parse_two t in (Eq (e1,e2), t')
    | OP::GT::t -> let (e1,e2,t') = parse_two t in (Gt (e1,e2), t')
    | OP::LT::t -> let (e1,e2,t') = parse_two t in (Lt (e1,e2), t')
    | OP::WHILE::t -> let (e1,e2,t') = parse_two t in (While (e1,e2), t')
    | OP::APP::t -> let (e1,e2,t') = parse_two t in (Apply (e1,e2), t')
    | OP::FUN::(ID s)::COLON::t ->
       let (tExp, t') = parse_type_expr t in
       let (bExp,t'') = parse_single t' in (Fun (s,tExp,bExp),t'')
    | OP::LET::(ID s)::t -> let (v,e,t') = parse_two t in (Let (s,v,e), t')
    | OP::SET::(ID s)::t -> let (e,t') = parse_single t in (Set (s,e), t')
    | OP::IF::t ->
       let (c,t1) = parser t in
       let (thn,els,t2) = parse_two t1 in (If (c,thn,els), t2)
    | OP::NOT::t -> let (e,t') = parse_single t in (Not(e),t')
    | OP::PRINT::t -> let (e,t') = parse_single t in (Print(e), t')
    | OP::SEQ::t -> let (l,t') = parse_list t in (Seq(l),t')
    | _ -> failwith "Unexpected token: unbalanced parentheses or keyword out of call position"

  and parse_single t = let (e,t') = parser t in  (* parse a single expression and "eat" the following close paren *)
    ( match t' with
      | CP::t'' -> (e,t'')
      | _ -> failwith "parser: missing closing paren.")

  and parse_two t = (* "eat" the close paren after two expressions *)
    let (e1,t1) = parser t in
    let (e2,t2) = parser t1 in
    ( match t2 with
      | CP::t' -> (e1,e2,t')
      | _ -> failwith "parser: missing closing paren.")

  and parse_list t = (* parse a list of expressions, consuming the final closing paren *)
    ( match t with
      | CP::t' -> ([],t')
      | [] -> failwith "unfinished expression sequence: missing close paren(s)."
      | _ -> let (e,t1) = parser t in
	     let (el,t2) = parse_list t1 in (e::el, t2)
    )
  in
  let (e,t) = parser tlist in
  match t with
  | [] -> e
  | _ -> failwith "parse failed: extra tokens in input."

(* insert (correct) definitions of const_fold and unused_def_elim here *)
(* const_fold function to perform the optimization on a program tree from language.
Basically similar format with the eval and modified for some cases.  *)
let rec const_fold (e : expr) = match e with
  | Const x -> Const x
  | Boolean x -> Boolean x
  | Name x -> Name x
  (* Case for the Add(x,y) *)
  | Add (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Const (x + y)
  | (x,y) -> Add (x, y))
  (* Case for the Sub(x,y) *)
  | Sub (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Const (x - y)
  | (x,y) -> Sub (x, y))
  (* Case for the Mul(x,y) *)
  | Mul (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Const (x * y)
  | (x,y) -> Mul (x, y))
  (* Case for the Div(x,y) *)
  | Div (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Const (x / y)
  | (x,y) -> Div (x, y))
  (* Case for the Lt(x,y) *)
  | Lt (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Boolean (x < y)
  | (x,y) -> Lt (x, y))
  (* Case for the Eq(x,y) *)
  | Eq (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Boolean (x = y)
  | (x,y) -> Eq (x, y))
  (* Case for the Gt(x,y) *)
  | Gt (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Const x, Const y) -> Boolean (x > y)
  | (x,y) -> Gt (x, y))
  (* Case for the And(x,y) *)
  | And (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Boolean x, Boolean y) -> Boolean (x && y)
  | (x,y) -> And (x, y))
  (* Case for the Or(x,y) *)
  | Or (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Boolean x, Boolean y) -> Boolean (x || y)
  | (x,y) -> Or (x, y))
  (* Case for the Not (x) *)
  | Not x -> let x = const_fold x in (match x with
  | (Boolean x) -> Boolean (not x)
  | x -> Not x)
  (* Case for the If(x,y,z). I modified to simplify for thn(which is written y)
  and for els(which is written z)*)
  | If (x,y,z) -> let x = const_fold x in let y = const_fold y in let z = const_fold z in (match (x,y,z) with
  | (Boolean true,y,z) -> y
  | (Boolean false,y,z) -> z
  | (x,y,z) -> If (x,y,z))
  (* Case for the Let(x,y,z). I used another let expression and modified. And made
  to simplify to b(which is written z) when both b and v(which is written as z)
  as constants *)
  | Let (x,y,z) -> let y = const_fold y in let z = const_fold z in (match (x,y,z) with
  | (x,Const y,Const z) -> Const z
  | (x,Boolean y,Boolean z) -> Boolean z
  | (x,Const y,Boolean z) -> Boolean z
  | (x,Boolean y,Const z) -> Const z
  | (x,y,z) -> Let (x,y,z))
  (* Case for the Seq(x). I modified as any constants expression before the last
  one in a Seq can be removed. And Seq[e] can be modified as e. I added let recursive
  expression to check sequence and make it to work. *)
  | Seq x -> let rec chkseq s = match s with
  | [] -> []
  | [Const y] -> [Const y]
  | [Boolean y] -> [Boolean y]
  | h::t -> let h = const_fold h in (match h with
    | Const y -> chkseq t
    | Boolean y -> chkseq t
    | y -> y::(chkseq t)) in
  (match (chkseq x) with
  | [Const x] -> Const x
  | [Boolean x] -> Boolean x
  | x -> Seq x)
  | While (x,y) -> let x = const_fold x in let y = const_fold y in (match (x,y) with
  | (Boolean false,y) -> Seq []
  | (x,y) -> While (x,y))
  | Set (x,y) -> Set (x,const_fold y)
  | Fun (x,y,z) -> Fun (x,y,const_fold z)
  | Apply (x,y) -> Apply (const_fold x, const_fold y)
  | Print x -> Print (const_fold x)
  (* Adding Readint expression to use Readint that newly declared  *)
  | Readint -> Readint

(* unused_def_elim expression to remove the dead code. I used the same format as
usual, dividing the cases and modified some cases as well. *)
let rec unused_def_elim (e: expr) = match e with
  | Const x -> Const x
  | Boolean x -> Boolean x
  | Name x -> Name x
  (* Case for the Add(e1,e2) *)
  | Add(e1,e2) -> Add(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Sub(e1,e2) *)
  | Sub(e1,e2) -> Sub(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Mul(e1,e2) *)
  | Mul(e1,e2) -> Mul(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Div(e1,e2) *)
  | Div(e1,e2) -> Div(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the And(e1,e2) *)
  | And(e1,e2) -> And(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Or(e1,e2) *)
  | Or(e1,e2) -> Or(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Lt(e1,e2) *)
  | Lt(e1,e2) -> Lt(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Eq(e1,e2) *)
  | Eq(e1,e2) -> Eq(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Gt(e1,e2) *)
  | Gt(e1,e2) -> Gt(unused_def_elim e1, unused_def_elim e2 )
  (* Case for the Let(x,y,z). In this case, we have to think about the shadow
  binding cases. If the body of the expression contains a new binding for the
  name, reference to this new name are not reference to original *)
  | Let (x,y,z) ->
    ( if (has_shadow_binding (Let(x,y,z))) then (unused_def_elim z)
    (* Below 3 lines are for the case of Fun. This is the other variant that
    might shadow bind. *)
    else match y with
    | Fun _ -> unused_def_elim z
    | _ -> Let(x, unused_def_elim y, unused_def_elim z))
  (* Case for the Seq (slist). *)
  | Seq slist ->
    let rec helper lst = List.map (fun x -> (unused_def_elim x)) lst
    in Seq (helper slist)
  | While (x, y) ->While (unused_def_elim x, unused_def_elim y)
  | Set (name, e) -> Set (name, unused_def_elim e)
  | Fun(x,y,z) -> Fun (x,y, unused_def_elim z)
  | Apply (f, e) -> Apply (f, unused_def_elim e)
  | Print(e) -> Print (unused_def_elim e)
  | Readint -> Readint
  | If(c, thn, els) -> If(unused_def_elim c, unused_def_elim thn, unused_def_elim els)
  | Not(e) -> Not(unused_def_elim e)
(* Below is the function for the shadow binding. I used the shadow binding function
similar as the ex we did and modified to work in this case. *)
and has_shadow_binding (e:expr) =
  let rec shadow e bound = match e with
  | Const _ | Boolean _ | Name _ | Readint -> false (* Added Readint case *)
  | Not e | Print e -> shadow e bound
  | Add (e1,e2) | Sub (e1,e2) | Mul (e1, e2) | Div (e1, e2)
  | And (e1, e2) | Or (e1, e2)
  | Lt (e1,e2) | Eq (e1, e2) | Gt (e1,e2) -> (shadow e1 bound) || (shadow e2 bound)
  | If (c,thn,els) -> (shadow c bound) || (shadow thn bound) || (shadow els bound)
  | Let (nm, v, b) -> (List.mem nm bound) || (shadow v bound) || (shadow b (nm::bound))
  | While(cond, e) -> shadow cond bound || shadow e bound
  (* Added expression for Set, Fun, Apply and make it to work as shadow binding *)
  | Set(_,e) | Fun(_,_,e) | Apply (_,e) -> shadow e bound
  (* Added expression for Seq. *)
  | Seq slist -> List.fold_left(fun acc el -> acc || (shadow el bound)) false slist
  in shadow e []

  (* parse_pos function that modifies the parse to keep track of position in the
  token list and raise the proper exception when it encounters. I modified parser
  function and added the raise expression to catch the exception. This has 3 cases
  that was mentioned in instruction. [OP; OP] throws SyntaxError since there are
  no CP expression that close the parenthesis. [OP; PLUS; CONST 1; CONST 1; CP; CONST 1]
  throws Unused exception since the last CONST 1 is not used. And gets the argument
  of 5 since it's the 6th position (1st position is 0 argument.)
  [OP; TIMES; OP; PLUS; CONST 0; CONST 1; CONST 2; CP; CONST 3; CP]
  throws Unclosed exception since the CONST 2 at the 7th position is wrong and
  it is expected to have CP expression instead since PLUS gets 2 arguments and
  need to be closed after that. All of the exception has the argument value
  for the position which has the wrong expression. *)
  let parse_pos tlist = let length = List.length tlist in
    (* parse an expression from a list of tokens, returning the expression and the list of unused tokens *)
    let rec parser tlist = match tlist with
      (* Exception Unused thrown for empty list. *)
      | [] -> raise (Unused length)
      | (READ)::t -> (Readint, t) (* Parsing the expression readint *)
      | (BCONST b)::t -> (Boolean b,t)
      | (CONST i)::t -> (Const i, t)
      | (ID s)::t -> (Name s, t)
      | OP::PLUS::t -> let (e1,e2,t') = parse_two t in (Add (e1,e2), t')
      | OP::MINUS::t -> let (e1,e2,t') = parse_two t in (Sub (e1,e2), t')
      | OP::TIMES::t -> let (e1,e2,t') = parse_two t in (Mul (e1,e2), t')
      | OP::DIV::t -> let (e1,e2,t') = parse_two t in (Div (e1,e2), t')
      | OP::AND::t -> let (e1,e2,t') = parse_two t in (And (e1,e2), t')
      | OP::OR::t -> let (e1,e2,t') = parse_two t in (Or (e1,e2), t')
      | OP::EQ::t -> let (e1,e2,t') = parse_two t in (Eq (e1,e2), t')
      | OP::GT::t -> let (e1,e2,t') = parse_two t in (Gt (e1,e2), t')
      | OP::LT::t -> let (e1,e2,t') = parse_two t in (Lt (e1,e2), t')
      | OP::WHILE::t -> let (e1,e2,t') = parse_two t in (While (e1,e2), t')
      | OP::APP::t -> let (e1,e2,t') = parse_two t in (Apply (e1,e2), t')
      | OP::FUN::(ID s)::COLON::t ->
         let (tExp, t') = parse_type_expr t in
         let (bExp,t'') = parse_single t' in (Fun (s,tExp,bExp),t'')
      | OP::LET::(ID s)::t -> let (v,e,t') = parse_two t in (Let (s,v,e), t')
      | OP::SET::(ID s)::t -> let (e,t') = parse_single t in (Set (s,e), t')
      | OP::IF::t ->
         let (c,t1) = parser t in
         let (thn,els,t2) = parse_two t1 in (If (c,thn,els), t2)
      | OP::NOT::t -> let (e,t') = parse_single t in (Not(e),t')
      | OP::PRINT::t -> let (e,t') = parse_single t in (Print(e), t')
      | OP::SEQ::t -> let (l,t') = parse_list t in (Seq(l),t')
      (* Used raise to throw SyntaxError in this case. *)
      | t -> raise (SyntaxError (1+length-(List.length t)))

    and parse_single t = let (e,t') = parser t in  (* parse a single expression and "eat" the following close paren *)
      ( match t' with
        | CP::t'' -> (e,t'')
        (* Used raise to throw Unclosed exception in this case. *)
        | t -> raise (Unclosed (length -(List.length t))))

    and parse_two t = (* "eat" the close paren after two expressions *)
      let (e1,t1) = parser t in
      let (e2,t2) = parser t1 in
      ( match t2 with
        | CP::t' -> (e1,e2,t')
        (* Used raise to throw Unclosed exception in this case as well. *)
        | t -> raise (Unclosed (length -(List.length t))))

    and parse_list t = (* parse a list of expressions, consuming the final closing paren *)
      ( match t with
        | CP::t' -> ([],t')
        (* Used raise to throw Unused exception in this case. *)
        | [] -> raise (Unused length)
        | _ -> let (e,t1) = parser t in
  	     let (el,t2) = parse_list t1 in (e::el, t2)
      )
    in
    let (e,t) = parser tlist in
    match t with
    | [] -> e
    (* Used raise to throw Unused exception in this case. *)
    | x -> raise (Unused (length - (List.length x)))
