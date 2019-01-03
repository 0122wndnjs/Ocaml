### ``power``  
Prove that for all n &in; &naturals;, for all x &in; `float`:  
`power x n` = `x `<sup>`n`</sup>

```
let rec power x n =
  if n = 0 then 1.0
  else x *. (power x n-1)
```

**Property _P_**:

&forall; n &in; &naturals; , let `p(n)` = &forall; x &in; float, `power x n` = `x `<sup>`n`</sup>  

 - We must show that `P(0)` holds  

 - We must show that `P(n+1)` holds assuming &forall; x &in; float, `P(n)`   

#### Base case:  

`P(0)` = &forall; `x` &in; `float`, `power x 0` = `x `<sup>`0`</sup>  

  - left-hand side:  
` power x 0` = `1.0` **[eval of power]**  

  - right-hand side:  
  `x `<sup>`0`</sup> = `1.0` **[by arith]**  

`power x 0` = `x `<sup>`0`</sup> = `1.0` **[by matching left & right hand side]** , &check;

#### Inductive case:  

In the inductive case, we want to show that &forall; n &in; &naturals;, &forall; x &in; `float`, `P(n)` &rArr; `P(n+1)`  

> **IH: &forall; n &in; &naturals;, &forall; x &in; `float`, `power x n` = `x `<sup>`n`</sup>**

We want to show `P(n+1)`. Therefore, we want to show if `power x (n+1)` = `x `<sup>`(n+1)`</sup>

- `P(n+1)`    
`power x (n+1)` ***[left-hand side]***    
= `x *. (power x ((n+1)-1))` ***[eval of power]***  
= `x` `*.` `(power x n)` ***[by simplification]***   
= `x` `*.` (`x `<sup>`n`</sup>) ***[by IH]***    
= `x `<sup>`(n+1)`</sup> ***[by arith]***  
= `x `<sup>`(n+1)`</sup> ***[right-hand side]*** , &check;  

### ``pow_nat``  
Use structural induction on the type `nat` to prove that &forall; `n` &in; `nat`, &forall; `x` &in; `float`,   
`power x (to_int n) = pow_nat x n`  

```
type nat = Zero | Succ of nat

let rec to_int n = match n with
| Zero -> 0
| Succ n' -> 1 + (to_int n')

let rec pow_nat x n = match n with
| Zero -> 1.0
| Succ n' -> x *. (pow_nat x n')
```

#### Property _P_ :  

&forall; `n` &in; `nat`, let `P(n)` = &forall; `x` &in; `float`, `power x (to_int n) = pow_nat x n`  

  - We must show that `P(Zero)` holds

  - We must show that `P(Succ n)` holds assuming &forall; `n` &in; `nat`, &forall; `x` &in; `float`, `P(n)`

#### Base case:  

`P(Zero)` = &forall; `x` &in; `float`, `power x (to_int Zero) = pow_nat x Zero`  

  - left-hand side:  
  `power x (to_int Zero)` = `power x 0` **[eval of to_int]**  
  = `1.0` **[eval of power]**  

  - right-hand side:  
  `pow_nat x Zero` = `1.0` **[eval of pow_nat]**   

`power x (to_int Zero)` = `pow_nat x Zero` = `1.0` **[by matching left & right hand side]** , &check;

#### Inductive case:  

In the inductive step, we want to show that &forall; `n` &in; `nat` , `P(n)` &rArr; `P(Succ n)`  

> **IH: &forall; `n` &in; `nat`, &forall; `x` &in; `float`, `power x (to_int n)` = `pow_nat x n`**  

We want to show `P(Succ n)`. Therefore, we want to show if `power x (to_int (Succ n))` = `pow_nat x (Succ n)`  

  - left-hand side:  
  `P(Succ n)` = `power x (to_int (Succ n))`  
  = `power x (1 + (to_int n))` ***[eval of to_int]***  
  = `x *. (power x (to_int n))` ***[eval of power]***  
  = `x *. (pow_nat x n)`  ***[by IH]***  

  - right-hand side:  
  `P(Succ n)` = `pow_nat x (Succ n)`    
  = `x *. (pow_nat x n)` ***[eval of pow_nat]***  

  - Conclusion by left-hand side & right-hand side  
  `power x (to_int (Succ n))`
  = `x *. (pow_nat x n)`  ***[eval of to_int]***  
  =  `pow_nat x (Succ n)` ***[reverse eval of pow_nat]*** , &check;

### ``less_nat``  

Use structural induction on the type `nat`to prove that &forall; `m` &in; `nat` &forall; `n` &in; `nat` :
`less_nat m n` &hArr; `(to_int m)` < `(to_int n)`.  

```
(* test whether m < n without converting to integers *)
let rec less_nat m n = match n with
| Zero -> false (* m is not less than Zero *)
| Succ n' -> if m = n' then true (* n = m+1 > m *)
                 else less_nat m n' (* n > m iff n-1 >= m *)
```
#### Property _P_:

&forall; `n` &in; `nat` , let `p(n)` = &forall; `m` &in; `nat` , `less_nat m n` &hArr; `(to_int m)` < `(to_int n)`    

 - We must show that `P(Zero)` holds  

 - We must show that `P(Succ n)` holds assuming &forall; `m` &in; `nat` &forall; `n` &in; `nat` , `P(Succ n)`   


#### Base case:  

In the case we have `P(Zero)` = &forall; `m` &in; `nat` , `less_nat m Zero` &hArr; `(to_int m)` < `(to_int Zero)`

- CASE 1 :   
  - left-hand side:  
  `less_nat m Zero` = `false` **[eval of less_nat]**  

  - right-hand side:  
  `(to_int m)` < `(to_int Zero)`    
  = `(to_int m)` < `0` **[eval of to_int]**    
  = `false` **[Since `m` is not less than Zero]**

`less_nat m Zero` &rArr; `(to_int m)` < `(to_int Zero)` **[by matching left & right hand side]** , &check;  

- CASE 2 :    
  - left-hand side:  
  `(to_int m)` < `(to_int Zero)`   
  = `(tp_int m)` < `0` **[eval of to_int]**   
  = `false` **[Since `m` is not less than Zero]**  

  - right-hand side:  
  `less_nat m Zero` = `false` **[eval of less_nat]**  

`less_nat m Zero` &lArr; `(to_int m)` < `(to_int Zero)` **[by matching left & right hand side]** , &check;  

Since &rArr; and &lArr; matches, `less_nat m Zero` &hArr; `(to_int m)` < `(to_int Zero)` , &check;

#### Inductive case:  

In the inductive case, we want to show that &forall; `m` &in; `nat` &forall; `n` &in; `nat` , `P(n)` &hArr; `P(Succ n)`  

> **IH: &forall; `m` &in; `nat` &forall; `n` &in; `nat` , `less_nat m n` &hArr; `(to_int m)` < `(to_int n)`**  

We want to show `P(Succ n)`. Therefore, we want to show if `less_nat m (Succ n)` &hArr; `(to_int m)` < `(to_int (Succ n))`  

Since this has &hArr;, it has to be proved in both ways, (&rArr;) and (&lArr;)
And there is an `if & else` statement in case of `Succ n'` in `less_nat`, it has to be proved in 2 CASES.    
First Case is when `m = n'` and second case is when `m != n`  

  - CASE 1 : (m = n)

    - `less_nat m (Succ n)` &rArr; `(to_int m)` < `(to_int (Succ n))`  

      - left-hand side:  
      `less_nat m (Succ n)`   
      = `true` ***[eval of less_nat]***  

      - right-hand side:  
      `(to_int m)` < `(to_int (Succ n))`
      = `(to_int m)` < `1 + (to_int n)` ***[eval of to_int]***  
      = `(to_int m)` < `(to_int (n+1))` ***[by arith]***
      = `(to_int m)` < `(to_int ((m+1)+1))` ***[eval of less_nat Succ n' (n = m+1)]***
      = `true`  ***[eval of less_nat]***  

      - Conclusion by left-hand side & right-hand side  
      `less_nat m (Succ n)` &rArr; `(to_int m)` < `(to_int (Succ n))` ***[by matching left & right hand side]*** , &check;

    - `(to_int m)` < `(to_int (Succ n))` &rArr; `less_nat m (Succ n)`  

      - left-hand side:   
      `(to_int m)` < `(to_int (Succ n))`  
      = `(to_int m)` < `1 + (to_int n)` ***[eval of to_int]***  
      = `(to_int m)` <  `(to_int (n+1))` ***[by arith]***  
      = `(to_int m)` < `(to_int ((m+1)+1))` ***[eval of less_nat Succ n' (n = m+1)]***  
      = `true` ***[eval of less_nat]***  

      - right-hand side:  
      `less_nat m (Succ n)`   
      = `true` ***[eval of less_nat]***  

      - Conclusion by left-hand side & right-hand side  
      `(to_int m)` < `(to_int (Succ n))` &rArr; `less_nat m (Succ n)` ***[by matching left & right hand side]*** , &check;  

  - CASE 2 : (m != n)

    - `less_nat m (Succ n)` &rArr; `(to_int m)` < `(to_int (Succ n))`  

      - left-hand side:  
      `less_nat m (Succ n)`   
      = `less_nat m n` ***[eval of less_nat]***   
      &rArr; `(to_int m)` < `(to_int n)` ***[by IH]***  
      = `true`   

      - right-hand side:  
      `(to_int m)` < `(to_int (Succ n))`
      = `(to_int m)` < `1 + (to_int n)` ***[eval of to_int]***    
      = `(to_int m)` < `(to_int (n+1))` ***[by arith]***  
      = `(to_int m)` < `(to_int ((m+1)+1))` ***[eval of less_nat Succ n' (n-1 >= m)]***  
      = `true`

      - Conclusion by left-hand side & right-hand side  
      `less_nat m (Succ n)` &rArr; `(to_int m)` < `(to_int (Succ n))` ***[by matching left & right hand side]*** , &check;  

    - `(to_int m)` < `(to_int (Succ n))` &rArr; `less_nat m (Succ n)`  

      - left-hand side:  
      `to_int m` < `(to_int (Succ n))`  
      = `(to_int m)` < `1 + (to_int n)` ***[eval of to_int]***  
      = `(to_int m)` < `(to_int (n+1))` ***[by arith]***  
      = `(to_int m)` < `(to_int ((m+1)+1))` ***[eval of less_nat Succ n' (n-1 <= m)]***  
      = `true`  

      - right-hand side:  
      `less_nat m (Succ n)`  
      = `less_nat m n` ***[eval of less_nat]***  
      &rArr; `(tp_int m)` < `(to_int n)` ***[by IH]***  
      = `true`  

      - Conclusion by left-hand side & right-hand side  
      `(to_int m)` < `(to_int (Succ n))` &rArr; `less_nat m (Succ n)` ***[by matching left & right hand side]*** , &check;  
