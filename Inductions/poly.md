### I. ``deg (compose p1 p2) = (deg p1)*(deg p2)``  

#### Property _P_ :  

&forall; `p`, let `P(p)` = &forall; `p2`, `deg (compose p p2)` = `(deg p) * (deg p2)`  

#### Base case:  

1. `P(Int i)` = `deg(compose (Int i) p2)` = `(deg (Int i)) * (deg p2)`  

  - left-hand side:  
  `P(Int i)` = `deg(compose (Int i) p2)`
  = `(deg (Int i))` **[eval of compose]**  
  = `0`  **[eval of deg (Int)]**  

  - right-hand side:  
  `P(Int i)` = `(deg (Int i)) * (deg p2)`  
  = `0` * `(deg p2)` **[eval of deg (Int)]**      
  = `0` **[by arith]**  

`deg(compose (Int i) p2)` = `0` = `(deg (Int i)) * (deg p2)` **[by matching left & right hand side]** , &check;  

2. `P(X)` = `deg(compose X p2)` = `(deg X) * (deg p2)`  

  - left-hand side:  
  `P(X)` = `deg(compose X p2)`  
  = `deg p2` **[eval of compose]**  

  - right-hand side:  
  `P(X)` = `(deg X) * (deg p2)`  
  = `1 * (deg p2)` **[eval of deg (X)]**  
  = `deg p2` **[by arith]**  

`deg(compose X p2)` = `deg p2` = `(deg X) * (deg p2)`  **[by matching left & right hand side]** , &check;   

#### Inductive case:  

In the inductive case, we want to show that &forall; `e1`, &forall; `e2`, `P(e1) and P(e2)` &rArr; `P(Add(e1,e2))` and `P(Mul(e1,e2))`  

>**IH: &forall; `p`, &forall; `p2`, `deg(compose p p2)` = `(deg p) * (deg p2)`**  

We want to show `P(Add(e1,e2))`. Therefore, we want to show if `deg(compose (Add(e1,e2)) p2)` = `(deg Add(e1,e2))` * `(deg p2)`  

- `P(Add(e1,e2))`  
  - left-hand side:  
  `P(Add(e1,e2))` = `deg(compose (Add(e1,e2)) p2)`  
  = `deg (Add (compose e1 p2, compose e2 p2))` ***[eval of compose]***  
  = `max(deg compose e1 p2) (deg compose e2 p2)` ***[eval of deg]***  
  = `max (deg e1) * (deg p2) (deg e2) * (deg p2)` ***[by IH]***   
  = `(max (deg e1) (deg e2)) * (deg p2)` ***[by arith]***   

  - right-hand side:  
  `P(Add(e1,e2))` = `(deg Add(e1,e2)) * (deg p2)`  
  = `(max (deg e1) (deg e2)) * (deg p2)` ***[eval of deg]***  

`deg(compose (Add(e1,e2)) p2)` = `(max (deg e1) (deg e2)) * (deg p2)` = `(deg Add(e1,e2)) * (deg p2)` ***[by matching left & right hand side]*** , &check;  

We want to show `P(Mul(e1,e2))`. Therefore, we want to show if `deg(compose (Mul(e1,e2)) p2)` = `(deg Mul(e1,e2))` * `(deg p2)`  

- `P(Mul(e1,e2))`  
  - left-hand side:  
  `P(Mul(e1,e2))` = `deg(compose (Mul(e1,e2)) p2)`  
  = `deg (Mul (compose e1 p2, compose e2 p2)` ***[eval of compose]***  
  = `(deg compose e1 p2) + (deg compose e2 p2)` ***[eval of deg]***  
  = `(deg e1) * (deg p2)` + `(deg e2) * (deg p2)` ***[by IH]***  
  = `(deg p2) * ((deg e1) + (deg e2))` ***[by arith]***   

  - right-hand side:  
  `P(Mul(e1,e2))` = `(deg Mul(e1,e2)) * (deg p2)`  
  = `((deg e1) + (deg e2))` * `deg p2` ***[eval of deg]***  

`deg(compose (Mul(e1,e2)) p2)` = `(deg p2) * ((deg e1) + (deg e2))` = `(deg Mul(e1,e2)) * (deg p2)` ***[by matching left & right hand side]*** , &check;

### II. ``deg (simplify p) <= deg p``  

#### Property _P_ :  

`P(p)` = &forall; `p`, `deg (simplify p) <= deg p`   

#### Base case:  

1. `P(Int i)` = `deg (simplify (Int i)) <= deg (Int i)`  

  - left-hand side:  
  `P(Int i)` = `deg (simplify (Int i))`  
  = `deg (Int i)` **[eval of simplify]**  
  = `0` **[eval of deg]**  

  - right-hand side:  
  `P(Int i)` = `deg (Int i)`  
  = `0` **[eval of deg]**  

`deg (simplify (Int i))` = `0` <= `deg (Int i)` = `0` **[by matching left & right hand side]** , &check;  

2. `P(X)` = `deg (simplify X) <= deg (X)`  

  - left-hand side:  
  `P(X)` = `deg (simplify X)`  
  = `deg X` **[eval of simplify]**  
  = `1` **[eval of deg]**  

  - right-hand side:  
  `P(X)` = `deg X`  
  = `1` **[eval of deg]**  

`deg (simplify X)` = `1` <= `deg X` = `1` **[by matching left & right hand side]** , &check;  

#### Inductive case:  

In the inductive case, we want to show that &forall; `e1`, &forall; `e2` `P(e1) and P(e2)` &rArr; `P(Add(e1,e2))` and `P(Mul(e1,e2))`  

>**IH: &forall; `p` , `deg (simplify p)` <= `deg p`**  

We want to show `P(Add(e1,e2))`. Therefore, we want to show if `deg (simplify (Add(e1,e2)))` = `deg Add(e1,e2)`  

- `P(Add(e1,e2))`  
  - left-hand side:  
  `P(Add(e1,e2))` = `deg (simplify (Add(e1,e2)))`  
  = `deg (simp_add (simplify e1, simplify e2))` ***[eval of simplify]***  
  = `deg (Add(e1,e2))` ***[eval of simplify]***  
  = `max (deg e1) (deg e2)`  ***[eval of deg]***  

  - right-hand side:  
  `P(Add(e1,e2))` = `deg Add(e1,e2)`  
  = `max (deg e1) (deg e2)` ***[eval of deg]***  

`deg (simplify (Add(e1,e2)))` = `max (deg e1) (deg e2)` = `deg Add(e1,e2)`  ***[by matching left & right hand side]*** , &check;  

We want to show `P(Mul(e1,e2))`. Therefore, we want to show if `deg (simplify (Mul(e1,e2)))` = `deg Mul(e1,e2)`  

- `P(Mul(e1,e2))`  
  - left-hand side:  
  `P(Mul(e1,e2))` = `deg (simplify (Add(e1,e2)))`  
  = `deg (simp_mul (simplify e1, simplify e2))` ***[eval of simplify]***  
  = `deg (Mul(e1,e2))`  ***[eval of simplify]***  
  = `(deg e1) + (deg e2)` ***[eval of deg]***  

  - right-hand side:  
   `P(Mul(e1,e2))` = `deg Mul(e1,e2)`  
   = `(deg e1) + (deg e2)` ***[eval of deg]***  

 `deg (simplify (Mul(e1,e2)))` = `(deg e1) + (deg e2)` = `deg Mul(e1,e2)`  ***[by matching left & right hand side]*** , &check;
