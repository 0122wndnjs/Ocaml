### I. ``length l = length (reverse l)``

#### Property _P_ :  

&forall; `l` , let `P(l)` = `length l` = `length (reverse l)`

   - We must show that `P([])` holds

   - We must show that `P(x::l)` holds assuming &forall; `l1` , &forall; `l2` , `P(l)`

   - Define `lemma`  
    - Let's assume the `lemma` be the `recursive reverse function`  
      ```
      let rec rev lst = match lst with
      | [] -> []
      | h::t -> (rev t) @ [h]
      ```  
      **Property _P_ :**  
      &forall; `lst` , let `P(lst)` = `length lst` = `length (rev lst)`  

      **Base case:**  
      `P([])` = `length []` = `length (rev [])`
        - left-hand side:  
        `length []` = `0` **[eval of length]**  
        - right-hand side:  
        `length (rev [])` = `length []` **[eval of rev]**  
        - Conclusion:  
        `length []` = `0` = `length (rev [])` **[by matching left & right hand side]**  

      ***Inductive case:***  
      &forall; `lst` , `P(lst)` &rArr; `P(x::lst)`  

      >**IH: &forall; `lst`, `length lst` = `length (rev lst)`**  

      we want to show `P(x::lst)`. Therefore, we want to show if `length (x::lst)` = `length (rev (x::lst))`  

      - left-hand side:
      `length (x::lst)`
      = `1 + (length lst)` ***[eval of length]***    
      - right-hand side:  
      `length (rev (x::lst))`  
      = `length ((rev lst)@[x])` ***[eval of rev]***  
      = `length (rev lst) + 1` ***[eval of length]***  
      = `(length lst) + 1` ***[by IH]***  
      - Conclusion:  
      `length (x::lst)` = `1 + (length lst)` = `length (rev (x::lst))` ***[by matching left & right hand side]*** , &check;  

#### Base case:  

`P([])` = `length []` = `length (reverse [])`  

  - left-hand side:  
  `length []` = `0` **[by eval of length]**  

  - right-hand side:  
  `length (reverse [])` = `length []` **[by def of reverse]**  
  = `0` **[by eval of length]**  

  `length []` = `length (reverse [])` = `0` **[by matching left & right hand side]** , &check;

#### Inductive case:  

In the inductive case, we want to show that &forall; `l` , `P(l)` &rArr; `P(x::l)`

> **IH: &forall; `l` &in; `'a list`, `length l` = `length (reverse l)`**  

We want to show `P(x::l)`. Therefore, we want to show if `length (x::l)` = `length (reverse (x::l))`  

  - left-hand side:   
  `length (x::l)` = `(length l)` + `1` ***[eval of length]***  

  - right-hand side:  
  `length (reverse (x::l))` = `length ((reverse l) @ x)` ***[by lemma]***  
  = `length (reverse l) + 1` ***[eval of length]***  
  = `length l + 1` ***[by IH]***  

  `length (x::l)` = `(length l)` + `1` = `length (reverse (x::l))`  ***[by matching left & right hand side]*** , &check;  

### II. ``tail_sum l = tail_sum (reverse l)``  

#### Property _P_ :  

&forall; `l` , `P(l)` = `tail_sum l` = `tail_sum (reverse l)`  

  - We must show that `P([])` holds  

  - We must show that `P(x::l)` holds assuming &forall; `l`, `P(l)` holds  

  - Define `lemma`  
   - Let's assume the `lemma` be the `recursive reverse function`  
     ```
     let rec rev lst = match lst with
     | [] -> []
     | h::t -> (rev t) @ [h]
     ```  
     **Property _P_ :**  
     &forall; `lst` , let `P(lst)` = `length lst` = `length (rev lst)`  

     **Base case:**  
     `P([])` = `length []` = `length (rev [])`
       - left-hand side:  
       `length []` = `0` **[eval of length]**  
       - right-hand side:  
       `length (rev [])` = `length []` **[eval of rev]**  
       - Conclusion:  
       `length []` = `0` = `length (rev [])` **[by matching left & right hand side]**  

     ***Inductive case:***  
     &forall; `lst` , `P(lst)` &rArr; `P(x::lst)`  

     >**IH: &forall; `lst`, `length lst` = `length (rev lst)`**  

     we want to show `P(x::lst)`. Therefore, we want to show if `length (x::lst)` = `length (rev (x::lst))`  

     - left-hand side:
     `length (x::lst)`
     = `1 + (length lst)` ***[eval of length]***    
     - right-hand side:  
     `length (rev (x::lst))`  
     = `length ((rev lst)@[x])` ***[eval of rev]***  
     = `length (rev lst) + 1` ***[eval of length]***  
     = `(length lst) + 1` ***[by IH]***  
     - Conclusion:  
     `length (x::lst)` = `1 + (length lst)` = `length (rev (x::lst))` ***[by matching left & right hand side]*** , &check;  

#### Base case:  

`P([])` = `tail_sum []` = `tail_sum (reverse [])`

  - left-hand side:  
  `tail_sum []` = `0` **[by eval of tail_sum]**  

  - right-hand side:  
  `tail_sum (reverse [])` = `0` **[by eval of reverse]**

`tail_sum []` = `0` = `tail_sum (reverse [])` **[by matching left & right hand side]** , &check;  

#### Inductive case:  

In the inductive case, we want to show that &forall; `l` , `P(l)` &rArr; `P(x::l)`  

> **IH: &forall; `l` , `tail_sum l ` = `tail_sum (reverse l)`**  

We want to show `P(x::l)`. Therefore, we want to show if `tail_sum (x::l)` = `tail_sum (reverse (x::l))`  

  - left-hand side:  
  `tail_sum (x::l)` = `x + tail_sum l` ***[eval of tail_sum]***  
  - right-hand side:  
  `tail_sum (reverse (x::l))` = `tail_sum ((reverse l) @ x)` ***[by lemma]***  
  = `x + tail_sum (reverse l)` ***[eval of tail_sum]***   
  = `x + tail_sum l` ***[by IH]***  

  `tail_sum (x::l)` = `tail_sum (reverse (x::l))` = `x + tail_sum l` ***[by matching left & right hand side]*** , &check;  
