----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import macros
import tactic 
import nat

using nat

namespace list

-- Axioms
-- ------

variable list : Type → Type
variable nil {T : Type} : list T
variable cons {T : Type} (x : T) (l : list T) : list T

variable list_rec {T : Type} {C : list T → Type} (c : C nil)                           
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) :
    forall l : list T,  C l
 
axiom list_rec_nil {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) :
  list_rec c g nil = c

axiom list_rec_cons {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l))
    (x : T) (l : list T):
  list_rec c g (cons x l) = g x l (list_rec c g l)

theorem list_induction_on {T : Type} {P : list T → Bool} (l : list T) (Hnil : P nil)
    (Hind : forall x : T, forall l : list T, forall H : P l, P (cons x l)) : P l
:= list_rec Hnil Hind l

theorem list_cases_on {T : Type} {P : list T → Bool} (l : list T) (Hnil : P nil)
  (Hcons : forall x : T, forall l : list T, P (cons x l)) : P l
:= list_induction_on l Hnil (take x l IH, Hcons x l)

-- Concat
-- ------

definition concat {T : Type} (s t : list T) : list T
:= list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

infix 50 @ : concat
infix 50 ## : cons

theorem nil_concat {T : Type} (t : list T) : nil @ t = t
:= list_rec_nil _ _ 

theorem cons_concat {T : Type} (x : T) (s t : list T) : concat (cons x s) t = cons x (concat s t)
:= list_rec_cons _ _ _ _

theorem concat_nil {T : Type} (t : list T) : concat t nil = t
:=
  list_induction_on t 
    (nil_concat nil) 
    (take (x : T) (l : list T) (H : concat l nil = l),
      show concat (cons x l) nil = cons x l, from
        calc
          concat (cons x l) nil = cons x (concat l nil) : cons_concat x l nil
            ... = cons x l : {H})

theorem concat_assoc {T : Type} (s t u : list T) : concat (concat s t) u = concat s (concat t u)
:=
  list_induction_on s
    (calc
      concat (concat nil t) u = concat t u : { nil_concat _ }
        ... = concat nil (concat t u) : symm (nil_concat _))
    (take x l,
      assume H : concat (concat l t) u = concat l (concat t u),
      calc
        concat (concat (cons x l) t) u = concat (cons x (concat l t)) u : {cons_concat _ _ _}
          ... = cons x (concat (concat l t) u) : {cons_concat _ _ _ } 
          ... = cons x (concat l (concat t u)) : { H }
          ... = concat (cons x l) (concat t u) : {symm (cons_concat _ _ _)})

-- Length
-- ------

definition length {T : Type} : list T → ℕ
:= list_rec zero (fun x l m, succ m)

theorem length_nil {T : Type} : length (@nil T) = zero
:= list_rec_nil _ _

theorem length_cons {T : Type} (x : T) (t : list T) : length (cons x t) = succ (length t)
:= list_rec_cons _ _ _ _ 

theorem length_concat {T : Type} (s t : list T) : length (concat s t) = length s + length t
:= 
  list_induction_on s
    (calc
      length (concat nil t) = length t : {nil_concat _}
        ... = zero + length t : {symm (add_zero_left (length t))}
        ... = length (@nil T) +length t : {symm (length_nil)})
    (take x s,
      assume H : length (concat s t) = length s + length t,
      calc
        length (concat (cons x s) t ) = length (cons x (concat s t)) : {cons_concat _ _ _}
          ... = succ (length (concat s t))  : {length_cons _ _}
          ... = succ (length s + length t)  : { H }
          ... = succ (length s) + length t  : {symm (add_succ_left _ _)}
          ... = length (cons x s) + length t : {symm (length_cons _ _)})

-- Reverse
-- -------

definition reverse {T : Type} : list T → list T := list_rec nil (fun x l r, concat r (cons x nil))

theorem reverse_nil {T : Type} : reverse (@nil T) = nil
:= list_rec_nil _ _

theorem reverse_cons {T : Type} (x : T) (l : list T) : reverse (cons x l) = 
    concat (reverse l) (cons x nil)
:= list_rec_cons _ _ _ _

theorem reverse_concat {T : Type} (s t : list T) : 
    reverse (concat s t) = concat (reverse t) (reverse s)
:=
  list_induction_on s
    (calc
      reverse (concat nil t) = reverse t : { nil_concat _ }
        ... = concat (reverse t) nil : symm (concat_nil _)
        ... = concat (reverse t) (reverse nil) : {symm (reverse_nil)})
    (take x l,
      assume H : reverse (concat l t) = concat (reverse t) (reverse l),
      calc
        reverse (concat (cons x l) t) = reverse (cons x (concat l t)) : {cons_concat _ _ _}
          ... = concat (reverse (concat l t)) (cons x nil) : reverse_cons _ _  
          ... = concat (concat (reverse t) (reverse l)) (cons x nil) : { H }
          ... = concat (reverse t) (concat (reverse l) (cons x nil)) : concat_assoc _ _ _
          ... = concat (reverse t) (reverse (cons x l)) : {symm (reverse_cons _ _)})
  
theorem reverse_reverse {T : Type} (t : list T) : reverse (reverse t) = t
:= 
  list_induction_on t
    (calc
      reverse (reverse (@nil T)) = reverse nil : {reverse_nil}
        ... = nil : reverse_nil)
    (take x l,
      assume H: reverse (reverse l) = l,
      show reverse (reverse (cons x l)) = cons x l, from 
        calc
          reverse (reverse (cons x l)) = reverse (concat (reverse l) (cons x nil)) 
              : {reverse_cons x l}
            ... = concat (reverse (cons x nil)) (reverse (reverse l)) : {reverse_concat _ _}
            ... = concat (reverse (cons x nil)) l : {H}
            ... = concat (concat (reverse nil) (cons x nil)) l : {reverse_cons _ _}
            ... = concat (concat nil (cons x nil)) l : {reverse_nil}
            ... = concat (cons x nil) l : {nil_concat _}
            ... = cons x (concat nil l) : cons_concat _ _ _
            ... = cons x l : {nil_concat _})

theorem concat_cons {T : Type} (x : T) (s l : list T) : 
    concat s (cons x l) = reverse (concat (reverse l) (cons x (reverse s)))
:=
 calc
   concat s (cons x l) = concat s (cons x (concat nil l)) : {symm (nil_concat _)}
     ... = concat s (concat (cons x nil) l) : {symm (cons_concat _ _ _)}
     ... = concat (concat s (cons x nil)) l : {symm (concat_assoc _ _ _)}
     ... = concat (concat (reverse(reverse s)) (cons x nil)) l : {symm (reverse_reverse _)}
     ... = concat (reverse (cons x (reverse s))) l : {symm (reverse_cons _ _)}
     ... = concat (reverse (cons x (reverse s))) (reverse(reverse l)) : {symm (reverse_reverse _)}
     ... = reverse (concat (reverse l) (cons x (reverse s))) : {symm (reverse_concat _ _)}

-- Append
-- ------

definition append {T : Type} (a : T) : list T → list T
:= list_rec (cons a nil) (fun x l b, cons x b)

theorem append_cons {T : Type } (x : T) (a : T) (t : list T) : 
    append a (cons x t)  = cons x (append a t)
:= list_rec_cons _ _ _ _                                       

theorem append_eq_concat {T : Type} (a : T) (t : list T) : append a t = concat t (cons a nil)
:= 
  list_induction_on t
    (calc
      append a nil = cons a nil : list_rec_nil _ _
        ... = concat nil (cons a nil) : symm (nil_concat _))
     (take x l,
       assume P : append a l = concat l (cons a nil),
       calc
         append a (cons x l) = cons x (append a l) : {append_cons _ _ _}
           ... = cons x (concat l (cons a nil)) : { P }
           ... = concat (cons x l) (cons a nil) : {symm (cons_concat _ _ _)})

theorem append_eq_reverse {T : Type} (a : T) (t : list T) : 
    append a t = reverse (cons a (reverse t))
:= 
  list_induction_on t
    (calc 
     append a nil = cons a nil : (list_rec_nil _ _)
       ... = concat nil (cons a nil) : {symm (nil_concat _)}
       ... = concat (reverse nil) (cons a nil)  : {symm (reverse_nil)}    
             ... = reverse (cons a nil) : {symm (reverse_cons _ _)}
             ... = reverse (cons a (reverse nil)) : {symm (reverse_nil)})
    (take x l,
      assume H : append a l = reverse (cons a (reverse l)),
        calc
         append a (cons x l) = concat (cons x l) (cons a nil) : append_eq_concat _ _
           ... = concat (reverse (reverse (cons x l))) (cons a nil) : {symm (reverse_reverse _)}
           ... = reverse (cons a (reverse (cons x l))) : {symm (reverse_cons _ _)})

-- Head and tail
-- -------------

definition head {T : Type} (null : T) : list T → T 
:= list_rec null (fun x l h, x)

theorem head_nil {T : Type} (null : T) : head null (@nil T) = null
:= list_rec_nil _ _

theorem head_cons {T : Type} (x : T) (null : T) (t : list T) : head null (cons x t) = x
:= list_rec_cons _ _ _ _

theorem head_concat {T : Type} (s t : list T) (null : T) : 
    s ≠ nil → (head null (concat s t) = head null s)
:= 
   list_cases_on s 
     (take H : nil ≠ nil, absurd_elim (head null (concat nil t) = head null nil) (refl nil) H) 
     (take x s,
       take H : cons x s ≠ nil,
       calc
         head null (concat (cons x s) t) = head null (cons x (concat s t)) : {cons_concat _ _ _}
           ... = x : {head_cons _ _ _}
           ... = head null (cons x s) : {symm ( head_cons x null s)})

definition tail {T : Type} : list T → list T
:= list_rec nil (fun x l b, l)

theorem tail_nil {T : Type} : tail (@nil T) = nil
:= list_rec_nil _ _

theorem tail_cons {T : Type} (x : T) (l : list T) : tail (cons x l) = l
:= list_rec_cons _ _ _ _ 

theorem cons_head_tail {T : Type} (null : T) (l : list T) : 
    l ≠ nil → cons (head null l) (tail l) = l
:= 
  list_cases_on l
    (assume H : nil ≠ nil,
      absurd_elim _ (refl _) H)
    (take x l, 
      assume H : cons x l ≠ nil,
      calc
        cons (head null (cons x l)) (tail (cons x l)) = cons x (tail (cons x l)) : {head_cons _ _ _}
          ... = cons x l : {tail_cons _ _})

-- List membership
-- ---------------

definition In {T : Type} (f : T) : list T → Bool
:= list_rec false (fun x l b,(b ∨ (x = f)))

theorem In_nil {T : Type} (f : T) : In f nil ↔ false
:= list_rec_nil _ _

theorem In_cons {T : Type} (x : T) (f : T) (l : list T) : In f (cons x l) ↔ (In f l ∨ x = f)
:= list_rec_cons _ _ _ _   

theorem In_concat_imp_or {T : Type} (f : T) (s t : list T) : In f (concat s t) → In f s ∨ In f t
:=
  list_induction_on s
    (assume H : In f (concat nil t),
      have H1 : In f t, from subst H (nil_concat t),
      show In f nil ∨ In f t, from or_intro_right _ H1)
    (take x l,
      assume IH : In f (concat l t) → In f l ∨ In f t,
      assume H : In f (concat (cons x l) t),
      have H1 : In f (cons x (concat l t)), from subst H (cons_concat _ _ _),
      have H2 : In f (concat l t) ∨ x = f, from (In_cons _ _ _) ◂ H1,
      have H3 : (In f l ∨ In f t) ∨ x = f, from or_imp_or_left H2 IH,
      have H4 : (In f l ∨ x = f) ∨ In f t, from or_right_comm _ _ _ ◂ H3,
      show In f (cons x l) ∨ In f t, from subst H4 (symm (In_cons _ _ _)))

theorem In_or_imp_concat {T : Type} (f : T) (s t : list T) : 
  In f s ∨ In f t → In f (concat s t)
:=
  list_induction_on s
    (assume H : In f nil ∨ In f t,
      have H1 : false ∨ In f t, from subst H (In_nil f),
      have H2 : In f t, from subst H1 (or_false_right _),
      show In f (concat nil t), from subst H2 (symm (nil_concat _)))
    (take x l,
      assume IH : In f l ∨ In f t → In f (concat l t),
      assume H : (In f (cons x l)) ∨ (In f t),
      have H1 : ((In f l) ∨ (x = f)) ∨ (In f t), from subst H (In_cons _ _ _),
      have H2 : (In f t) ∨ ((In f l) ∨ (x = f)), from subst H1 (or_comm _ _),
      have H3 : ((In f t) ∨ (In f l)) ∨ (x = f), from subst H2 (symm (or_assoc _ _ _)),
      have H4 : ((In f l) ∨ (In f t)) ∨ (x = f), from subst H3 (or_comm _ _),
      have H5 : (In f (concat l t)) ∨ (x = f), from  (or_imp_or_left H4 IH),
      have H6 : (In f (cons x (concat l t))), from subst H5 (symm (In_cons _ _ _)),
      show  (In f (concat (cons x l) t)), from subst H6 (symm (cons_concat _ _ _)))

theorem In_concat {T : Type} (f : T) (s t : list T) : In f (concat s t) ↔ In f s ∨ In f t 
:= iff_intro (In_concat_imp_or _ _ _) (In_or_imp_concat _ _ _)

theorem In_split {T : Type} (f : T) (s : list T) : In f s → ∃ a b : list T, s = concat a (cons f b)
:= 
  list_induction_on s 
    (assume H : In f nil,
      have H1  : In f nil ↔ false, from (In_nil f),
      show ∃ a b : list T, nil = concat a (cons f b), from absurd_elim _ H (eqf_elim H1))  
    (take x l,
      assume P1 : In f l → ∃ a b : list T, l = concat a (cons f b),
      assume P2 : In f (cons x l),
      have P3 : In f l ∨ x = f, from subst P2 (In_cons _ _ _),
      show ∃ a b : list T, cons x l = concat a (cons f b), from
        or_elim P3
          (assume Q1 : In f l,
            obtain (a : list T) (PQ : ∃ b, l = concat a (cons f b)), from P1 Q1,
            obtain (b : list T) (RS : l = concat a (cons f b)), from PQ,
            exists_intro (cons x a)
              (exists_intro b
                (calc 
                  cons x l = cons x (concat a (cons f b)) : { RS }
                    ... = concat (cons x a) (cons f b) : (symm (cons_concat _ _ _)))))
          (assume Q2 : x = f,
            exists_intro nil
              (exists_intro l
                (calc 
                  cons x l = concat nil (cons x l) : (symm (nil_concat _))
                    ... = concat nil (cons f l) : {Q2}))))

-- Position
-- --------

-- rename to find?
definition position {T : Type} (f : T) : list T → ℕ
:= list_rec zero (fun x l b, if x = f then succ zero else (if In f l then succ b else b))

theorem nil_position {T : Type} (f : T) : position f nil = zero
:=list_rec_nil _ _

theorem cons_position {T : Type} (f x : T) (l : list T) : position f (cons x l) =  if (x = f) then (succ zero) else (if (In f l) then (succ (position f l)) else (position f l))
:= list_rec_cons _ _ _ _

definition list_succ {T : Type} (f : T) (null : T) : list T → T
:= list_rec null (fun x l b, if (position f l = succ zero) then x else b)

theorem cons_list_succ {T : Type} (f x : T) (null : T) (l : list T) : 
  list_succ f null (cons x l) =  if (position f l = succ zero) then x else list_succ f null l 
:= list_rec_cons _ _ _ _

definition nth_element {T : Type} (n : ℕ ) (null : T) : list T → T
:= list_rec null (fun x l b, if (n > succ (length l)) then null else list_succ b null (cons x l))

theorem cons_nth_element {T : Type} (n : ℕ) (null x : T) (l : list T) : 
    nth_element n null (cons x l) = 
      if n > succ (length l) then null else list_succ (nth_element n null l) null (cons x l)
:= list_rec_cons _ _ _ _

  --rank of f = position of f in a sorted list
definition rank (f : ℕ) : list ℕ → ℕ
:= list_rec zero (fun x l b, if ((x ≥ f) ∨ (¬ (In f (cons x l)))) then b else (succ b))         

theorem nil_rank (f : ℕ) : rank f nil = zero
:= list_rec_nil _ _

theorem cons_rank (f x : ℕ) (l : list ℕ) : rank f (cons x l) =  if ((x ≥ f) ∨ (¬ (In f (cons x l)))) then rank f l else (succ (rank f l))
:= list_rec_cons _ _ _ _

theorem neg_In_rank (f : ℕ) (l : list ℕ) : ¬ (In f l) → (rank f l = zero)
:= 
  list_induction_on l 
    (assume P1 : ¬ (In f nil),
      show rank f nil = zero, from nil_rank f) 
    (take x l,
      assume H1 : (¬ (In f l)) → (rank f l = zero),
      assume P2 : ¬ (In f (cons x l)),
      have P3 :   ¬ ((In f l) ∨ (x = f)),from subst P2 (In_cons _ _ _),
      have P4 :  (¬ (In f l)) ∧ (¬ (x = f)),from subst P3 (not_or _ _),
      have P5 : (¬ (In f l))               ,from and_elim_left P4,
      have P6 : (x ≥ f) ∨ (¬(In f (cons x l))),from or_intro_right (x ≥ f) P2,
      have H2 : ((x ≥ f) ∨ (¬(In f l))) ,from or_intro_right (x ≥ f) P5,
      have P7 : rank f (cons x l) = 
          if (x ≥ f ∨ ¬ (In f (cons x l))) then rank f l else succ (rank f l), 
        from (cons_rank _ _ _),
      have P8 : (if ((x ≥ f) ∨ (¬ (In f (cons x l)))) then rank f l else succ (rank f l)) = 
          rank f l, 
        from imp_if_eq P6 _ _,
      have P9 : rank f (cons x l) = rank f l, from trans P7 P8, 
      have H5 : rank f l = zero, from H1 P5,
      show rank f (cons x l) = zero, from trans P9 H5)

theorem neg_In_position {T : Type} (l : list T) (f : T) : (¬ (In f l)) → (position f l =zero)
:= 
  list_induction_on l 
    (assume P1 : ¬ (In f nil),
      show position f nil = zero , from nil_position f) 
    (take x l,
      assume H1 : (¬ (In f l)) → (position f l =zero),
      assume P1 : (¬ (In f (cons x l))),
      have P2 : ¬ ( In f l ∨ (x = f)) , from subst P1 (In_cons _ _ _),
      have P3 : (¬ (In f l)) ∧ (¬(x = f)),from subst P2 (not_or _ _),
      have P4 : ¬ (x = f) ,from (and_elim_right P3),
      have P5 : position f (cons x l) = 
          (if (x = f) then (succ zero) else 
            (if (In f l) then (succ (position f l)) else (position f l))), 
        from (cons_position _ _ _),
      have P6 : (if x = f then succ zero else 
            (if (In f l) then (succ (position f l)) else (position f l))) = 
          (if (In f l) then (succ (position f l)) else (position f l)), 
        from (not_imp_if_eq P4 _ _),
      have P7 : position f (cons x l) = 
          (if (In f l) then (succ (position f l)) else (position f l)), 
        from trans P5 P6,
      have P8 : (¬ (In f l)),from (and_elim_left P3),
      have P9 :(if (In f l) then (succ (position f l)) else (position f l)) = (position f l),
        from (not_imp_if_eq P8 _ _),
      have P10 : position f (cons x l) = position f l ,from trans P7 P9,
      have H2 : position f l = zero ,from H1 P8,
      show position f (cons x l) = zero, from trans P10 H2)

definition insert (null f : ℕ) : list ℕ → list ℕ
:= list_rec (cons f nil) (fun x l b, if (f ≥ x) then (cons x b) else cons (head null b) (cons x (tail b))) -- Assumes l to be sorted

theorem cons_insert (null f x : ℕ) (l : list ℕ) : insert null f (cons x l) = (if (f ≥ x) then (cons x (insert null f l)) else cons (head null (insert null f l)) (cons x (tail (insert null f l))))
:=list_rec_cons _ _ _ _

definition asort (null : ℕ) : list ℕ → list ℕ
:= list_rec nil (fun x l b, insert null x b) 

theorem asort_nil (null : ℕ) : asort null nil = nil
:= list_rec_nil _ _

definition dsort (null : ℕ) (l : list ℕ) : list ℕ
:= reverse (asort null l)

--theorem asort_rank (f : ℕ) (l : list ℕ) : rank f l = rank f (asort null l)
--:= list_rec (
--show rank f nil = rank f (asort null nil), from congr2 _ (symm (asort_nil null))
--) (
-- take x l,
-- assume H1 : rank f l = rank f (asort null l)
-- by_cases
 

--) l 




-- theorem rank_asort (null f : ℕ) (l : list ℕ) : rank f l = position f (asort null l)
-- := by_cases (In f l) _
-- (assume H1 : ¬ (In f l),
--  have P   : rank f l = zero ,from (neg_In_rank _ _ H1),
--  have Q   : zero  = position f l ,from (symm (neg_In_position _ _ H1)),
--  show rank f l = position f l ,from trans P Q)
   
  
     




 
definition map {T : Type} {S : Type} (P : T → S) (null : S) : list T → list S
:= list_rec (cons null nil) (fun x l b, cons (P x) b)

definition foldr {T : Type} {S : Type} (f : T → T → T) (null : T) : list T → T
:= list_rec null (fun x l b,f x b)

-- l = x [a b c d]                                                  
-- b =  f(c f( b (f a d))))      f( a (f b (f c d)))  f (f (f a b) c) d                         
-- r =  f (c f(b f(a (f x d))))  f  a  f  b  f c d    f  ( f (f  ( f x a) b) c) d  



definition last {T : Type} (null : T) (l : list T) : T
:= head null (reverse l) 

