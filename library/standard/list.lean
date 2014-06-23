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
unary_nat

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
-- infix 50 ## : cons

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
:= list_rec 0 (fun x l m, succ m)

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

add_rewrite length_nil length_cons

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

  -- keep?
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

definition head {T : Type} (x0 : T) : list T → T
:= list_rec x0 (fun x l h, x)

theorem head_nil {T : Type} (x0 : T) : head x0 (@nil T) = x0
:= list_rec_nil _ _

theorem head_cons {T : Type} (x : T) (x0 : T) (t : list T) : head x0 (cons x t) = x
:= list_rec_cons _ _ _ _

theorem head_concat {T : Type} (s t : list T) (x0 : T) :
    s ≠ nil → (head x0 (concat s t) = head x0 s)
:=
   list_cases_on s
     (take H : nil ≠ nil, absurd_elim (head x0 (concat nil t) = head x0 nil) (refl nil) H)
     (take x s,
       take H : cons x s ≠ nil,
       calc
         head x0 (concat (cons x s) t) = head x0 (cons x (concat s t)) : {cons_concat _ _ _}
           ... = x : {head_cons _ _ _}
           ... = head x0 (cons x s) : {symm ( head_cons x x0 s)})

definition tail {T : Type} : list T → list T
:= list_rec nil (fun x l b, l)

theorem tail_nil {T : Type} : tail (@nil T) = nil
:= list_rec_nil _ _

theorem tail_cons {T : Type} (x : T) (l : list T) : tail (cons x l) = l
:= list_rec_cons _ _ _ _

theorem cons_head_tail {T : Type} (x0 : T) (l : list T) :
    l ≠ nil → cons (head x0 l) (tail l) = l
:=
  list_cases_on l
    (assume H : nil ≠ nil,
      absurd_elim _ (refl _) H)
    (take x l,
      assume H : cons x l ≠ nil,
      calc
        cons (head x0 (cons x l)) (tail (cons x l)) = cons x (tail (cons x l)) : {head_cons _ _ _}
          ... = cons x l : {tail_cons _ _})

-- List membership
-- ---------------

definition mem {T : Type} (f : T) : list T → Bool
:= list_rec false (fun x l b,(b ∨ (x = f)))

infix 50 ∈ : mem

theorem mem_nil {T : Type} (f : T) : mem f nil ↔ false
:= list_rec_nil _ _

theorem mem_cons {T : Type} (x : T) (f : T) (l : list T) : mem f (cons x l) ↔ (mem f l ∨ x = f)
:= list_rec_cons _ _ _ _

theorem mem_concat_imp_or {T : Type} (f : T) (s t : list T) : mem f (concat s t) → mem f s ∨ mem f t
:=
  list_induction_on s
    (assume H : mem f (concat nil t),
      have H1 : mem f t, from subst H (nil_concat t),
      show mem f nil ∨ mem f t, from or_intro_right _ H1)
    (take x l,
      assume IH : mem f (concat l t) → mem f l ∨ mem f t,
      assume H : mem f (concat (cons x l) t),
      have H1 : mem f (cons x (concat l t)), from subst H (cons_concat _ _ _),
      have H2 : mem f (concat l t) ∨ x = f, from (mem_cons _ _ _) ◂ H1,
      have H3 : (mem f l ∨ mem f t) ∨ x = f, from or_imp_or_left H2 IH,
      have H4 : (mem f l ∨ x = f) ∨ mem f t, from or_right_comm _ _ _ ◂ H3,
      show mem f (cons x l) ∨ mem f t, from subst H4 (symm (mem_cons _ _ _)))

theorem mem_or_imp_concat {T : Type} (f : T) (s t : list T) :
  mem f s ∨ mem f t → mem f (concat s t)
:=
  list_induction_on s
    (assume H : mem f nil ∨ mem f t,
      have H1 : false ∨ mem f t, from subst H (mem_nil f),
      have H2 : mem f t, from subst H1 (or_false_right _),
      show mem f (concat nil t), from subst H2 (symm (nil_concat _)))
    (take x l,
      assume IH : mem f l ∨ mem f t → mem f (concat l t),
      assume H : (mem f (cons x l)) ∨ (mem f t),
      have H1 : ((mem f l) ∨ (x = f)) ∨ (mem f t), from subst H (mem_cons _ _ _),
      have H2 : (mem f t) ∨ ((mem f l) ∨ (x = f)), from subst H1 (or_comm _ _),
      have H3 : ((mem f t) ∨ (mem f l)) ∨ (x = f), from subst H2 (symm (or_assoc _ _ _)),
      have H4 : ((mem f l) ∨ (mem f t)) ∨ (x = f), from subst H3 (or_comm _ _),
      have H5 : (mem f (concat l t)) ∨ (x = f), from  (or_imp_or_left H4 IH),
      have H6 : (mem f (cons x (concat l t))), from subst H5 (symm (mem_cons _ _ _)),
      show  (mem f (concat (cons x l) t)), from subst H6 (symm (cons_concat _ _ _)))

theorem mem_concat {T : Type} (f : T) (s t : list T) : mem f (concat s t) ↔ mem f s ∨ mem f t
:= iff_intro (mem_concat_imp_or _ _ _) (mem_or_imp_concat _ _ _)

theorem mem_split {T : Type} (f : T) (s : list T) :
    mem f s → ∃ a b : list T, s = concat a (cons f b)
:=
  list_induction_on s
    (assume H : mem f nil,
      have H1  : mem f nil ↔ false, from (mem_nil f),
      show ∃ a b : list T, nil = concat a (cons f b), from absurd_elim _ H (eqf_elim H1))
    (take x l,
      assume P1 : mem f l → ∃ a b : list T, l = concat a (cons f b),
      assume P2 : mem f (cons x l),
      have P3 : mem f l ∨ x = f, from subst P2 (mem_cons _ _ _),
      show ∃ a b : list T, cons x l = concat a (cons f b), from
        or_elim P3
          (assume Q1 : mem f l,
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
definition find {T : Type} (x : T) : list T → ℕ
:= list_rec 0 (fun y l b, if x = y then 0 else succ b)

theorem find_nil {T : Type} (f : T) : find f nil = 0
:=list_rec_nil _ _

theorem find_cons {T : Type} (x y : T) (l : list T) : find x (cons y l) =
    if x = y then 0 else succ (find x l)
:= list_rec_cons _ _ _ _

theorem not_mem_find {T : Type} (l : list T) (x : T) : ¬ mem x l → find x l = length l
:=
  @list_induction_on T (λl, ¬ mem x l → find x l = length l) l
--  list_induction_on l
    (assume P1 : ¬ mem x nil,
      show find x nil = length nil, from
        calc
          find x nil = 0 : find_nil _
            ... = length nil : by simp)
     (take y l,
       assume IH : ¬ (mem x l) → find x l = length l,
       assume P1 : ¬ (mem x (cons y l)),
       have P2 : ¬ (mem x l ∨ (y = x)), from subst P1 (mem_cons _ _ _),
       have P3 : ¬ (mem x l) ∧ (y ≠ x),from subst P2 (not_or _ _),
       have P4 : x ≠ y, from ne_symm (and_elim_right P3),
       calc
          find x (cons y l) = succ (find x l) :
              trans (find_cons _ _ _) (not_imp_if_eq P4 _ _)
            ... = succ (length l) : {IH (and_elim_left P3)}
            ... = length (cons y l) : symm (length_cons _ _))

-- nth element
-- -----------

definition nth_element {T : Type} (x0 : T) (l : list T) (n : ℕ) : T
:= nat::rec (λl, head x0 l) (λm f l, f (tail l)) n l

theorem nth_element_zero {T : Type} (x0 : T) (l : list T) : nth_element x0 l 0 = head x0 l
:= hcongr1 (nat::rec_zero _ _) l

theorem nth_element_succ {T : Type} (x0 : T) (l : list T) (n : ℕ) :
    nth_element x0 l (succ n) = nth_element x0 (tail l) n
:= hcongr1 (nat::rec_succ _ _ _) l

-- theorem ... (n : ℕ) : ∀l, ....

-- definition list_succ {T : Type} (x : T) (x0 : T) : list T → T
-- := list_rec x0 (fun y l b, if (find x l = succ zero) then y else b)

-- theorem cons_list_succ {T : Type} (f x : T) (x0 : T) (l : list T) :
--   list_succ f x0 (cons x l) =  if (find f l = succ zero) then x else list_succ f x0 l
-- := list_rec_cons _ _ _ _

-- definition nth_element {T : Type} (n : ℕ) (x0 : T) : list T → T
-- := list_rec x0 (fun x l b, if (n > succ (length l)) then x0 else list_succ b x0 (cons x l))

-- theorem cons_nth_element {T : Type} (n : ℕ) (x0 x : T) (l : list T) :
--     nth_element n x0 (cons x l) =
--       if n > succ (length l) then x0 else list_succ (nth_element n x0 l) x0 (cons x l)
-- := list_rec_cons _ _ _ _

-- rank
-- ----

  --rank of f = position of f in a sorted list
definition rank (f : ℕ) : list ℕ → ℕ
:= list_rec zero (fun x l b, if ((x ≥ f) ∨ (¬ (mem f (cons x l)))) then b else (succ b))

theorem rank_nil (f : ℕ) : rank f nil = zero
:= list_rec_nil _ _

theorem rank_cons (f x : ℕ) (l : list ℕ) : rank f (cons x l) =  if ((x ≥ f) ∨ (¬ (mem f (cons x l)))) then rank f l else (succ (rank f l))
:= list_rec_cons _ _ _ _

theorem not_mem_rank (f : ℕ) (l : list ℕ) : ¬ (mem f l) → (rank f l = zero)
:=
  list_induction_on l
    (assume P1 : ¬ (mem f nil),
      show rank f nil = zero, from rank_nil f)
    (take x l,
      assume H1 : (¬ (mem f l)) → (rank f l = zero),
      assume P2 : ¬ (mem f (cons x l)),
      have P3 :   ¬ ((mem f l) ∨ (x = f)),from subst P2 (mem_cons _ _ _),
      have P4 :  (¬ (mem f l)) ∧ (¬ (x = f)),from subst P3 (not_or _ _),
      have P5 : (¬ (mem f l))               ,from and_elim_left P4,
      have P6 : (x ≥ f) ∨ (¬(mem f (cons x l))),from or_intro_right (x ≥ f) P2,
      have H2 : ((x ≥ f) ∨ (¬(mem f l))) ,from or_intro_right (x ≥ f) P5,
      have P7 : rank f (cons x l) =
          if (x ≥ f ∨ ¬ (mem f (cons x l))) then rank f l else succ (rank f l),
        from (rank_cons _ _ _),
      have P8 : (if ((x ≥ f) ∨ (¬ (mem f (cons x l)))) then rank f l else succ (rank f l)) =
          rank f l,
        from imp_if_eq P6 _ _,
      have P9 : rank f (cons x l) = rank f l, from trans P7 P8,
      have H5 : rank f l = zero, from H1 P5,
      show rank f (cons x l) = zero, from trans P9 H5)

-- Sorting a list of natural numbers
-- ---------------------------------

  -- Assumes l to be sorted
definition insert (n : ℕ) : list ℕ → list ℕ
:= list_rec (cons n nil) (fun m l b, if n ≥ m then (cons m b) else cons n (cons m l))

theorem insert_nil (n : ℕ) : insert n nil = cons n nil
:= list_rec_nil _ _

theorem insert_cons (n m : ℕ) (l : list ℕ) : insert n (cons m l) =
    (if n ≥ m then cons m (insert n l) else cons n (cons m l))
:=list_rec_cons _ _ _ _

definition asort : list ℕ → list ℕ
:= list_rec nil (fun x l b, insert x b)

theorem asort_nil : asort nil = nil
:= list_rec_nil _ _

theorem asort_cons (n : ℕ) (l : list ℕ) : asort (cons n l) = insert n (asort l)
:= list_rec_cons _ _ _ _

theorem mem_head {T : Type} (f x0 : T) (l : list T) (A : f ≠ x0) : (head x0 l = f) → (mem f l)
:= list_induction_on l
  (assume H : head x0 nil = f,
   have H1 : x0 = f,from subst H (head_nil x0),
   show mem f nil,from absurd_elim _ (symm H1) A)
  (take x l,
   assume H1 : (head x0 l = f) → (mem f l),
   assume P1 : head x0 (cons x l) = f,
   have P2 : x = f,from subst P1 (head_cons _ _ _),
   have P3 : (mem f l) ∨ (x = f),from (or_intro_right _ P2),
   show mem f (cons x l),from subst P3 (symm (mem_cons _ _ _)))

theorem mem_tail {T : Type} (f : T) (l : list T) : mem f (tail l) → mem f l
:= list_induction_on l
  (assume H : mem f (tail nil),
    show mem f nil ,from subst H (tail_nil))
  (take x l,
    assume P : mem f (tail l) → mem f l,
    assume H : mem f (tail (cons x l)),
    have H1  : mem f l, from subst H (tail_cons x l),
    have H2  : (mem f l) ∨ (x = f),from (or_intro_left _ H1),
    show mem f (cons x l),from subst H2 (symm (mem_cons x f l)))

theorem mem_insert (n m : ℕ) (l : list ℕ) : mem n (insert m l) → (mem n l) ∨ (m = n)
:=
  list_induction_on l
    (assume H1 : mem n (insert m nil),
      have H2 : mem n (cons m nil),from subst H1 (insert_nil _),
      show  mem n nil ∨ (m = n), from subst H2 (mem_cons _ _ _))
    (take x l,
       assume H : mem n (insert m l) → (mem n l) ∨ (m = n),
       assume P : mem n (insert m (cons x l)),
       have P1 : mem n (if m ≥ x then cons x (insert m l) else cons m (cons x l)),
         from subst P (insert_cons _ _ _),
       by_cases                         --To break the if-else structure in P1
         (assume Q : m ≥ x,
           have Q1 : mem n (cons x (insert m l)), from subst P1 (imp_if_eq Q _ _),
           have Q2 : mem n (insert m l) ∨ (x = n), from subst Q1 (mem_cons _ _ _),
           have Q3 : ((mem n l) ∨ (m = n)) ∨ (x = n), from or_imp_or_left Q2 H,
           have Q4 : ((((mem n l) ∨ (m = n)) ∨ (x = n)) = (((mem n l) ∨ (x = n)) ∨ (m = n))),
             by simp,
           show mem n (cons x l) ∨ (m = n), from subst (Q4 ◂ Q3) (symm (mem_cons _ _ _)))
        (assume R : ¬ (m ≥ x),              --Else condition
           have R1 : mem n (cons m (cons x l)), from subst P1 (not_imp_if_eq R _ _),
           show mem n (cons x l) ∨ (m = n), from (mem_cons _ _ _) ◂ R1))




-- theorem mem_whateva (x0 f g : ℕ) (l : list ℕ) : (¬ mem f l) ∧ (g ≠ f) → ¬ mem f (insert x0 g l)
-- := list_induction_on l
-- (
--  assume H1 : (¬ mem f nil) ∧ (g ≠ f),
--  have H2   : ¬ (mem f nil ∨ (g = f)), from subst H1 (symm (not_or _ _)),
--  have H3   : ¬ (mem f (cons g nil)), from subst H2 (symm (mem_cons _ _ _)),
--  show        ¬ (mem f (insert x0 g nil)),from subst H3 (symm (nil_insert _ _)))

-- ( take x l,
--   assume H : (¬ mem f l) ∧ (g ≠ f) → ¬ mem f (insert x0 g l),
--   assume P :  ¬ mem f (cons x l) ∧ (g ≠ f),
--   have P1 : ¬ (mem f l ∨ (x = f)),from subst P (mem_cons _ _ _),
--   have P2 : (¬ mem f l) ∧ (x ≠ f),from subst P1 (not_or _ _),




-- theorem bwah (x0 : ℕ) (f : ℕ) (l : list ℕ) : ¬ mem f l → ¬ mem f (asort x0 l)
-- := list_induction_on l
-- ( assume H : ¬ mem f nil,
--   have H1  : (¬ mem f (asort x0 nil)) = (¬ mem f (nil)), from congr2 (fun x : list ℕ , ¬ mem f x) (asort_nil x0),
--   have H2  : (¬ mem f nil) = (¬ false),from congr2 (fun x : Bool , ¬ x) (mem_nil f),
--   have H3  : ¬ false, from not_false_trivial,
--   have H4  : ¬ mem f nil ,from subst H3 (symm H2),
--   show  ¬ mem f (asort x0 nil) ,from subst H4 (symm H1) )
-- ( take x l,
--   assume H  : ¬ mem f l → ¬ mem f (asort x0 l),
--   assume P1 : ¬ mem f (cons x l),
--   assume P2 : ¬ mem f (cons x (cons m n)) = long int (int )
--   have R    : ¬ mem f




-- definition dsort (x0 : ℕ) (l : list ℕ) : list ℕ
-- := reverse (asort x0 l)

-- theorem asort_rank (f : ℕ) (l : list ℕ) : rank f l = rank f (asort x0 l)
-- := list_rec (
-- show rank f nil = rank f (asort x0 nil), from congr2 _ (symm (asort_nil x0))
-- ) (
-- take x l,
-- assume H1 : rank f l = rank f (asort x0 l)
-- by_cases (mem f (cons x l)) _
-- (assume P : ¬ mem f (cons x l),
--  have  P1 : rank f (cons x l) = zero ,from (neg_mem_rank _ _ H1),
--  have  P2 :





-- ) l




-- theorem rank_asort (x0 f : ℕ) (l : list ℕ) : rank f l = position f (asort x0 l)
-- := by_cases (mem f l) _
-- (assume H1 : ¬ (mem f l),
--  have P   : rank f l = zero ,from (neg_mem_rank _ _ H1),
--  have Q   : zero  = position f l ,from (symm (neg_mem_position _ _ H1)),
--  show rank f l = position f l ,from trans P Q)


definition map {T : Type} {S : Type} (P : T → S) (x0 : S) : list T → list S
:= list_rec (cons x0 nil) (fun x l b, cons (P x) b)

definition foldr {T : Type} {S : Type} (f : T → T → T) (x0 : T) : list T → T
:= list_rec x0 (fun x l b,f x b)

-- l = x [a b c d]
-- b =  f(c f( b (f a d))))      f( a (f b (f c d)))  f (f (f a b) c) d
-- r =  f (c f(b f(a (f x d))))  f  a  f  b  f c d    f  ( f (f  ( f x a) b) c) d

definition last {T : Type} (x0 : T) (l : list T) : T
:= head x0 (reverse l)

