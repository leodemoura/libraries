----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-------------------------------------------------- axioms
import kernel
import macros

variable nat : Type
alias ℕ : nat
unary_nat -- enables numerals

namespace nat

variable zero : nat
variable succ : nat -> nat
axiom nat_rec {P : nat → Type} (x : P 0)  (f : ∀m : nat, P m → P (succ m)) (m:nat) : P m
axiom nat_rec_zero {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) :
    nat_rec x f 0 = x
axiom nat_rec_succ {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) (n : nat) :
    nat_rec x f (succ n) = f n  (nat_rec x f n)

-------------------------------------------------- succ pred

theorem induction_on {P : nat → Bool} (a : nat) (H1 : P 0)
    (H2 : ∀ (n : nat) (IH : P n), P (succ n)) : P a
:= nat_rec H1 H2 a

theorem succ_ne_zero (n : nat) : succ n ≠ 0
:=
  not_intro
    (take H : succ n = 0,
      have H2 : true = false, from
        (let f : nat -> Bool := (nat_rec false (fun a b,true))
          in calc
            true = f (succ n) : symm (nat_rec_succ _ _ _)
             ... = f 0 : {H}
	           ... = false : nat_rec_zero _ _),
      absurd H2 true_ne_false)

definition pred (n : nat) := nat_rec 0 (fun m x, m) n

theorem pred_zero : pred 0 = 0
:= nat_rec_zero _ _
theorem pred_succ (n : nat) : pred (succ n) = n
:= nat_rec_succ _ _ _

set_opaque pred true

theorem zero_or_succ (n : nat) : n = 0 ∨ n = succ (pred n)
:=
  induction_on n
    (or_intro_left _ (refl 0))
    (take m IH, or_intro_right _
      (show succ m = succ (pred (succ m)), from congr2 succ (symm (pred_succ m))))

theorem zero_or_succ2 (n : nat) : n = 0 ∨ ∃k, n = succ k
:= or_imp_or (zero_or_succ n) (assume H, H) (assume H : n = succ (pred n), exists_intro (pred n) H)

-- rename to case? (nat::case)
theorem nat_case {P : nat → Bool} (n : nat) (H1: P 0) (H2 : ∀m, P (succ m)) : P n
:=
  induction_on n H1 (take m IH, H2 m)

-- rename to discriminate? (nat::discriminate)
theorem nat_discriminate {B : Bool} {n : nat} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B
:=
  or_elim (zero_or_succ n)
    (take H3 : n = 0, H1 H3)
    (take H3 : n = succ (pred n), H2 (pred n) H3)

theorem succ_inj {n m : nat} (H : succ n = succ m) : n = m
:=
  calc
    n = pred (succ n) : symm (pred_succ n)
  ... = pred (succ m) : {H}
  ... = m : pred_succ m

theorem succ_ne_self (n : nat) : succ n ≠ n
:=
  not_intro (induction_on n
    (take H : 1 = 0,
      have ne : 1 ≠ 0, from succ_ne_zero 0,
      absurd H ne)
    (take k IH H, IH (succ_inj H)))

theorem decidable_equality (n m : nat) : n = m ∨ n ≠ m
:=
  have general : ∀n, n = m ∨ n ≠ m, from
    induction_on m
      (take n : nat,
        nat_discriminate
          (assume H : n = 0, or_intro_left _ H)
          (take l : nat,
            assume H : n = succ l,
            have H2 : n ≠ 0, from subst (succ_ne_zero l) (symm H),
            or_intro_right _ H2))
      (take k : nat,
        assume IH : ∀n, n = k ∨ n ≠ k,
        take n : nat,
        nat_discriminate
          (assume H : n = 0,
            have H2 : n ≠ succ k, from subst (ne_symm (succ_ne_zero k)) (symm H),
            or_intro_right _ H2)
          (take l : nat,
            assume H : n = succ l,
            or_imp_or (IH l)
              (take H2 : l = k,
                show n = succ k, from trans H (congr2 succ H2))
              (take H2 : l ≠ k,
                show n ≠ succ k, from
                  not_intro
                    (take H4 : n = succ k,
                      have H5 : succ l = succ k, from trans (symm H) H4,
                      have H6 : l = k, from succ_inj H5,
                      absurd H6 H2)))),
    general n

theorem two_step_induction_on {P : nat → Bool} (a : nat) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a
:=
  have stronger : P a ∧ P (succ a), from
    induction_on a
      (and_intro H1 H2)
      (take k IH,
        have IH1 : P k, from and_elim_left IH,
        have IH2 : P (succ k), from and_elim_right IH,
          and_intro IH2 (H3 k IH1 IH2)),
    and_elim_left stronger

theorem sub_induction {P : nat → nat → Bool} (n m : nat) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m
:=
  have general : ∀m, P n m, from
  induction_on n
    (take m : nat, H1 m)
    (take k : nat,
      assume IH : ∀m, P k m,
      take m : nat,
      nat_discriminate
        (assume Hm : m = 0,
          subst (H2 k) (symm Hm))
        (take l : nat,
          assume Hm : m = succ l,
          subst (H3 k l (IH l)) (symm Hm))),
  general m



-------------------------------------------------- add

definition add (n m : nat) := nat_rec n (fun k x, succ x) m
infixl 65 +  : add

theorem add_zero_right (n:nat) : n + 0 = n
:= nat_rec_zero _ _
theorem add_succ_right (n m:nat) : n + succ m = succ (n + m)
:= nat_rec_succ _ _ _

set_opaque add true

---------- comm, assoc

theorem add_zero_left (n:nat) : 0 + n = n
:=
  induction_on n
    (add_zero_right 0)
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add_succ_right _ _
   	    ... = succ m : {IH})

theorem add_succ_left (n m:nat) : (succ n) + m = succ (n + m)
:=
  induction_on m
    (calc
      succ n + 0 = succ n : add_zero_right (succ n)
        ... = succ (n + 0) : {symm (add_zero_right n)})
    (take k IH,
      calc
        succ n + succ k = succ (succ n + k) : add_succ_right _ _
          ... = succ (succ (n + k)) : {IH}
          ... = succ (n + succ k) : {symm (add_succ_right _ _)})

theorem add_comm (n m:nat) : n + m = m + n
:=
  induction_on m
    (trans (add_zero_right _) (symm (add_zero_left _)))
    (take k IH,
      calc
        n + succ k = succ (n+k) : add_succ_right _ _
          ... = succ (k + n) : {IH}
          ... = succ k + n : symm (add_succ_left _ _))

theorem add_move_succ (n m:nat) : succ n + m = n + succ m
:=
  calc
    succ n + m = succ (n + m) : add_succ_left n m
      ... = n +succ m : symm (add_succ_right n m)

theorem add_comm_succ (n m:nat) : n + succ m = m + succ n
:=
  calc
    n + succ m = succ n + m : symm (add_move_succ n m)
      ... = m + succ n : add_comm (succ n) m

theorem add_assoc (n m k:nat) : (n + m) + k = n + (m + k)
:=
  induction_on k
    (calc
      (n + m) + 0 = n + m : add_zero_right _
        ... = n + (m + 0) : {symm (add_zero_right m)})
    (take l IH,
      calc
        (n + m) + succ l = succ ((n + m) + l) : add_succ_right _ _
          ... = succ (n + (m + l)) : {IH}
          ... = n + succ (m + l) : symm (add_succ_right _ _)
          ... = n + (m + succ l) : {symm (add_succ_right _ _)})

theorem add_comm_left (n m k : nat) : n + (m + k) = m + (n + k)
:= left_comm add_comm add_assoc n m k

theorem add_comm_right (n m k : nat) : n + m + k = n + k + m
:= right_comm add_comm add_assoc n m k

--the following is used a couple of times in int.lean
theorem add_switch (n m k l : nat) : n + m + (k + l) = n + k + (m + l)
:=
  calc
    n + m + (k + l) = n + m + k + l : symm (add_assoc (n + m) k l)
      ... = n + k + m + l : {add_comm_right n m k}
      ... = n + k + (m + l) : add_assoc (n + k) m l

---------- inversion

--rename to add_inj_left
theorem add_right_inj {n m k : nat} : n + m = n + k → m = k
:=
  induction_on n
    (take H : 0 + m = 0 + k,
      calc
        m = 0 + m : symm (add_zero_left m)
          ... = 0 + k : H
          ... = k : add_zero_left k)
    (take (n : nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
      have H2 : succ (n + m) = succ (n + k),
      from calc
        succ (n + m) = succ n + m : symm (add_succ_left n m)
          ... = succ n + k : H
          ... = succ (n + k) : add_succ_left n k,
      have H3 : n + m = n + k, from succ_inj H2,
      IH H3)

--rename to add_inj_right
theorem add_left_inj {n m k : nat} (H : n + m = k + m) : n = k
:=
  have H2 : m + n = m + k,
    from calc
      m + n = n + m : add_comm m n
      ... = k + m : H
      ... = m + k : add_comm k m,
    add_right_inj H2

theorem add_eq_zero_left {n m : nat} : n + m = 0 → n = 0
:=
  induction_on n
    (take (H : 0 + m = 0), refl 0)
    (take k IH,
      assume (H : succ k + m = 0),
      absurd_elim (succ k = 0)
        (show succ (k + m) = 0, from
          calc
            succ (k + m) = succ k + m : symm (add_succ_left k m)
              ... = 0 : H)
        (succ_ne_zero (k + m)))

theorem add_eq_zero_right {n m : nat} (H : n + m = 0) : m = 0
:= add_eq_zero_left (trans (add_comm m n) H)

theorem add_eq_zero {n m : nat} (H : n + m = 0) : n = 0 ∧ m = 0
:= and_intro (add_eq_zero_left H) (add_eq_zero_right H)

-- add_eq_self below

---------- misc

theorem add_one (n:nat) : n + 1 = succ n
:=
  calc
    n + 1 = succ (n + 0) : add_succ_right _ _
      ... = succ n : {add_zero_right _}

theorem add_one_left (n:nat) : 1 + n = succ n
:=
  calc
    1 + n = succ (0 + n) : add_succ_left _ _
      ... = succ n : {add_zero_left _}

--the following theorem has a terrible name, but since the name is not a substring or superstring of another name, it is at least easy to globally replace it
theorem induction_plus_one {P : nat → Bool} (a : nat) (H1 : P 0)
    (H2 : ∀ (n : nat) (IH : P n), P (n + 1)) : P a
:= nat_rec H1 (take n IH, subst (H2 n IH) (add_one n)) a

add_rewrite add_zero_left add_zero_right

-------------------------------------------------- mul

definition mul (n m : nat) := nat_rec 0 (fun m x, x + n) m
infixl 70 *  : mul

theorem mul_zero_right (n:nat) : n * 0 = 0
:= nat_rec_zero _ _
theorem mul_succ_right (n m:nat) : n * succ m = n * m + n
:= nat_rec_succ _ _ _

set_opaque mul true

---------- comm, distr, assoc, identity

theorem mul_zero_left (n:nat) : 0 * n = 0
:=
  induction_on n
    (mul_zero_right 0)
    (take m IH,
      calc
        0 * succ m = 0 * m + 0 : mul_succ_right _ _
          ... = 0 * m : add_zero_right _
          ... = 0 : IH)

theorem mul_succ_left (n m:nat) : (succ n) * m = (n * m) + m
:=
  induction_on m
    (calc
      succ n * 0 = 0 : mul_zero_right _
        ... = n * 0 : symm (mul_zero_right _)
        ... = n * 0 + 0 	: symm (add_zero_right _))
    (take k IH,
      calc
        succ n * succ k = (succ n * k) + succ n : mul_succ_right _ _
            ... = (n * k) + k + succ n : {IH}
            ... = (n * k) + (k + succ n) : add_assoc _ _ _
--            ... = (n * k) + succ (k + n) : {add_succ_right _ _}
--            ... = (n * k) + (succ k + n) : {symm (add_succ_left _ _)}
--            ... = (n * k) + (n + succ k) : {add_comm _ _}
--use either next line or three previous lines
   	      ... = (n * k) + (n + succ k) : {add_comm_succ _ _}
            ... = (n * k) + n + succ k : symm (add_assoc _ _ _)
            ... = (n * succ k) + succ k : {symm (mul_succ_right n k)})

theorem mul_comm (n m:nat) : n * m = m * n
:=
  induction_on m
    (trans (mul_zero_right _) (symm (mul_zero_left _)))
    (take k IH,
      calc
        n * succ k = n * k + n : mul_succ_right _ _
          ... = k * n + n : {IH}
          ... = (succ k) * n : symm (mul_succ_left _ _))

theorem mul_add_distr_right (n m k : nat) : (n + m) * k = n * k + m * k
:=
  induction_on k
    (calc
      (n + m) * 0 = 0 : mul_zero_right _
        ... = 0 + 0 : symm (add_zero_right _)
        ... = n * 0 + 0 : {symm (mul_zero_right _)}
        ... = n * 0 + m * 0 : {symm (mul_zero_right _)})
    (take l IH,
      calc
        (n + m) * succ l = (n + m) * l + (n + m) : mul_succ_right _ _
          ... = n * l + m * l + (n + m) : {IH}
          ... = n * l + m * l + n + m : symm (add_assoc _ _ _)
          ... = n * l + n + m * l + m : {add_comm_right _ _ _}
          ... = n * l + n + (m * l + m) : add_assoc _ _ _
          ... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
          ... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})

theorem mul_add_distr_left (n m k : nat) : n * (m + k) = n * m + n * k
:=
  calc
    n * (m + k) = (m + k) * n : mul_comm _ _
      ... = m * n + k * n : mul_add_distr_right _ _ _
      ... = n * m + k * n : {mul_comm _ _}
      ... = n * m + n * k : {mul_comm _ _}

theorem mul_assoc (n m k:nat) : (n * m) * k = n * (m * k)
:=
  induction_on k
    (calc
      (n * m) * 0 = 0 : mul_zero_right _
        ... = n * 0 : symm (mul_zero_right _)
        ... = n * (m * 0) : {symm (mul_zero_right _)})
    (take l IH,
      calc
        (n * m) * succ l = (n * m) * l + n * m : mul_succ_right _ _
          ... = n * (m * l) + n * m : {IH}
          ... = n * (m * l + m) : symm (mul_add_distr_left _ _ _)
          ... = n * (m * succ l) : {symm (mul_succ_right _ _)})

theorem mul_comm_left (n m k : nat) : n * (m * k) = m * (n * k)
:= left_comm mul_comm mul_assoc n m k

theorem mul_comm_right (n m k : nat) : n * m * k = n * k * m
:= right_comm mul_comm mul_assoc n m k

theorem mul_one_right (n : nat) : n * 1 = n
:=
  calc
    n * 1 = n * 0 + n : mul_succ_right n 0
      ... = 0 + n : {mul_zero_right n}
      ... = n : add_zero_left n

theorem mul_one_left (n : nat) : 1 * n = n
:=
  calc
    1 * n = n * 1 : mul_comm _ _
      ... = n : mul_one_right n

---------- inversion

theorem mul_eq_zero {n m : nat} (H : n * m = 0) : n = 0 ∨ m = 0
:=
  nat_discriminate
    (take Hn : n = 0, or_intro_left _ Hn)
    (take (k : nat),
      assume (Hk : n = succ k),
      nat_discriminate
        (take (Hm : m = 0), or_intro_right _ Hm)
        (take (l : nat),
          assume (Hl : m = succ l),
          have Heq : succ (k * succ l + l) = n * m, from
            symm (calc
              n * m = n * succ l : {Hl}
                ... = succ k * succ l : {Hk}
                ... = k * succ l + succ l : mul_succ_left _ _
                ... = succ (k * succ l + l) : add_succ_right _ _),
          absurd_elim _  (trans Heq H) (succ_ne_zero _)))

-- see more under "positivity" below

add_rewrite mul_zero_left mul_zero_right

-------------------------------------------------- le

definition le (n m:nat) : Bool := exists k:nat, n + k = m
infix  50 <= : le
infix  50 ≤  : le

theorem le_intro {n m k : nat} (H : n + k = m) : n ≤ m
:= exists_intro k H

theorem le_elim {n m : nat} (H : n ≤ m) : ∃ k, n + k = m
:= H

set_opaque le true

---------- partial order (totality is part of lt)

theorem le_refl (n : nat) : n ≤ n
:= le_intro (add_zero_right n)

theorem le_zero (n : nat) : 0 ≤ n
:= le_intro (add_zero_left n)

theorem le_zero_inv {n : nat} (H : n ≤ 0) : n = 0
:=
  obtain (k : nat) (Hk : n + k = 0), from le_elim H,
  add_eq_zero_left Hk

theorem not_succ_le_zero (n : nat) : ¬ succ n ≤ 0
:=
  not_intro
    (assume H : succ n ≤ 0,
      have H2 : succ n = 0, from le_zero_inv H,
      absurd H2 (succ_ne_zero n))

theorem le_trans {n m k : nat} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k
:=
  obtain (l1 : nat) (Hl1 : n + l1 = m), from le_elim H1,
  obtain (l2 : nat) (Hl2 : m + l2 = k), from le_elim H2,
  le_intro
    (calc
      n + (l1 + l2) =  n + l1 + l2 : symm (add_assoc n l1 l2)
        ... = m + l2 : {Hl1}
        ... = k : Hl2)

theorem le_antisym {n m : nat} (H1 : n ≤ m) (H2 : m ≤ n) : n = m
:=
  obtain (k : nat) (Hk : n + k = m), from (le_elim H1),
  obtain (l : nat) (Hl : m + l = n), from (le_elim H2),
  have L1 : k + l = 0, from
    add_right_inj
      (calc
        n + (k + l) = n + k + l : symm (add_assoc n k l)
          ... = m + l : {Hk}
          ... = n : Hl
          ... = n + 0 : symm (add_zero_right n)),
  have L2 : k = 0, from add_eq_zero_left L1,
  calc
    n = n + 0 : symm (add_zero_right n)
      ... = n  + k : {symm L2}
      ... = m : Hk

---------- interaction with add

theorem le_add_right (n m : nat) : n ≤ n + m
:= le_intro (refl (n + m))

theorem le_add_left (n m : nat) : n ≤ m + n
:= le_intro (add_comm n m)

theorem add_le_left {n m : nat} (H : n ≤ m) (k : nat) : k + n ≤ k + m
:=
  obtain (l : nat) (Hl : n + l = m), from (le_elim H),
  le_intro
    (calc
        k + n + l  = k + (n + l) : add_assoc k n l
          ... = k + m : {Hl})

theorem add_le_right {n m : nat} (H : n ≤ m) (k : nat) : n + k ≤ m + k
:= subst (subst (add_le_left H k) (add_comm k n)) (add_comm k m)

theorem add_le {n m k l : nat} (H1 : n ≤ k) (H2 : m ≤ l) : n + m ≤ k + l
:= le_trans (add_le_right H1 m) (add_le_left H2 k)

theorem add_le_left_inv {n m k : nat} (H : k + n ≤ k + m) : n ≤ m
:=
  obtain (l : nat) (Hl : k + n + l = k + m), from (le_elim H),
  le_intro (add_right_inj
    calc
        k + (n + l)  = k + n + l : symm (add_assoc k n l)
          ... = k + m : Hl )

theorem add_le_right_inv {n m k : nat} (H : n + k ≤ m + k) : n ≤ m
:= add_le_left_inv (subst (subst H (add_comm n k)) (add_comm m k))

theorem add_le_inv {n m k l : nat} (H1 : n + m ≤ k + l) (H2 : k ≤ n) : m ≤ l
:=
  obtain (a : nat) (Ha : k + a = n), from le_elim H2,
  have H3 : k + (a + m) ≤ k + l, from subst (subst H1 (symm Ha)) (add_assoc k a m),
  have H4 : a + m ≤ l, from add_le_left_inv H3,
  show m ≤ l, from le_trans (le_add_left m a) H4

---------- interaction with succ and pred

theorem succ_le {n m : nat} (H : n ≤ m) : succ n ≤ succ m
:= subst (subst (add_le_right H 1) (add_one n)) (add_one m)

theorem succ_le_inv {n m : nat} (H : succ n ≤ succ m) :  n ≤ m
:= add_le_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem le_self_succ (n : nat) : n ≤ succ n
:= le_intro (add_one n)

theorem succ_le_right {n m : nat} (H : n ≤ m) : n ≤ succ m
:= le_trans H (le_self_succ m)

theorem succ_le_left_or {n m : nat} (H : n ≤ m) : succ n ≤ m ∨ n = m
:=
  obtain (k : nat) (Hk : n + k = m), from (le_elim H),
  nat_discriminate
    (assume H3 : k = 0,
      have Heq : n = m,
        from calc
          n = n + 0 : symm (add_zero_right n)
            ... = n + k : {symm H3}
            ... = m : Hk,
      or_intro_right _ Heq)
    (take l:nat,
      assume H3 : k = succ l,
      have Hlt : succ n ≤ m, from
        (le_intro
          (calc
            succ n + l = n + succ l : add_move_succ n l
              ... = n + k : {symm H3}
              ... = m : Hk)),
      or_intro_left _ Hlt)

theorem succ_le_left {n m : nat} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m
:= resolve_left (succ_le_left_or H1) H2

theorem succ_le_right_inv {n m : nat} (H : n ≤ succ m) : n ≤ m ∨ n = succ m
:=
  or_imp_or (succ_le_left_or H)
    (take H2 : succ n ≤ succ m, show n ≤ m, from succ_le_inv H2)
    (take H2 : n = succ m, H2)

theorem succ_le_left_inv {n m : nat} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m
:=
  and_intro
    (le_trans (le_self_succ n) H)
    (not_intro
      (assume H2 : n = m,
        have H3 : succ n ≤ n, from subst H (symm H2),
        have H4 : succ n = n, from le_antisym H3 (le_self_succ n),
        show false, from absurd H4 (succ_ne_self n)))

theorem le_pred_self (n : nat) : pred n ≤ n
:=
  nat_case n
    (subst (le_refl 0) (symm pred_zero))
    (take k : nat, subst (le_self_succ k) (symm (pred_succ k)))

theorem pred_le {n m : nat} (H : n ≤ m) : pred n ≤ pred m
:=
  nat_discriminate
    (take Hn : n = 0,
      have H2 : pred n = 0,
        from calc
          pred n = pred 0 : {Hn}
             ... = 0 : pred_zero,
      subst (le_zero (pred m)) (symm H2))
    (take k : nat,
      assume Hn : n = succ k,
      obtain (l : nat) (Hl : n + l = m), from le_elim H,
      have H2 : pred n + l = pred m,
        from calc
          pred n + l = pred (succ k) + l : {Hn}
            ... = k + l : {pred_succ k}
            ... = pred (succ (k + l)) : symm (pred_succ (k + l))
            ... = pred (succ k + l) : {symm (add_succ_left k l)}
            ... = pred (n + l) : {symm Hn}
            ... = pred m : {Hl},
      le_intro H2)


theorem pred_le_left_inv {n m : nat} (H : pred n ≤ m) : n ≤ m ∨ n = succ m
:=
  nat_discriminate
    (take Hn : n = 0,
      or_intro_left _ (subst (le_zero m) (symm Hn)))
    (take k : nat,
      assume Hn : n = succ k,
      have H2 : pred n = k,
        from calc
          pred n = pred (succ k) : {Hn}
             ... = k : pred_succ k,
      have H3 : k ≤ m, from subst H H2,
      have H4 : succ k ≤ m ∨ k = m, from succ_le_left_or H3,
      show n ≤ m ∨ n = succ m, from
        or_imp_or H4
          (take H5 : succ k ≤ m, show n ≤ m, from subst H5 (symm Hn))
          (take H5 : k = m, show n = succ m, from subst Hn H5))

---------- interaction with mul

theorem mul_le_left {n m : nat} (H : n ≤ m) (k : nat) : k * n ≤ k * m
:=
  obtain (l : nat) (Hl : n + l = m), from (le_elim H),
  induction_on k
    (have H2 : 0 * n = 0 * m,
      from calc
        0 * n = 0 : mul_zero_left n
          ... = 0 * m : symm (mul_zero_left m),
      show 0 * n ≤ 0 * m, from subst (le_refl (0 * n)) H2)
    (take (l : nat),
      assume IH : l * n ≤ l * m,
      have H2 : l * n + n ≤ l * m + m, from add_le IH H,
      have H3 : succ l * n ≤ l * m + m, from subst H2 (symm (mul_succ_left l n)),
      show succ l * n ≤ succ l * m, from subst H3 (symm (mul_succ_left l m)))

theorem mul_le_right {n m : nat} (H : n ≤ m) (k : nat) : n * k ≤ m * k
:= subst (subst (mul_le_left H k) (mul_comm k n)) (mul_comm k m)

theorem mul_le {n m k l : nat} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l
:= le_trans (mul_le_right H1 m) (mul_le_left H2 k)

-- mul_le_[left|right]_inv below

-------------------------------------------------- lt

definition lt (n m : nat) := succ n ≤ m
infix 50 <  : lt

theorem lt_intro {n m k : nat} (H : succ n + k = m) : n < m
:= le_intro H

theorem lt_elim {n m : nat} (H : n < m) : ∃ k, succ n + k = m
:= le_elim H

theorem lt_intro2 (n m : nat) : n < n + succ m
:= lt_intro (add_move_succ n m)

---------- basic facts

theorem lt_ne {n m : nat} (H : n < m) : n ≠ m
:= and_elim_right (succ_le_left_inv H)

theorem lt_irrefl (n : nat) : ¬ n < n
:= not_intro (assume H : n < n, absurd (refl n) (lt_ne H))

theorem lt_zero (n : nat) : 0 < succ n
:= succ_le (le_zero n)

theorem lt_zero_inv (n : nat) : ¬ n < 0
:= not_succ_le_zero n

theorem lt_positive {n m : nat} (H : n < m) : exists k, m = succ k
:=
  nat_discriminate
    (take (Hm : m = 0), absurd_elim _ (subst H Hm) (lt_zero_inv n))
    (take (l : nat) (Hm : m = succ l), exists_intro l Hm)

---------- interaction with le

theorem lt_le_succ {n m : nat} (H : n < m) : succ n ≤ m
:= H

theorem le_succ_lt {n m : nat} (H : succ n ≤ m) : n < m
:= H

theorem self_lt_succ (n : nat) : n < succ n
:= le_refl (succ n)

theorem lt_le {n m : nat} (H : n < m) : n ≤ m
:= and_elim_left (succ_le_left_inv H)

theorem le_lt_or {n m : nat} (H : n ≤ m) : n < m ∨ n = m
:= succ_le_left_or H

theorem le_lt {n m : nat} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m
:= succ_le_left H1 H2

theorem le_lt_succ {n m : nat} (H : n ≤ m) : n < succ m
:= succ_le H

theorem lt_succ_le {n m : nat} (H : n < succ m) : n ≤ m
:= succ_le_inv H

---------- trans, antisym

theorem lt_le_trans {n m k : nat} (H1 : n < m) (H2 : m ≤ k) : n < k
:= le_trans H1 H2

theorem lt_trans {n m k : nat} (H1 : n < m) (H2 : m < k) : n < k
:= lt_le_trans H1 (lt_le H2)

theorem le_lt_trans {n m k : nat} (H1 : n ≤ m) (H2 : m < k) : n < k
:= le_trans (succ_le H1) H2

theorem le_lt_antisym {n m : nat} (H : n ≤ m) : ¬ m < n
:= not_intro (take H2 : m < n, absurd (le_lt_trans H H2) (lt_irrefl n))

theorem lt_le_antisym {n m : nat} (H : n < m) : ¬ m ≤ n
:= not_intro (take H2 : m ≤ n, absurd (lt_le_trans H H2) (lt_irrefl n))

theorem lt_antisym {n m : nat} (H : n < m) : ¬ m < n
:= le_lt_antisym (lt_le H)

---------- interaction with add

theorem add_lt_left {n m : nat} (H : n < m) (k : nat) : k + n < k + m
:= @subst _ _ _ (fun x, x ≤ k + m) (add_le_left H k) (add_succ_right k n)

theorem add_lt_right {n m : nat} (H : n < m) (k : nat) : n + k < m + k
:= subst (subst (add_lt_left H k) (add_comm k n)) (add_comm k m)

theorem add_le_lt {n m k l : nat} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l
:= le_lt_trans (add_le_right H1 m) (add_lt_left H2 k)

theorem add_lt_le {n m k l : nat} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l
:= lt_le_trans (add_lt_right H1 m) (add_le_left H2 k)

theorem add_lt {n m k l : nat} (H1 : n < k) (H2 : m < l) : n + m < k + l
:= add_lt_le H1 (lt_le H2)

theorem add_lt_left_inv {n m k : nat} (H : k + n < k + m) : n < m
:= add_le_left_inv (subst H (symm (add_succ_right k n)))

theorem add_lt_right_inv {n m k : nat} (H : n + k < m + k) : n < m
:= add_lt_left_inv (subst (subst H (add_comm n k)) (add_comm m k))

---------- interaction with succ (see also the interaction with le)

theorem succ_lt {n m : nat} (H : n < m) : succ n < succ m
:= subst (subst (add_lt_right H 1) (add_one n)) (add_one m)

theorem succ_lt_inv {n m : nat} (H : succ n < succ m) :  n < m
:= add_lt_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem lt_self_succ (n : nat) : n < succ n
:= le_refl (succ n)

theorem succ_lt_right {n m : nat} (H : n < m) : n < succ m
:= lt_trans H (lt_self_succ m)

---------- totality of lt and le

theorem le_or_lt (n m : nat) : n ≤ m ∨ m < n
:=
  induction_on n
    (or_intro_left _ (le_zero m))
    (take (k : nat),
      assume IH : k ≤ m ∨ m < k,
      or_elim IH
        (assume H : k ≤ m,
          obtain (l : nat) (Hl : k + l = m), from le_elim H,
          nat_discriminate
            (assume H2 : l = 0,
              have H3 : m = k,
                from calc
                  m = k + l : symm Hl
                    ... = k + 0 : {H2}
                    ... = k : add_zero_right k,
              have H4 : m < succ k, from subst (lt_self_succ m) H3,
              or_intro_right _ H4)
            (take l2 : nat,
              assume H2 : l = succ l2,
              have H3 : succ k + l2 = m,
                from calc
                  succ k + l2 = k + succ l2 : add_move_succ k l2
                    ... = k + l : {symm H2}
                    ... = m : Hl,
              or_intro_left _ (le_intro H3)))
        (assume H : m < k, or_intro_right _ (succ_lt_right H)))

theorem trichotomy_alt (n m : nat) : (n < m ∨ n = m) ∨ m < n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, le_lt_or H) (assume H : m < n, H)

theorem trichotomy (n m : nat) : n < m ∨ n = m ∨ m < n
:= iff_elim_left (or_assoc _ _ _) (trichotomy_alt n m)

theorem le_total (n m : nat) : n ≤ m ∨ m ≤ n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, H) (assume H : m < n, lt_le H)

theorem not_lt_imp_le {n m : ℕ} (H : ¬ n < m) : m ≤ n
:= resolve_left (le_or_lt m n) H

theorem not_le_imp_lt {n m : ℕ} (H : ¬ n ≤ m) : m < n
:= resolve_right (le_or_lt n m) H

-- interaction with mul under "positivity"

theorem strong_induction {P : nat → Bool} (n : nat) (IH : ∀n, (∀m, m < n → P m) → P n) : P n
:=
  have stronger : ∀k, k ≤ n → P k, from
    induction_on n
      (take (k : nat),
        assume H : k ≤ 0,
        have H2 : k = 0, from le_zero_inv H,
        have H3 : ∀m, m < k → P m, from
          (take m : nat,
            assume H4 : m < k,
            have H5 : m < 0, from subst H4 H2,
            absurd_elim _ H5 (lt_zero_inv m)),
        show P k, from IH k H3)
      (take l : nat,
        assume IHl : ∀k, k ≤ l → P k,
        take k : nat,
        assume H : k ≤ succ l,
        or_elim (succ_le_right_inv H)
          (assume H2 : k ≤ l, show P k, from IHl k H2)
          (assume H2 : k = succ l,
            have H3 : ∀m, m < k → P m, from
              (take m : nat,
                assume H4 : m < k,
                have H5 : m ≤ l, from lt_succ_le (subst H4 H2),
                show P m, from IHl m H5),
            show P k, from IH k H3)),
  stronger n (le_refl n)

theorem add_eq_self {n m : nat} (H : n + m = n) : m = 0
:=
  nat_discriminate
    (take Hm : m = 0, Hm)
    (take k : nat,
      assume Hm : m = succ k,
      have H2 : succ n + k = n,
        from calc
          succ n + k = n + succ k : add_move_succ n k
            ... = n + m : {symm Hm}
            ... = n : H,
      have H3 : n < n, from lt_intro H2,
      have H4 : n ≠ n, from lt_ne H3,
      absurd_elim _ (refl n) H4)

-------------------------------------------------- ge, gt

definition ge (n m : nat) := m ≤ n
infix 50 >= : ge
infix 50 ≥  : ge

definition gt (n m : nat) := m < n
infix 50 >  : gt

-- prove some theorems, like ge_le le_ge lt_gt gt_lt?

-------------------------------------------------- positivity

-- " _ > 0" is the preferred way to describe that a number is positive

---------- basic

-- see also lt_zero

theorem zero_or_positive (n : nat) : n = 0 ∨ n > 0
:= or_imp_or (or_flip (le_lt_or (le_zero n))) (take H : 0 = n, symm H) (take H : n > 0, H)

theorem succ_positive {n m : nat} (H : n = succ m) : n > 0
:= subst (lt_zero m) (symm H)

theorem ne_zero_positive {n : nat} (H : n ≠ 0) : n > 0
:= or_elim (zero_or_positive n) (take H2 : n = 0, absurd_elim _ H2 H) (take H2 : n > 0, H2)

theorem positive_succ {n : nat} (H : n > 0) : exists l, n = succ l
:=
  nat_discriminate
    (take H2, absurd_elim _ (subst H H2) (lt_irrefl 0))
    (take l Hl, exists_intro l Hl)

theorem add_positive_right (n : nat) {k : nat} (H : k > 0) : n + k > n
:=
  obtain (l : nat) (Hl : k = succ l), from positive_succ H,
  subst (lt_intro2 n l) (symm Hl)

theorem add_positive_left (n : nat) {k : nat} (H : k > 0) : k + n > n
:= subst (add_positive_right n H) (add_comm n k)

---------- mul

theorem mul_positive {n m : nat} (Hn : n > 0) (Hm : m > 0) : n * m > 0
:=
  obtain (k : nat) (Hk : n = succ k), from positive_succ Hn,
  obtain (l : nat) (Hl : m = succ l), from positive_succ Hm,
  succ_positive calc
    n * m = succ k * m : {Hk}
      ... = succ k * succ l : {Hl}
      ... = succ k * l + succ k : mul_succ_right (succ k) l
      ... = succ (succ k * l + k) : add_succ_right _ _

theorem mul_positive_inv_left {n m : nat} (H : n * m > 0) : n > 0
:=
  nat_discriminate
    (assume H2 : n = 0,
      have H3 : n * m = 0,
        from calc
          n * m = 0 * m : {H2}
            ... = 0 : mul_zero_left m,
      have H4 : 0 > 0, from subst H H3,
      absurd_elim _ H4 (lt_irrefl 0))
    (take l : nat,
      assume Hl : n = succ l,
      subst (lt_zero l) (symm Hl))

theorem mul_positive_inv_right {n m : nat} (H : n * m > 0) : m > 0
:= mul_positive_inv_left (subst H (mul_comm n m))

theorem mul_left_inj {n m k : nat} (Hn : n > 0) (H : n * m = n * k) : m = k
:=
  have general : ∀m, n * m = n * k → m = k, from
    induction_on k
      (take m:nat,
        assume H : n * m = n * 0,
        have H2 : n * m = 0,
          from calc
            n * m = n * 0 : H
              ... = 0 : mul_zero_right n,
        have H3 : n = 0 ∨ m = 0, from mul_eq_zero H2,
        resolve_right H3 (ne_symm (lt_ne Hn)))
      (take (l : nat),
        assume (IH : ∀ m, n * m = n * l → m = l),
        take (m : nat),
        assume (H : n * m = n * succ l),
        have H2 :  n * succ l > 0, from mul_positive Hn (lt_zero l),
        have H3 : m > 0, from mul_positive_inv_right (subst H2 (symm H)),
        obtain (l2:nat) (Hm : m = succ l2), from positive_succ H3,
        have H4 : n * l2 + n = n * l + n,
          from calc
            n * l2 + n = n * succ l2 : symm (mul_succ_right n l2)
              ... = n * m : {symm Hm}
              ... = n * succ l : H
              ... = n * l + n : mul_succ_right n l,
        have H5 : n * l2 = n * l, from add_left_inj H4,
        calc
          m = succ l2 : Hm
        ... = succ l : {IH l2 H5}),
  general m H

theorem mul_right_inj {n m k : nat} (Hm : m > 0) (H : n * m = k * m) : n = k
:= mul_left_inj Hm (subst (subst H (mul_comm n m)) (mul_comm k m))

-- mul_eq_one below

---------- interaction of mul with le and lt


theorem mul_lt_left {n m k : nat} (Hk : k > 0) (H : n < m) : k * n < k * m
:=
  have H2 : k * n < k * n + k, from add_positive_right (k * n) Hk,
  have H3 : k * n + k ≤ k * m, from subst (mul_le_left H k) (mul_succ_right k n),
  lt_le_trans H2 H3

theorem mul_lt_right {n m k : nat} (Hk : k > 0) (H : n < m)  : n * k < m * k
:= subst (subst (mul_lt_left Hk H) (mul_comm k n)) (mul_comm k m)

theorem mul_le_lt {n m k l : nat} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) : n * m < k * l
:= le_lt_trans (mul_le_right H1 m) (mul_lt_left Hk H2)

theorem mul_lt_le {n m k l : nat} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) : n * m < k * l
:= le_lt_trans (mul_le_left H2 n) (mul_lt_right Hl H1)

theorem mul_lt {n m k l : nat} (H1 : n < k) (H2 : m < l) : n * m < k * l
:=
  have H3 : n * m ≤ k * m, from mul_le_right (lt_le H1) m,
  have H4 : k * m < k * l, from mul_lt_left (le_lt_trans (le_zero n) H1) H2,
  le_lt_trans H3 H4

theorem mul_lt_left_inv {n m k : nat} (H : k * n < k * m) : n < m
:=
  have general : ∀ m, k * n < k * m → n < m, from
    induction_on n
      (take m : nat,
        assume H2 : k * 0 < k * m,
        have H3 : 0 < k * m, from subst H2 (mul_zero_right k),
        show 0 < m, from mul_positive_inv_right H3)
      (take l : nat,
        assume IH : ∀ m, k * l < k * m → l < m,
        take m : nat,
        assume H2 : k * succ l < k * m,
        have H3 : 0 < k * m, from le_lt_trans (le_zero _) H2,
        have H4 : 0 < m, from mul_positive_inv_right H3,
        obtain (l2 : nat) (Hl2 : m = succ l2), from positive_succ H4,
        have H5 : k * l + k < k * m, from subst H2 (mul_succ_right k l),
        have H6 : k * l + k < k * succ l2, from subst H5 Hl2,
        have H7 : k * l + k < k * l2 + k, from subst H6 (mul_succ_right k l2),
        have H8 : k * l < k * l2, from add_lt_right_inv H7,
        have H9 : l < l2, from IH l2 H8,
        have H10 : succ l < succ l2, from succ_lt H9,
        show succ l < m, from subst H10 (symm Hl2)),
  general m H

theorem mul_lt_right_inv {n m k : nat} (H : n * k < m * k) : n < m
:= mul_lt_left_inv (subst (subst H (mul_comm n k)) (mul_comm m k))

theorem mul_le_left_inv {n m k : nat} (H : succ k * n ≤ succ k * m) : n ≤ m
:=
  have H2 : succ k * n < succ k * m + succ k, from le_lt_trans H (lt_intro2 _ _),
  have H3 : succ k * n < succ k * succ m, from subst H2 (symm (mul_succ_right (succ k) m)),
  have H4 : n < succ m, from mul_lt_left_inv H3,
  show n ≤ m, from lt_succ_le H4

theorem mul_le_right_inv {n m k : nat} (H : n * succ m ≤ k * succ m) : n ≤ k
:= mul_le_left_inv (subst (subst H (mul_comm n (succ m))) (mul_comm k (succ m)))

theorem mul_eq_one_left {n m : nat} (H : n * m = 1) : n = 1
:=
  have H2 : n * m > 0, from subst (lt_zero 0) (symm H),
  have H3 : n > 0, from mul_positive_inv_left H2,
  have H4 : m > 0, from mul_positive_inv_right H2,
  or_elim (le_or_lt n 1)
    (assume H5 : n ≤ 1,
      show n = 1, from le_antisym H5 H3)
    (assume H5 : n > 1,
      have H6 : n * m ≥ 2 * 1, from mul_le H5 H4,
      have H7 : 1 ≥ 2, from subst (subst H6 H) (mul_one_right 2),
      absurd_elim _ (self_lt_succ 1) (le_lt_antisym H7))
  -- obtain
  -- obtain (k : nat) (Hm : m = succ k), from (mul_eq_succ_right H),
  -- obtain (l1 : nat) (Hn : n = succ l1), from (mul_eq_succ_left H),
  --   nat_discriminate
  --     (take Hl : l1 = 0,
  --       calc
  --         n = succ l1 : Hn
  --           ... = 1 : {Hl})
  --     (take (l2 : nat),
  --     assume (Hl : l1 = succ l2),
  --     have H2 : 1 = succ (succ (succ (succ l2) * k + l2)),
  --       from calc
  --         1 = n * m : symm H
  --           ... = n * succ k : {Hm}
  --           ... = succ l1 * succ k : {Hn}
  --           ... = succ (succ l2) * succ k : {Hl}
  --           ... = succ (succ l2) * k + succ (succ l2) : {mul_succ_right _ _}
  --           ... = succ (succ (succ l2) * k + succ l2): add_succ_right _ _
  --           ... = succ (succ (succ (succ l2) * k + l2)) : {add_succ_right _ _},
  --       have H3 : 0 = succ (succ (succ l2) * k + l2), from succ_inj H2,
  --       absurd_elim _ (symm H3) (succ_ne_zero _))

theorem mul_eq_one_right {n m : nat} (H : n * m = 1) : m = 1
:= mul_eq_one_left (subst H (mul_comm n m))

theorem mul_eq_one {n m : nat} (H : n * m = 1) : n = 1 ∧ m = 1
:= and_intro (mul_eq_one_left H) (mul_eq_one_right H)

set_opaque lt true

-------------------------------------------------- sub

definition sub (n m : nat) : nat := nat_rec n (fun m x, pred x) m
infixl 65 - : sub

theorem sub_zero_right (n : nat) : n - 0 = n
:= nat_rec_zero _ _
theorem sub_succ_right (n m : nat) : n - succ m = pred (n - m)
:= nat_rec_succ _ _ _

set_opaque sub true

theorem sub_zero_left (n : nat) : 0 - n = 0
:=
  induction_on n (sub_zero_right 0)
    (take k : nat,
      assume IH : 0 - k = 0,
      calc
        0 - succ k = pred (0 - k) : sub_succ_right 0 k
          ... = pred 0 : {IH}
          ... = 0 : pred_zero)

--theorem sub_succ_left (n m : nat) : pred (succ n - m) = n - m
-- :=
--   induction_on m
--     (calc
--       pred (succ n - 0) = pred (succ n) : {sub_zero_right (succ n)}
--         ... = n : pred_succ n
--         ... = n - 0 : symm (sub_zero_right n))
--     (take k : nat,
--       assume IH : pred (succ n - k) = n - k,
--       _)

theorem sub_succ_succ (n m : nat) : succ n - succ m = n - m
:=
  induction_on m
    (calc
      succ n - 1 = pred (succ n - 0) : sub_succ_right (succ n) 0
        ... = pred (succ n) : {sub_zero_right (succ n)}
        ... = n : pred_succ n
        ... = n - 0 : symm (sub_zero_right n))
    (take k : nat,
      assume IH : succ n - succ k = n - k,
      calc
        succ n - succ (succ k) = pred (succ n - succ k) : sub_succ_right (succ n) (succ k)
          ... = pred (n - k) : {IH}
          ... = n - succ k : symm (sub_succ_right n k))

theorem sub_one (n : nat) : n - 1 = pred n
:=
  calc
    n - 1 = pred (n - 0) : sub_succ_right n 0
      ... = pred n : {sub_zero_right n}

theorem sub_self (n : nat) : n - n = 0
:= induction_on n (sub_zero_right 0) (take k IH, trans (sub_succ_succ k k) IH)

theorem sub_add_add_right (n m k : nat) : (n + k) - (m + k) = n - m
:=
  induction_on k
    (calc
      (n + 0) - (m + 0) = n - (m + 0) : {add_zero_right _}
        ... = n - m : {add_zero_right _})
    (take l : nat,
      assume IH : (n + l) - (m + l) = n - m,
      calc
        (n + succ l) - (m + succ l) = succ (n + l) - (m + succ l) : {add_succ_right _ _}
          ... = succ (n + l) - succ (m + l) : {add_succ_right _ _}
          ... = (n + l) - (m + l) : sub_succ_succ _ _
          ... =  n - m : IH)

theorem sub_add_add_left (n m k : nat) : (k + n) - (k + m) = n - m
:= subst (subst (sub_add_add_right n m k) (add_comm n k)) (add_comm m k)

theorem sub_add_left (n m : nat) : n + m - m = n
:=
  induction_on m
    (subst (sub_zero_right n) (symm (add_zero_right n)))
    (take k : nat,
      assume IH : n + k - k = n,
      calc
        n + succ k - succ k = succ (n + k) - succ k : {add_succ_right n k}
          ... = n + k - k : sub_succ_succ _ _
          ... = n : IH)

theorem sub_add_left2 (n m : nat) : n + m - n = m
:= subst (sub_add_left m n) (add_comm m n)

theorem sub_sub (n m k : nat) : n - m - k = n - (m + k)
:=
  induction_on k
    (calc
      n - m - 0 = n - m : sub_zero_right _
        ... =  n - (m + 0) : {symm (add_zero_right m)})
    (take l : nat,
      assume IH : n - m - l = n - (m + l),
      calc
        n - m - succ l = pred (n - m - l) : sub_succ_right (n - m) l
          ... = pred (n - (m + l)) : {IH}
          ... = n - succ (m + l) : symm (sub_succ_right n (m + l))
          ... = n - (m + succ l) : {symm (add_succ_right m l)})

theorem succ_sub_sub (n m k : nat) : succ n - m - succ k = n - m - k
:=
  calc
    succ n - m - succ k = succ n - (m + succ k) : sub_sub _ _ _
      ... = succ n - succ (m + k) : {add_succ_right m k}
      ... = n - (m + k) : sub_succ_succ _ _
      ... = n - m - k : symm (sub_sub n m k)

theorem sub_add_right_eq_zero (n m : nat) : n - (n + m) = 0
:=
  calc
    n - (n + m) = n - n - m : symm (sub_sub n n m)
      ... = 0 - m : {sub_self n}
      ... = 0 : sub_zero_left m

theorem sub_comm (m n k : nat) : m - n - k = m - k - n
:=
  calc
    m - n - k = m - (n + k) : sub_sub m n k
      ... = m - (k + n) : {add_comm n k}
      ... = m - k - n : symm (sub_sub m k n)

theorem succ_sub_one (n : nat) : succ n - 1 = n
:= trans (sub_succ_succ n 0) (sub_zero_right n)

---------- interaction with mul

theorem mul_pred_left (n m : nat) : pred n * m = n * m - m
:=
  induction_on n
    (calc
      pred 0 * m = 0 * m : {pred_zero}
        ... = 0 : mul_zero_left _
        ... = 0 - m : symm (sub_zero_left m)
        ... = 0 * m - m : {symm (mul_zero_left m)})
    (take k : nat,
      assume IH : pred k * m = k * m - m,
      calc
        pred (succ k) * m = k * m : {pred_succ k}
          ... = k * m + m - m : symm (sub_add_left _ _)
          ... = succ k * m - m : {symm (mul_succ_left k m)})

theorem mul_pred_right (n m : nat) : n * pred m = n * m - n
:=
  calc n * pred m = pred m * n : mul_comm _ _
    ... = m * n - n : mul_pred_left m n
    ... = n * m - n : {mul_comm m n}

theorem mul_sub_distr_right (n m k : nat) : (n - m) * k = n * k - m * k
:=
  induction_on m
    (calc
      (n - 0) * k = n * k : {sub_zero_right n}
        ... = n * k - 0 : symm (sub_zero_right _)
        ... = n * k - 0 * k : {symm (mul_zero_left _)})
    (take l : nat,
      assume IH : (n - l) * k = n * k - l * k,
      calc
        (n - succ l) * k = pred (n - l) * k : {sub_succ_right n l}
          ... = (n - l) * k - k : mul_pred_left _ _
          ... = n * k - l * k - k : {IH}
          ... = n * k - (l * k + k) : sub_sub _ _ _
          ... = n * k - (succ l * k) : {symm (mul_succ_left l k)})

theorem mul_sub_distr_left (n m k : nat) : n * (m - k) = n * m - n * k
:=
  calc
    n * (m - k) = (m - k) * n : mul_comm _ _
      ... = m * n - k * n : mul_sub_distr_right _ _ _
      ... = n * m - k * n : {mul_comm _ _}
      ... = n * m - n * k : {mul_comm _ _}

---------- interaction with inequalities

theorem sub_succ_left_le {n m : nat} : n ≤ m → succ m - n  = succ (m - n)
:=
  sub_induction n m
    (take k,
      assume H : 0 ≤ k,
      calc
        succ k - 0 = succ k : sub_zero_right (succ k)
          ... = succ (k - 0) : {symm (sub_zero_right k)})
    (take k,
      assume H : succ k ≤ 0,
      absurd_elim _ H (not_succ_le_zero k))
    (take k l,
      assume IH : k ≤ l → succ l - k = succ (l - k),
      take H : succ k ≤ succ l,
      calc
        succ (succ l) - succ k = succ l - k : sub_succ_succ (succ l) k
          ... = succ (l - k) : IH (succ_le_inv H)
          ... = succ (succ l - succ k) : {symm (sub_succ_succ l k)})

theorem add_sub_right {n m : nat} : n ≤ m → n + (m - n) = m
:=
  sub_induction n m
    (take k,
      assume H : 0 ≤ k,
      calc
        0 + (k - 0) = k - 0 : add_zero_left (k - 0)
          ... = k : sub_zero_right k)
    (take k, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_le_zero k))
    (take k l,
      assume IH : k ≤ l → k + (l - k) = l,
      take H : succ k ≤ succ l,
      calc
        succ k + (succ l - succ k) = succ k + (l - k) : {sub_succ_succ l k}
          ... = succ (k + (l - k)) : add_succ_left k (l - k)
          ... = succ l : {IH (succ_le_inv H)})

theorem add_sub_left {n m : nat} (H : n ≤ m) : m - n + n = m
:= subst (add_sub_right H) (add_comm n (m - n))

theorem le_imp_sub_eq_zero {n m : nat} (H : n ≤ m) : n - m = 0
:= obtain (k : nat) (Hk : n + k = m), from le_elim H, subst (sub_add_right_eq_zero n k) Hk

theorem nat_sub_split {P : nat → Bool} {n m : nat} (H1 : n ≤ m → P 0) (H2 : ∀k, n = m + k -> P k)
    : P (n - m)
:=
  or_elim (le_total n m)
    (assume H3 : n ≤ m, subst (H1 H3) (symm (le_imp_sub_eq_zero H3)))
    (assume H3 : m ≤ n, H2 (n - m) (symm (add_sub_right H3)))

theorem sub_le_self (n m : nat) : n - m ≤ n
:=
  nat_sub_split
    (assume H : n ≤ m, le_zero n)
    (take k : nat, assume H : n = m + k, le_intro (subst (symm H) (add_comm m k)))

theorem le_imp_sub (n m : nat) (H : n ≤ m) : exists k, m - k = n
:=
  obtain (k : nat) (Hk : n + k = m), from le_elim H,
  exists_intro k
    calc
      m - k = n + k - k : {symm Hk}
        ... = n : sub_add_left n k

theorem sub_add_assoc {n m k : nat} : k ≤ m → n + m - k = n + (m - k)
:=
  sub_induction k m
    (take m : nat,
      assume H : 0 ≤ m,
      calc
        n + m - 0 = n + m : sub_zero_right (n + m)
          ... = n + (m - 0) : {symm (sub_zero_right m)})
    (take k : nat, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_le_zero k))
    (take k m,
      assume IH : k ≤ m → n + m - k = n + (m - k),
      take H : succ k ≤ succ m,
      calc
        n + succ m - succ k = succ (n + m) - succ k : {add_succ_right n m}
          ... = n + m - k : sub_succ_succ (n + m) k
          ... = n + (m - k) : IH (succ_le_inv H)
          ... = n + (succ m - succ k) : {symm (sub_succ_succ m k)})

theorem sub_eq_zero_imp_le {n m : nat} : n - m = 0 → n ≤ m
:=
  nat_sub_split
    (assume H1 : n ≤ m, assume H2 : 0 = 0, H1)
    (take k : nat,
      assume H1 : n = m + k,
      assume H2 : k = 0,
      have H3 : n = m, from subst (subst H1 H2) (add_zero_right m),
      subst (le_refl n) H3)

theorem nat_sub_sub_split {P : nat → nat → Bool} {n m : nat} (H1 : ∀k, n = m + k -> P k 0)
    (H2 : ∀k, m = n + k → P 0 k) : P (n - m) (m - n)
:=
  or_elim (le_total n m)
    (assume H3 : n ≤ m, subst (H2 (m - n) (symm (add_sub_right H3))) (symm (le_imp_sub_eq_zero H3)))
    (assume H3 : m ≤ n, subst (H1 (n - m) (symm (add_sub_right H3))) (symm (le_imp_sub_eq_zero H3)))

theorem sub_intro {n m k : ℕ} (H : n + m = k) : k - n = m
:=
  have H2 : k - n + n = m + n, from
    calc
      k - n + n = k : add_sub_left (le_intro H)
        ... = n + m : symm H
        ... = m + n : add_comm n m,
  add_left_inj H2

-------------------------------------------------- max, min, iteration, maybe: div
-- n - m + m = max n m

--absolute difference between n and m
--this section is still incomplete, it is only added to define the absolute value of an integer
definition sub_abs (n m : ℕ) := (n - m) + (m - n)

theorem sub_abs_comm (n m : ℕ) : sub_abs n m = sub_abs m n
:= add_comm (n - m) (m - n)

theorem sub_abs_le {n m : ℕ} (H : n ≤ m) : sub_abs n m = m - n
:=
  calc
    sub_abs n m = 0 + (m - n) : {le_imp_sub_eq_zero H}
      ... = m - n : add_zero_left (m - n)

theorem sub_abs_ge {n m : ℕ} (H : n ≥ m) : sub_abs n m = n - m
:= subst (sub_abs_le H) (sub_abs_comm m n)

theorem sub_abs_zero_right (n : ℕ) : sub_abs n 0 = n
:= trans (sub_abs_ge (le_zero n)) (sub_zero_right n)

theorem sub_abs_zero_left (n : ℕ) : sub_abs 0 n = n
:= trans (sub_abs_le (le_zero n)) (sub_zero_right n)

theorem sub_abs_intro {n m k : ℕ} (H : n + m = k) : sub_abs k n = m
:=
  calc
    sub_abs k n = k - n : sub_abs_ge (le_intro H)
      ... = m : sub_intro H

theorem sub_abs_add_right (n m k : ℕ) : sub_abs (n + k) (m + k) = sub_abs n m
:=
  calc
    sub_abs (n + k) (m + k) = n - m + ((m + k) - (n + k)) : {sub_add_add_right n m k}
      ... = n - m + (m - n) : {sub_add_add_right m n k}

theorem sub_abs_ge_add_right {n m : ℕ} (H : n ≥ m) : sub_abs n m + m = n
:=
  calc
    sub_abs n m + m = n - m + m : {sub_abs_ge H}
      ... = n : add_sub_left H

theorem sub_abs_add_left (n m k : ℕ) : sub_abs (k + n) (k + m) = sub_abs n m
:= subst (subst (sub_abs_add_right n m k) (add_comm n k)) (add_comm m k)

theorem sub_abs_eq {n m k l : ℕ} (H : n + m = k + l) : sub_abs n k = sub_abs l m
:=
  have special : ∀n m k l, n + m = k + l → m ≤ l → sub_abs n k = sub_abs l m,
    from
      take n m k l,
      assume H : n + m = k + l,
      assume H2 : m ≤ l,
      have H3 : k + sub_abs l m + m = n + m, from
        calc
          k + sub_abs l m + m = k + (sub_abs l m + m) : add_assoc _ _ _
            ... = k + l : {sub_abs_ge_add_right H2}
            ... = n + m : symm H,
      have H4 : k + sub_abs l m = n, from add_left_inj H3,
      sub_abs_intro H4,
  or_elim (le_total m l)
    (assume H2 : m ≤ l, special n m k l H H2)
    (assume H2 : l ≤ m,
      have H3 : sub_abs k n = sub_abs m l, from special k l n m (symm H) H2,
      trans (sub_abs_comm n k) (trans H3 (sub_abs_comm m l)))



  -- subst (subst (refl (((n + k) - (m + k)) + ((m + k) - (n + k))))
  --   (sub_add_add_right n m k)) (sub_add_add_right m n k)





end --namespace nat