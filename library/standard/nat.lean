----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-- Theory nat
-- ==========
--
-- The natural numbers, with addition, multiplication, ordering, and subtraction.

-- Axioms
-- ------

import kernel macros tactic

variable nat : Type
alias ℕ : nat
unary_nat -- enables numerals

namespace nat

variable zero : nat
variable succ : nat -> nat
axiom rec {P : nat → Type} (x : P 0)  (f : ∀m : nat, P m → P (succ m)) (m : ℕ) : P m
axiom rec_zero {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) :
    rec x f 0 = x
axiom rec_succ {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) (n : ℕ) :
    rec x f (succ n) = f n  (rec x f n)

theorem induction_on {P : nat → Bool} (a : ℕ) (H1 : P 0)
    (H2 : ∀(n : ℕ) (IH : P n), P (succ n)) : P a
:= rec H1 H2 a

-- Successor and predecessor
-- -------------------------

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0
:=
  not_intro
    (take H : succ n = 0,
      have H2 : true = false, from
        (let f : nat -> Bool := (rec false (fun a b,true))
          in calc
            true = f (succ n) : symm (rec_succ _ _ _)
             ... = f 0 : {H}
	           ... = false : rec_zero _ _),
      absurd H2 true_ne_false)

definition pred (n : ℕ) := rec 0 (fun m x, m) n

theorem pred_zero : pred 0 = 0
:= rec_zero _ _
theorem pred_succ (n : ℕ) : pred (succ n) = n
:= rec_succ _ _ _

set_opaque pred true

theorem zero_or_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n)
:=
  induction_on n
    (or_intro_left _ (refl 0))
    (take m IH, or_intro_right _
      (show succ m = succ (pred (succ m)), from congr2 succ (symm (pred_succ m))))

theorem zero_or_exists_succ (n : ℕ) : n = 0 ∨ ∃k, n = succ k
:=
  or_imp_or_right (zero_or_succ_pred n)
    (assume H : n = succ (pred n), exists_intro (pred n) H)

theorem case {P : nat → Bool} (n : ℕ) (H1: P 0) (H2 : ∀m, P (succ m)) : P n
:= induction_on n H1 (take m IH, H2 m)

theorem discriminate {B : Bool} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B
:=
  or_elim (zero_or_succ_pred n)
    (take H3 : n = 0, H1 H3)
    (take H3 : n = succ (pred n), H2 (pred n) H3)

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m
:=
  calc
    n = pred (succ n) : symm (pred_succ n)
  ... = pred (succ m) : {H}
  ... = m : pred_succ m

theorem succ_ne_self (n : ℕ) : succ n ≠ n
:=
  not_intro (induction_on n
    (take H : 1 = 0,
      have ne : 1 ≠ 0, from succ_ne_zero 0,
      absurd H ne)
    (take k IH H, IH (succ_inj H)))

theorem decidable_equality (n m : ℕ) : n = m ∨ n ≠ m
:=
  have general : ∀n, n = m ∨ n ≠ m, from
    induction_on m
      (take n : nat,
        discriminate
          (assume H : n = 0, or_intro_left _ H)
          (take l : nat,
            assume H : n = succ l,
            have H2 : n ≠ 0, from subst (succ_ne_zero l) (symm H),
            or_intro_right _ H2))
      (take k : nat,
        assume IH : ∀n, n = k ∨ n ≠ k,
        take n : nat,
        discriminate
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

theorem two_step_induction_on {P : nat → Bool} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a
:=
  have stronger : P a ∧ P (succ a), from
    induction_on a
      (and_intro H1 H2)
      (take k IH,
        have IH1 : P k, from and_elim_left IH,
        have IH2 : P (succ k), from and_elim_right IH,
          and_intro IH2 (H3 k IH1 IH2)),
    and_elim_left stronger

theorem sub_induction {P : nat → nat → Bool} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m
:=
  have general : ∀m, P n m, from
  induction_on n
    (take m : nat, H1 m)
    (take k : nat,
      assume IH : ∀m, P k m,
      take m : nat,
      discriminate
        (assume Hm : m = 0,
          subst (H2 k) (symm Hm))
        (take l : nat,
          assume Hm : m = succ l,
          subst (H3 k l (IH l)) (symm Hm))),
  general m

add_rewrite succ_ne_zero

-- Addition
-- --------

definition add (n m : ℕ) := rec n (fun k x, succ x) m
infixl 65 +  : add

theorem add_zero_right (n : ℕ) : n + 0 = n
:= rec_zero _ _
theorem add_succ_right (n m : ℕ) : n + succ m = succ (n + m)
:= rec_succ _ _ _

set_opaque add true

-- ### commutativity and associativity

theorem add_zero_left (n : ℕ) : 0 + n = n
:=
  induction_on n
    (add_zero_right 0)
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add_succ_right _ _
   	    ... = succ m : {IH})

theorem add_succ_left (n m : ℕ) : (succ n) + m = succ (n + m)
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

theorem add_comm (n m : ℕ) : n + m = m + n
:=
  induction_on m
    (trans (add_zero_right _) (symm (add_zero_left _)))
    (take k IH,
      calc
        n + succ k = succ (n+k) : add_succ_right _ _
          ... = succ (k + n) : {IH}
          ... = succ k + n : symm (add_succ_left _ _))

theorem add_move_succ (n m : ℕ) : succ n + m = n + succ m
:=
  calc
    succ n + m = succ (n + m) : add_succ_left n m
      ... = n +succ m : symm (add_succ_right n m)

theorem add_comm_succ (n m : ℕ) : n + succ m = m + succ n
:=
  calc
    n + succ m = succ n + m : symm (add_move_succ n m)
      ... = m + succ n : add_comm (succ n) m

theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k)
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

theorem add_left_comm (n m k : ℕ) : n + (m + k) = m + (n + k)
:= left_comm add_comm add_assoc n m k

theorem add_right_comm (n m k : ℕ) : n + m + k = n + k + m
:= right_comm add_comm add_assoc n m k

add_rewrite add_zero_left add_zero_right
add_rewrite add_succ_left add_succ_right
add_rewrite add_comm add_assoc add_left_comm

--- the following WAS used a couple of times in int.lean
-- theorem add_switch (n m k l : ℕ) : n + m + (k + l) = n + k + (m + l)
-- := by simp

-- ### cancelation

theorem add_cancel_left {n m k : ℕ} : n + m = n + k → m = k
:=
  induction_on n
    (take H : 0 + m = 0 + k,
      calc
        m = 0 + m : symm (add_zero_left m)
          ... = 0 + k : H
          ... = k : add_zero_left k)
    (take (n : ℕ) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
      have H2 : succ (n + m) = succ (n + k),
      from calc
        succ (n + m) = succ n + m : symm (add_succ_left n m)
          ... = succ n + k : H
          ... = succ (n + k) : add_succ_left n k,
      have H3 : n + m = n + k, from succ_inj H2,
      IH H3)

theorem add_cancel_right {n m k : ℕ} (H : n + m = k + m) : n = k
:=
  have H2 : m + n = m + k,
    from calc
      m + n = n + m : add_comm m n
      ... = k + m : H
      ... = m + k : add_comm k m,
    add_cancel_left H2

theorem add_eq_zero_left {n m : ℕ} : n + m = 0 → n = 0
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

theorem add_eq_zero_right {n m : ℕ} (H : n + m = 0) : m = 0
:= add_eq_zero_left (trans (add_comm m n) H)

theorem add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0
:= and_intro (add_eq_zero_left H) (add_eq_zero_right H)

-- See also add_eq_self below.

-- ### misc

theorem add_one (n : ℕ) : n + 1 = succ n
:=
  calc
    n + 1 = succ (n + 0) : add_succ_right _ _
      ... = succ n : {add_zero_right _}

theorem add_one_left (n : ℕ) : 1 + n = succ n
:=
  calc
    1 + n = succ (0 + n) : add_succ_left _ _
      ... = succ n : {add_zero_left _}

--- rename? remove?
theorem induction_plus_one {P : nat → Bool} (a : ℕ) (H1 : P 0)
    (H2 : ∀ (n : ℕ) (IH : P n), P (n + 1)) : P a
:= rec H1 (take n IH, subst (H2 n IH) (add_one n)) a

-- Multiplication
-- --------------

definition mul (n m : ℕ) := rec 0 (fun m x, x + n) m
infixl 70 *  : mul

theorem mul_zero_right (n : ℕ) : n * 0 = 0
:= rec_zero _ _
theorem mul_succ_right (n m : ℕ) : n * succ m = n * m + n
:= rec_succ _ _ _

set_opaque mul true

-- ### commutativity, distributivity, associativity, identity

theorem mul_zero_left (n : ℕ) : 0 * n = 0
:=
  induction_on n
    (mul_zero_right 0)
    (take m IH,
      calc
        0 * succ m = 0 * m + 0 : mul_succ_right _ _
          ... = 0 * m : add_zero_right _
          ... = 0 : IH)

theorem mul_succ_left (n m : ℕ) : (succ n) * m = (n * m) + m
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
            ... = (n * k) + (n + succ k) : {add_comm_succ _ _}
            ... = (n * k) + n + succ k : symm (add_assoc _ _ _)
            ... = (n * succ k) + succ k : {symm (mul_succ_right n k)})

theorem mul_comm (n m : ℕ) : n * m = m * n
:=
  induction_on m
    (trans (mul_zero_right _) (symm (mul_zero_left _)))
    (take k IH,
      calc
        n * succ k = n * k + n : mul_succ_right _ _
          ... = k * n + n : {IH}
          ... = (succ k) * n : symm (mul_succ_left _ _))

theorem mul_distr_right (n m k : ℕ) : (n + m) * k = n * k + m * k
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
          ... = n * l + n + m * l + m : {add_right_comm _ _ _}
          ... = n * l + n + (m * l + m) : add_assoc _ _ _
          ... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
          ... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})

theorem mul_distr_left (n m k : ℕ) : n * (m + k) = n * m + n * k
:=
  calc
    n * (m + k) = (m + k) * n : mul_comm _ _
      ... = m * n + k * n : mul_distr_right _ _ _
      ... = n * m + k * n : {mul_comm _ _}
      ... = n * m + n * k : {mul_comm _ _}

theorem mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k)
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
          ... = n * (m * l + m) : symm (mul_distr_left _ _ _)
          ... = n * (m * succ l) : {symm (mul_succ_right _ _)})

theorem mul_left_comm (n m k : ℕ) : n * (m * k) = m * (n * k)
:= left_comm mul_comm mul_assoc n m k

theorem mul_right_comm (n m k : ℕ) : n * m * k = n * k * m
:= right_comm mul_comm mul_assoc n m k

theorem mul_one_right (n : ℕ) : n * 1 = n
:=
  calc
    n * 1 = n * 0 + n : mul_succ_right n 0
      ... = 0 + n : {mul_zero_right n}
      ... = n : add_zero_left n

theorem mul_one_left (n : ℕ) : 1 * n = n
:=
  calc
    1 * n = n * 1 : mul_comm _ _
      ... = n : mul_one_right n

theorem mul_eq_zero {n m : ℕ} (H : n * m = 0) : n = 0 ∨ m = 0
:=
  discriminate
    (take Hn : n = 0, or_intro_left _ Hn)
    (take (k : ℕ),
      assume (Hk : n = succ k),
      discriminate
        (take (Hm : m = 0), or_intro_right _ Hm)
        (take (l : ℕ),
          assume (Hl : m = succ l),
          have Heq : succ (k * succ l + l) = n * m, from
            symm (calc
              n * m = n * succ l : {Hl}
                ... = succ k * succ l : {Hk}
                ... = k * succ l + succ l : mul_succ_left _ _
                ... = succ (k * succ l + l) : add_succ_right _ _),
          absurd_elim _  (trans Heq H) (succ_ne_zero _)))

add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
add_rewrite mul_succ_left mul_succ_right
add_rewrite mul_comm mul_assoc mul_left_comm
add_rewrite mul_distr_right mul_distr_left

-- Less than or equal
-- ------------------

definition le (n m : ℕ) : Bool := exists k : nat, n + k = m
infix  50 <= : le
infix  50 ≤  : le

theorem le_intro {n m k : ℕ} (H : n + k = m) : n ≤ m
:= exists_intro k H

theorem le_elim {n m : ℕ} (H : n ≤ m) : ∃ k, n + k = m
:= H

set_opaque le true

-- ### partial order (totality is part of less than)

theorem le_refl (n : ℕ) : n ≤ n
:= le_intro (add_zero_right n)

theorem zero_le (n : ℕ) : 0 ≤ n
:= le_intro (add_zero_left n)

theorem le_zero {n : ℕ} (H : n ≤ 0) : n = 0
:=
  obtain (k : ℕ) (Hk : n + k = 0), from le_elim H,
  add_eq_zero_left Hk

theorem not_succ_zero_le (n : ℕ) : ¬ succ n ≤ 0
:=
  not_intro
    (assume H : succ n ≤ 0,
      have H2 : succ n = 0, from le_zero H,
      absurd H2 (succ_ne_zero n))

theorem le_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k
:=
  obtain (l1 : ℕ) (Hl1 : n + l1 = m), from le_elim H1,
  obtain (l2 : ℕ) (Hl2 : m + l2 = k), from le_elim H2,
  le_intro
    (calc
      n + (l1 + l2) =  n + l1 + l2 : symm (add_assoc n l1 l2)
        ... = m + l2 : {Hl1}
        ... = k : Hl2)

theorem le_antisym {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m
:=
  obtain (k : ℕ) (Hk : n + k = m), from (le_elim H1),
  obtain (l : ℕ) (Hl : m + l = n), from (le_elim H2),
  have L1 : k + l = 0, from
    add_cancel_left
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

-- ### interaction with addition

theorem le_add_right (n m : ℕ) : n ≤ n + m
:= le_intro (refl (n + m))

theorem le_add_left (n m : ℕ) : n ≤ m + n
:= le_intro (add_comm n m)

theorem add_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m
:=
  obtain (l : ℕ) (Hl : n + l = m), from (le_elim H),
  le_intro
    (calc
        k + n + l  = k + (n + l) : add_assoc k n l
          ... = k + m : {Hl})

theorem add_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n + k ≤ m + k
:= subst (subst (add_le_left H k) (add_comm k n)) (add_comm k m)

theorem add_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n + m ≤ k + l
:= le_trans (add_le_right H1 m) (add_le_left H2 k)

theorem add_le_cancel_left {n m k : ℕ} (H : k + n ≤ k + m) : n ≤ m
:=
  obtain (l : ℕ) (Hl : k + n + l = k + m), from (le_elim H),
  le_intro (add_cancel_left
    calc
        k + (n + l)  = k + n + l : symm (add_assoc k n l)
          ... = k + m : Hl )

theorem add_le_cancel_right {n m k : ℕ} (H : n + k ≤ m + k) : n ≤ m
:= add_le_cancel_left (subst (subst H (add_comm n k)) (add_comm m k))

theorem add_le_inv {n m k l : ℕ} (H1 : n + m ≤ k + l) (H2 : k ≤ n) : m ≤ l
:=
  obtain (a : ℕ) (Ha : k + a = n), from le_elim H2,
  have H3 : k + (a + m) ≤ k + l, from subst (subst H1 (symm Ha)) (add_assoc k a m),
  have H4 : a + m ≤ l, from add_le_cancel_left H3,
  show m ≤ l, from le_trans (le_add_left m a) H4

add_rewrite le_add_right le_add_left

-- ### interaction with successor and predecessor

theorem succ_le {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m
:= subst (subst (add_le_right H 1) (add_one n)) (add_one m)

theorem succ_le_cancel {n m : ℕ} (H : succ n ≤ succ m) :  n ≤ m
:= add_le_cancel_right (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem self_le_succ (n : ℕ) : n ≤ succ n
:= le_intro (add_one n)

theorem le_imp_le_succ {n m : ℕ} (H : n ≤ m) : n ≤ succ m
:= le_trans H (self_le_succ m)

theorem le_imp_succ_le_or_eq {n m : ℕ} (H : n ≤ m) : succ n ≤ m ∨ n = m
:=
  obtain (k : ℕ) (Hk : n + k = m), from (le_elim H),
  discriminate
    (assume H3 : k = 0,
      have Heq : n = m,
        from calc
          n = n + 0 : symm (add_zero_right n)
            ... = n + k : {symm H3}
            ... = m : Hk,
      or_intro_right _ Heq)
    (take l : nat,
      assume H3 : k = succ l,
      have Hlt : succ n ≤ m, from
        (le_intro
          (calc
            succ n + l = n + succ l : add_move_succ n l
              ... = n + k : {symm H3}
              ... = m : Hk)),
      or_intro_left _ Hlt)

theorem le_ne_imp_succ_le {n m : ℕ} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m
:= resolve_left (le_imp_succ_le_or_eq H1) H2

theorem le_succ_imp_le_or_eq {n m : ℕ} (H : n ≤ succ m) : n ≤ m ∨ n = succ m
:=
  or_imp_or (le_imp_succ_le_or_eq H)
    (take H2 : succ n ≤ succ m, show n ≤ m, from succ_le_cancel H2)
    (take H2 : n = succ m, H2)

theorem succ_le_imp_le_and_ne {n m : ℕ} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m
:=
  and_intro
    (le_trans (self_le_succ n) H)
    (not_intro
      (assume H2 : n = m,
        have H3 : succ n ≤ n, from subst H (symm H2),
        have H4 : succ n = n, from le_antisym H3 (self_le_succ n),
        show false, from absurd H4 (succ_ne_self n)))

theorem pred_le_self (n : ℕ) : pred n ≤ n
:=
  case n
    (subst (le_refl 0) (symm pred_zero))
    (take k : nat, subst (self_le_succ k) (symm (pred_succ k)))

theorem pred_le {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m
:=
  discriminate
    (take Hn : n = 0,
      have H2 : pred n = 0,
        from calc
          pred n = pred 0 : {Hn}
             ... = 0 : pred_zero,
      subst (zero_le (pred m)) (symm H2))
    (take k : nat,
      assume Hn : n = succ k,
      obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
      have H2 : pred n + l = pred m,
        from calc
          pred n + l = pred (succ k) + l : {Hn}
            ... = k + l : {pred_succ k}
            ... = pred (succ (k + l)) : symm (pred_succ (k + l))
            ... = pred (succ k + l) : {symm (add_succ_left k l)}
            ... = pred (n + l) : {symm Hn}
            ... = pred m : {Hl},
      le_intro H2)

theorem pred_le_imp_le_or_eq {n m : ℕ} (H : pred n ≤ m) : n ≤ m ∨ n = succ m
:=
  discriminate
    (take Hn : n = 0,
      or_intro_left _ (subst (zero_le m) (symm Hn)))
    (take k : nat,
      assume Hn : n = succ k,
      have H2 : pred n = k,
        from calc
          pred n = pred (succ k) : {Hn}
             ... = k : pred_succ k,
      have H3 : k ≤ m, from subst H H2,
      have H4 : succ k ≤ m ∨ k = m, from le_imp_succ_le_or_eq H3,
      show n ≤ m ∨ n = succ m, from
        or_imp_or H4
          (take H5 : succ k ≤ m, show n ≤ m, from subst H5 (symm Hn))
          (take H5 : k = m, show n = succ m, from subst Hn H5))

-- ### interaction with multiplication

theorem mul_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k * n ≤ k * m
:=
  obtain (l : ℕ) (Hl : n + l = m), from (le_elim H),
  induction_on k
    (have H2 : 0 * n = 0 * m,
      from calc
        0 * n = 0 : mul_zero_left n
          ... = 0 * m : symm (mul_zero_left m),
      show 0 * n ≤ 0 * m, from subst (le_refl (0 * n)) H2)
    (take (l : ℕ),
      assume IH : l * n ≤ l * m,
      have H2 : l * n + n ≤ l * m + m, from add_le IH H,
      have H3 : succ l * n ≤ l * m + m, from subst H2 (symm (mul_succ_left l n)),
      show succ l * n ≤ succ l * m, from subst H3 (symm (mul_succ_left l m)))

theorem mul_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n * k ≤ m * k
:= subst (subst (mul_le_left H k) (mul_comm k n)) (mul_comm k m)

theorem mul_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l
:= le_trans (mul_le_right H1 m) (mul_le_left H2 k)

--- mul_le_[left|right]_inv below

-- Less than
-- ---------

definition lt (n m : ℕ) := succ n ≤ m
infix 50 <  : lt

theorem lt_intro {n m k : ℕ} (H : succ n + k = m) : n < m
:= le_intro H

theorem lt_elim {n m : ℕ} (H : n < m) : ∃ k, succ n + k = m
:= le_elim H

theorem lt_add_succ (n m : ℕ) : n < n + succ m
:= lt_intro (add_move_succ n m)

-- ### basic facts

theorem lt_imp_ne {n m : ℕ} (H : n < m) : n ≠ m
:= and_elim_right (succ_le_imp_le_and_ne H)

theorem lt_irrefl (n : ℕ) : ¬ n < n
:= not_intro (assume H : n < n, absurd (refl n) (lt_imp_ne H))

theorem succ_pos (n : ℕ) : 0 < succ n
:= succ_le (zero_le n)

theorem not_lt_zero (n : ℕ) : ¬ n < 0
:= not_succ_zero_le n

theorem lt_imp_eq_succ {n m : ℕ} (H : n < m) : exists k, m = succ k
:=
  discriminate
    (take (Hm : m = 0), absurd_elim _ (subst H Hm) (not_lt_zero n))
    (take (l : ℕ) (Hm : m = succ l), exists_intro l Hm)

-- ### interaction with le

theorem lt_imp_le_succ {n m : ℕ} (H : n < m) : succ n ≤ m
:= H

theorem le_succ_imp_lt {n m : ℕ} (H : succ n ≤ m) : n < m
:= H

theorem self_lt_succ (n : ℕ) : n < succ n
:= le_refl (succ n)

theorem lt_imp_le {n m : ℕ} (H : n < m) : n ≤ m
:= and_elim_left (succ_le_imp_le_and_ne H)

theorem le_imp_lt_or_eq {n m : ℕ} (H : n ≤ m) : n < m ∨ n = m
:= le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {n m : ℕ} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m
:= le_ne_imp_succ_le H1 H2

theorem le_imp_lt_succ {n m : ℕ} (H : n ≤ m) : n < succ m
:= succ_le H

theorem lt_succ_imp_le {n m : ℕ} (H : n < succ m) : n ≤ m
:= succ_le_cancel H

-- ### transitivity, antisymmmetry

theorem lt_le_trans {n m k : ℕ} (H1 : n < m) (H2 : m ≤ k) : n < k
:= le_trans H1 H2

theorem le_lt_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m < k) : n < k
:= le_trans (succ_le H1) H2

theorem lt_trans {n m k : ℕ} (H1 : n < m) (H2 : m < k) : n < k
:= lt_le_trans H1 (lt_imp_le H2)

theorem le_imp_not_lt {n m : ℕ} (H : n ≤ m) : ¬ m < n
:= not_intro (take H2 : m < n, absurd (le_lt_trans H H2) (lt_irrefl n))

theorem lt_imp_not_le {n m : ℕ} (H : n < m) : ¬ m ≤ n
:= not_intro (take H2 : m ≤ n, absurd (lt_le_trans H H2) (lt_irrefl n))

theorem lt_antisym {n m : ℕ} (H : n < m) : ¬ m < n
:= le_imp_not_lt (lt_imp_le H)

-- ### interaction with addition

theorem add_lt_left {n m : ℕ} (H : n < m) (k : ℕ) : k + n < k + m
:= substp (fun x, x ≤ k + m) (add_le_left H k) (add_succ_right k n)

theorem add_lt_right {n m : ℕ} (H : n < m) (k : ℕ) : n + k < m + k
:= subst (subst (add_lt_left H k) (add_comm k n)) (add_comm k m)

theorem add_le_lt {n m k l : ℕ} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l
:= le_lt_trans (add_le_right H1 m) (add_lt_left H2 k)

theorem add_lt_le {n m k l : ℕ} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l
:= lt_le_trans (add_lt_right H1 m) (add_le_left H2 k)

theorem add_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n + m < k + l
:= add_lt_le H1 (lt_imp_le H2)

theorem add_lt_cancel_left {n m k : ℕ} (H : k + n < k + m) : n < m
:= add_le_cancel_left (subst H (symm (add_succ_right k n)))

theorem add_lt_cancel_right {n m k : ℕ} (H : n + k < m + k) : n < m
:= add_lt_cancel_left (subst (subst H (add_comm n k)) (add_comm m k))

-- ### interaction with successor (see also the interaction with le)

theorem succ_lt {n m : ℕ} (H : n < m) : succ n < succ m
:= subst (subst (add_lt_right H 1) (add_one n)) (add_one m)

theorem succ_lt_cancel {n m : ℕ} (H : succ n < succ m) :  n < m
:= add_lt_cancel_right (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem lt_imp_lt_succ {n m : ℕ} (H : n < m) : n < succ m
 := lt_trans H (self_lt_succ m)

-- ### totality of lt and le

theorem le_or_lt (n m : ℕ) : n ≤ m ∨ m < n
:=
  induction_on n
    (or_intro_left _ (zero_le m))
    (take (k : ℕ),
      assume IH : k ≤ m ∨ m < k,
      or_elim IH
        (assume H : k ≤ m,
          obtain (l : ℕ) (Hl : k + l = m), from le_elim H,
          discriminate
            (assume H2 : l = 0,
              have H3 : m = k,
                from calc
                  m = k + l : symm Hl
                    ... = k + 0 : {H2}
                    ... = k : add_zero_right k,
              have H4 : m < succ k, from subst (self_lt_succ m) H3,
              or_intro_right _ H4)
            (take l2 : nat,
              assume H2 : l = succ l2,
              have H3 : succ k + l2 = m,
                from calc
                  succ k + l2 = k + succ l2 : add_move_succ k l2
                    ... = k + l : {symm H2}
                    ... = m : Hl,
              or_intro_left _ (le_intro H3)))
        (assume H : m < k, or_intro_right _ (lt_imp_lt_succ H)))

theorem trichotomy_alt (n m : ℕ) : (n < m ∨ n = m) ∨ m < n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, le_imp_lt_or_eq H) (assume H : m < n, H)

theorem trichotomy (n m : ℕ) : n < m ∨ n = m ∨ m < n
:= iff_elim_left (or_assoc _ _ _) (trichotomy_alt n m)

theorem le_total (n m : ℕ) : n ≤ m ∨ m ≤ n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, H) (assume H : m < n, lt_imp_le H)

theorem not_lt_imp_le {n m : ℕ} (H : ¬ n < m) : m ≤ n
:= resolve_left (le_or_lt m n) H

theorem not_le_imp_lt {n m : ℕ} (H : ¬ n ≤ m) : m < n
:= resolve_right (le_or_lt n m) H

-- Note: interaction with multiplication under "positivity"

-- ### misc

theorem strong_induction_on {P : nat → Bool} (n : ℕ) (H : ∀n, (∀m, m < n → P m) → P n) : P n
:=
  have H1 : ∀n, ∀m, m < n → P m, from
    take n,
    induction_on n
      (show ∀m, m < 0 → P m, from take m H, absurd_elim _ H (not_lt_zero _))
      (take n',
        assume IH : ∀m, m < n' → P m,
        have H2: P n', from H n' IH,
        show ∀m, m < succ n' → P m, from
          take m,
          assume H3 : m < succ n',
          or_elim (le_imp_lt_or_eq (lt_succ_imp_le H3))
            (assume H4: m < n', IH _ H4)
            (assume H4: m = n', subst H2 (symm H4))),
  H1 _ _ (self_lt_succ n)

theorem case_strong_induction_on {P : nat → Bool} (a : nat) (H0 : P 0)
    (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a
:=
  strong_induction_on a (
    take n,
    show (∀m, m < n → P m) → P n, from
      case n
         (assume H : (∀m, m < 0 → P m), show P 0, from H0)
         (take n,
           assume H : (∀m, m < succ n → P m),
           show P (succ n), from
             Hind n (take m, assume H1 : m ≤ n, H _ (le_imp_lt_succ H1))))

theorem add_eq_self {n m : ℕ} (H : n + m = n) : m = 0
:=
  discriminate
    (assume Hm : m = 0, Hm)
    (take k : nat,
      assume Hm : m = succ k,
      have H2 : succ n + k = n,
        from calc
          succ n + k = n + succ k : add_move_succ n k
            ... = n + m : {symm Hm}
            ... = n : H,
      have H3 : n < n, from lt_intro H2,
      have H4 : n ≠ n, from lt_imp_ne H3,
      absurd_elim _ (refl n) H4)

-- Greater than, greater than or equal
-- -----------------------------------

definition ge (n m : ℕ) := m ≤ n
infix 50 >= : ge
infix 50 ≥  : ge

definition gt (n m : ℕ) := m < n
infix 50 >  : gt

--- prove some theorems, like ge_imp_le le_imp_ge lt_imp_gt gt_imp_lt?

-- Positivity
-- ---------
--
-- Writing "t > 0" is the preferred way to assert that a natural number is positive.

-- ### basic

-- See also succ_pos.

theorem case_zero_pos {P : ℕ → Bool} (y : ℕ) (H0 : P 0) (H1 : ∀y, y > 0 → P y) : P y
:= case y H0 (take y', H1 _ (succ_pos _))

theorem zero_or_pos (n : ℕ) : n = 0 ∨ n > 0
:= or_imp_or (or_flip (le_imp_lt_or_eq (zero_le n))) (take H : 0 = n, symm H) (take H : n > 0, H)

theorem succ_imp_pos {n m : ℕ} (H : n = succ m) : n > 0
:= subst (succ_pos m) (symm H)

theorem ne_zero_pos {n : ℕ} (H : n ≠ 0) : n > 0
:= or_elim (zero_or_pos n) (take H2 : n = 0, absurd_elim _ H2 H) (take H2 : n > 0, H2)

theorem pos_imp_eq_succ {n : ℕ} (H : n > 0) : exists l, n = succ l
:= lt_imp_eq_succ H

theorem add_pos_right (n : ℕ) {k : ℕ} (H : k > 0) : n + k > n
:=
  obtain (l : ℕ) (Hl : k = succ l), from pos_imp_eq_succ H,
  subst (lt_add_succ n l) (symm Hl)

theorem add_pos_left (n : ℕ) {k : ℕ} (H : k > 0) : k + n > n
:= subst (add_pos_right n H) (add_comm n k)

-- ### multiplication

theorem mul_pos {n m : ℕ} (Hn : n > 0) (Hm : m > 0) : n * m > 0
:=
  obtain (k : ℕ) (Hk : n = succ k), from pos_imp_eq_succ Hn,
  obtain (l : ℕ) (Hl : m = succ l), from pos_imp_eq_succ Hm,
  succ_imp_pos calc
    n * m = succ k * m : {Hk}
      ... = succ k * succ l : {Hl}
      ... = succ k * l + succ k : mul_succ_right (succ k) l
      ... = succ (succ k * l + k) : add_succ_right _ _

theorem mul_pos_imp_pos_left {n m : ℕ} (H : n * m > 0) : n > 0
:=
  discriminate
    (assume H2 : n = 0,
      have H3 : n * m = 0,
        from calc
          n * m = 0 * m : {H2}
            ... = 0 : mul_zero_left m,
      have H4 : 0 > 0, from subst H H3,
      absurd_elim _ H4 (lt_irrefl 0))
    (take l : nat,
      assume Hl : n = succ l,
      subst (succ_pos l) (symm Hl))

theorem mul_pos_imp_pos_right {n m : ℕ} (H : n * m > 0) : m > 0
:= mul_pos_imp_pos_left (subst H (mul_comm n m))

theorem mul_cancel_left {n m k : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k
:=
  have general : ∀m, n * m = n * k → m = k, from
    induction_on k
      (take m : nat,
        assume H : n * m = n * 0,
        have H2 : n * m = 0,
          from calc
            n * m = n * 0 : H
              ... = 0 : mul_zero_right n,
        have H3 : n = 0 ∨ m = 0, from mul_eq_zero H2,
        resolve_right H3 (ne_symm (lt_imp_ne Hn)))
      (take (l : ℕ),
        assume (IH : ∀ m, n * m = n * l → m = l),
        take (m : ℕ),
        assume (H : n * m = n * succ l),
        have H2 :  n * succ l > 0, from mul_pos Hn (succ_pos l),
        have H3 : m > 0, from mul_pos_imp_pos_right (subst H2 (symm H)),
        obtain (l2 : ℕ) (Hm : m = succ l2), from pos_imp_eq_succ H3,
        have H4 : n * l2 + n = n * l + n,
          from calc
            n * l2 + n = n * succ l2 : symm (mul_succ_right n l2)
              ... = n * m : {symm Hm}
              ... = n * succ l : H
              ... = n * l + n : mul_succ_right n l,
        have H5 : n * l2 = n * l, from add_cancel_right H4,
        calc
          m = succ l2 : Hm
        ... = succ l : {IH l2 H5}),
  general m H

theorem mul_cancel_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k
:= mul_cancel_left Hm (subst (subst H (mul_comm n m)) (mul_comm k m))

-- See also mul_eq_one below.

-- ### interaction of mul with le and lt

theorem mul_lt_left {n m k : ℕ} (Hk : k > 0) (H : n < m) : k * n < k * m
:=
  have H2 : k * n < k * n + k, from add_pos_right (k * n) Hk,
  have H3 : k * n + k ≤ k * m, from subst (mul_le_left H k) (mul_succ_right k n),
  lt_le_trans H2 H3

theorem mul_lt_right {n m k : ℕ} (Hk : k > 0) (H : n < m)  : n * k < m * k
:= subst (subst (mul_lt_left Hk H) (mul_comm k n)) (mul_comm k m)

theorem mul_le_lt {n m k l : ℕ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) : n * m < k * l
:= le_lt_trans (mul_le_right H1 m) (mul_lt_left Hk H2)

theorem mul_lt_le {n m k l : ℕ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) : n * m < k * l
:= le_lt_trans (mul_le_left H2 n) (mul_lt_right Hl H1)

theorem mul_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n * m < k * l
:=
  have H3 : n * m ≤ k * m, from mul_le_right (lt_imp_le H1) m,
  have H4 : k * m < k * l, from mul_lt_left (le_lt_trans (zero_le n) H1) H2,
  le_lt_trans H3 H4

theorem mul_lt_cancel_left {n m k : ℕ} (H : k * n < k * m) : n < m
:=
  have general : ∀ m, k * n < k * m → n < m, from
    induction_on n
      (take m : nat,
        assume H2 : k * 0 < k * m,
        have H3 : 0 < k * m, from subst H2 (mul_zero_right k),
        show 0 < m, from mul_pos_imp_pos_right H3)
      (take l : nat,
        assume IH : ∀ m, k * l < k * m → l < m,
        take m : nat,
        assume H2 : k * succ l < k * m,
        have H3 : 0 < k * m, from le_lt_trans (zero_le _) H2,
        have H4 : 0 < m, from mul_pos_imp_pos_right H3,
        obtain (l2 : ℕ) (Hl2 : m = succ l2), from pos_imp_eq_succ H4,
        have H5 : k * l + k < k * m, from subst H2 (mul_succ_right k l),
        have H6 : k * l + k < k * succ l2, from subst H5 Hl2,
        have H7 : k * l + k < k * l2 + k, from subst H6 (mul_succ_right k l2),
        have H8 : k * l < k * l2, from add_lt_cancel_right H7,
        have H9 : l < l2, from IH l2 H8,
        have H10 : succ l < succ l2, from succ_lt H9,
        show succ l < m, from subst H10 (symm Hl2)),
  general m H

theorem mul_lt_cancel_right {n m k : ℕ} (H : n * k < m * k) : n < m
:= mul_lt_cancel_left (subst (subst H (mul_comm n k)) (mul_comm m k))

theorem mul_le_cancel_left {n m k : ℕ} (Hk : k > 0) (H : k * n ≤ k * m) : n ≤ m
:=
  have H2 : k * n < k * m + k, from le_lt_trans H (add_pos_right _ Hk),
  have H3 : k * n < k * succ m, from subst H2 (symm (mul_succ_right k m)),
  have H4 : n < succ m, from mul_lt_cancel_left H3,
  show n ≤ m, from lt_succ_imp_le H4

theorem mul_le_cancel_right {n m k : ℕ} (Hm : m > 0) (H : n * m ≤ k * m) : n ≤ k
:= mul_le_cancel_left Hm (subst (subst H (mul_comm n m)) (mul_comm k m))

theorem mul_eq_one_left {n m : ℕ} (H : n * m = 1) : n = 1
:=
  have H2 : n * m > 0, from subst (succ_pos 0) (symm H),
  have H3 : n > 0, from mul_pos_imp_pos_left H2,
  have H4 : m > 0, from mul_pos_imp_pos_right H2,
  or_elim (le_or_lt n 1)
    (assume H5 : n ≤ 1,
      show n = 1, from le_antisym H5 H3)
    (assume H5 : n > 1,
      have H6 : n * m ≥ 2 * 1, from mul_le H5 H4,
      have H7 : 1 ≥ 2, from subst (subst H6 H) (mul_one_right 2),
      absurd_elim _ (self_lt_succ 1) (le_imp_not_lt H7))

theorem mul_eq_one_right {n m : ℕ} (H : n * m = 1) : m = 1
:= mul_eq_one_left (subst H (mul_comm n m))

--- theorem mul_eq_one {n m : ℕ} (H : n * m = 1) : n = 1 ∧ m = 1
--- := and_intro (mul_eq_one_left H) (mul_eq_one_right H)

set_opaque lt true

-- ### sub

definition sub (n m : ℕ) : nat := rec n (fun m x, pred x) m
infixl 65 - : sub

theorem sub_zero_right (n : ℕ) : n - 0 = n
:= rec_zero _ _
theorem sub_succ_right (n m : ℕ) : n - succ m = pred (n - m)
:= rec_succ _ _ _

set_opaque sub true

theorem sub_zero_left (n : ℕ) : 0 - n = 0
:=
  induction_on n (sub_zero_right 0)
    (take k : nat,
      assume IH : 0 - k = 0,
      calc
        0 - succ k = pred (0 - k) : sub_succ_right 0 k
          ... = pred 0 : {IH}
          ... = 0 : pred_zero)
--(
--theorem sub_succ_left (n m : ℕ) : pred (succ n - m) = n - m
-- :=
--   induction_on m
--     (calc
--       pred (succ n - 0) = pred (succ n) : {sub_zero_right (succ n)}
--         ... = n : pred_succ n
--         ... = n - 0 : symm (sub_zero_right n))
--     (take k : nat,
--       assume IH : pred (succ n - k) = n - k,
--       _)
--)

theorem sub_succ_succ (n m : ℕ) : succ n - succ m = n - m
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

theorem sub_self (n : ℕ) : n - n = 0
:= induction_on n (sub_zero_right 0) (take k IH, trans (sub_succ_succ k k) IH)

theorem sub_add_add_right (n m k : ℕ) : (n + k) - (m + k) = n - m
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

theorem sub_add_add_left (n m k : ℕ) : (k + n) - (k + m) = n - m
:= subst (subst (sub_add_add_right n m k) (add_comm n k)) (add_comm m k)

theorem sub_add_left (n m : ℕ) : n + m - m = n
:=
  induction_on m
    (subst (sub_zero_right n) (symm (add_zero_right n)))
    (take k : nat,
      assume IH : n + k - k = n,
      calc
        n + succ k - succ k = succ (n + k) - succ k : {add_succ_right n k}
          ... = n + k - k : sub_succ_succ _ _
          ... = n : IH)

theorem sub_add_left2 (n m : ℕ) : n + m - n = m
:= subst (sub_add_left m n) (add_comm m n)

theorem sub_sub (n m k : ℕ) : n - m - k = n - (m + k)
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

theorem succ_sub_sub (n m k : ℕ) : succ n - m - succ k = n - m - k
:=
  calc
    succ n - m - succ k = succ n - (m + succ k) : sub_sub _ _ _
      ... = succ n - succ (m + k) : {add_succ_right m k}
      ... = n - (m + k) : sub_succ_succ _ _
      ... = n - m - k : symm (sub_sub n m k)

theorem sub_add_right_eq_zero (n m : ℕ) : n - (n + m) = 0
:=
  calc
    n - (n + m) = n - n - m : symm (sub_sub n n m)
      ... = 0 - m : {sub_self n}
      ... = 0 : sub_zero_left m

theorem sub_comm (m n k : ℕ) : m - n - k = m - k - n
:=
  calc
    m - n - k = m - (n + k) : sub_sub m n k
      ... = m - (k + n) : {add_comm n k}
      ... = m - k - n : symm (sub_sub m k n)

theorem sub_one (n : ℕ) : n - 1 = pred n
:=
  calc
    n - 1 = pred (n - 0) : sub_succ_right n 0
      ... = pred n : {sub_zero_right n}

theorem succ_sub_one (n : ℕ) : succ n - 1 = n
:= trans (sub_succ_succ n 0) (sub_zero_right n)

add_rewrite sub_add_left

-- ### interaction with multiplication

theorem mul_pred_left (n m : ℕ) : pred n * m = n * m - m
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

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n
:=
  calc n * pred m = pred m * n : mul_comm _ _
    ... = m * n - n : mul_pred_left m n
    ... = n * m - n : {mul_comm m n}

theorem mul_sub_distr_right (n m k : ℕ) : (n - m) * k = n * k - m * k
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

theorem mul_sub_distr_left (n m k : ℕ) : n * (m - k) = n * m - n * k
:=
  calc
    n * (m - k) = (m - k) * n : mul_comm _ _
      ... = m * n - k * n : mul_sub_distr_right _ _ _
      ... = n * m - k * n : {mul_comm _ _}
      ... = n * m - n * k : {mul_comm _ _}

-- ### interaction with inequalities

theorem succ_sub {n m : ℕ} : n ≤ m → succ m - n  = succ (m - n)
:=
  sub_induction n m
    (take k,
      assume H : 0 ≤ k,
      calc
        succ k - 0 = succ k : sub_zero_right (succ k)
          ... = succ (k - 0) : {symm (sub_zero_right k)})
    (take k,
      assume H : succ k ≤ 0,
      absurd_elim _ H (not_succ_zero_le k))
    (take k l,
      assume IH : k ≤ l → succ l - k = succ (l - k),
      take H : succ k ≤ succ l,
      calc
        succ (succ l) - succ k = succ l - k : sub_succ_succ (succ l) k
          ... = succ (l - k) : IH (succ_le_cancel H)
          ... = succ (succ l - succ k) : {symm (sub_succ_succ l k)})

theorem le_imp_sub_eq_zero {n m : ℕ} (H : n ≤ m) : n - m = 0
:= obtain (k : ℕ) (Hk : n + k = m), from le_elim H, subst (sub_add_right_eq_zero n k) Hk

theorem add_sub_le {n m : ℕ} : n ≤ m → n + (m - n) = m
:=
  sub_induction n m
    (take k,
      assume H : 0 ≤ k,
      calc
        0 + (k - 0) = k - 0 : add_zero_left (k - 0)
          ... = k : sub_zero_right k)
    (take k, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_zero_le k))
    (take k l,
      assume IH : k ≤ l → k + (l - k) = l,
      take H : succ k ≤ succ l,
      calc
        succ k + (succ l - succ k) = succ k + (l - k) : {sub_succ_succ l k}
          ... = succ (k + (l - k)) : add_succ_left k (l - k)
          ... = succ l : {IH (succ_le_cancel H)})

theorem add_sub_ge_left {n m : ℕ} : n ≥ m → n - m + m = n
:= subst add_sub_le (add_comm m (n - m))

theorem add_sub_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n
:=
  calc
    n + (m - n) = n + 0 : {le_imp_sub_eq_zero H}
      ... = n : add_zero_right n

theorem add_sub_le_left {n m : ℕ} : n ≤ m → n - m + m = m
:= subst add_sub_ge (add_comm m (n - m))


theorem le_add_sub_left (n m : ℕ) : n ≤ n + (m - n)
:=
  or_elim (le_total n m)
    (assume H : n ≤ m, subst H (symm (add_sub_le H)))
    (assume H : m ≤ n, subst (le_refl n) (symm (add_sub_ge H)))

theorem le_add_sub_right (n m : ℕ) : m ≤ n + (m - n)
:=
  or_elim (le_total n m)
    (assume H : n ≤ m, subst (le_refl m) (symm (add_sub_le H)))
    (assume H : m ≤ n, subst H (symm (add_sub_ge H)))

-- replace "n = m + k" with "m + k = n"?
theorem sub_split {P : nat → Bool} {n m : ℕ} (H1 : n ≤ m → P 0) (H2 : ∀k, n = m + k -> P k)
    : P (n - m)
:=
  or_elim (le_total n m)
    (assume H3 : n ≤ m, subst (H1 H3) (symm (le_imp_sub_eq_zero H3)))
    (assume H3 : m ≤ n, H2 (n - m) (symm (add_sub_le H3)))

theorem sub_le_self (n m : ℕ) : n - m ≤ n
:=
  sub_split
    (assume H : n ≤ m, zero_le n)
    (take k : nat, assume H : n = m + k, le_intro (subst (symm H) (add_comm m k)))

theorem le_elim_sub (n m : ℕ) (H : n ≤ m) : exists k, m - k = n
:=
  obtain (k : ℕ) (Hk : n + k = m), from le_elim H,
  exists_intro k
    calc
      m - k = n + k - k : {symm Hk}
        ... = n : sub_add_left n k

theorem add_sub_assoc {m k : ℕ} (H : k ≤ m) (n : ℕ) : n + m - k = n + (m - k)
:=
  have lemma : k ≤ m → n + m - k = n + (m - k), from
    sub_induction k m
      (take m : nat,
        assume H : 0 ≤ m,
        calc
          n + m - 0 = n + m : sub_zero_right (n + m)
            ... = n + (m - 0) : {symm (sub_zero_right m)})
      (take k : nat, assume H : succ k ≤ 0, absurd_elim _ H (not_succ_zero_le k))
      (take k m,
        assume IH : k ≤ m → n + m - k = n + (m - k),
        take H : succ k ≤ succ m,
        calc
          n + succ m - succ k = succ (n + m) - succ k : {add_succ_right n m}
            ... = n + m - k : sub_succ_succ (n + m) k
            ... = n + (m - k) : IH (succ_le_cancel H)
            ... = n + (succ m - succ k) : {symm (sub_succ_succ m k)}),
  lemma H

theorem sub_eq_zero_imp_le {n m : ℕ} : n - m = 0 → n ≤ m
:=
  sub_split
    (assume H1 : n ≤ m, assume H2 : 0 = 0, H1)
    (take k : nat,
      assume H1 : n = m + k,
      assume H2 : k = 0,
      have H3 : n = m, from subst (subst H1 H2) (add_zero_right m),
      subst (le_refl n) H3)

theorem sub_sub_split {P : nat → nat → Bool} {n m : ℕ} (H1 : ∀k, n = m + k -> P k 0)
    (H2 : ∀k, m = n + k → P 0 k) : P (n - m) (m - n)
:=
  or_elim (le_total n m)
    (assume H3 : n ≤ m, subst (H2 (m - n) (symm (add_sub_le H3)))
      (symm (le_imp_sub_eq_zero H3)))
    (assume H3 : m ≤ n, subst (H1 (n - m) (symm (add_sub_le H3)))
      (symm (le_imp_sub_eq_zero H3)))

theorem sub_intro {n m k : ℕ} (H : n + m = k) : k - n = m
:=
  have H2 : k - n + n = m + n, from
    calc
      k - n + n = k : add_sub_ge_left (le_intro H)
        ... = n + m : symm H
        ... = m + n : add_comm n m,
  add_cancel_right H2

theorem sub_lt {x y : ℕ} (xpos : x > 0) (ypos : y > 0) : x - y < x
:=
  obtain (x' : ℕ) (xeq : x = succ x'), from pos_imp_eq_succ xpos,
  obtain (y' : ℕ) (yeq : y = succ y'), from pos_imp_eq_succ ypos,
  have xsuby_eq : x - y = x' - y', from
    calc
      x - y = succ x' - y : {xeq}
        ... = succ x' - succ y' : {yeq}
        ... = x' - y' : sub_succ_succ _ _,
  have H1 : x' - y' ≤ x', from sub_le_self _ _,
  have H2 : x' < succ x', from self_lt_succ _,
  show x - y < x, from subst (subst (le_lt_trans H1 H2) (symm xsuby_eq)) (symm xeq)

theorem sub_le_right {n m : ℕ} (H : n ≤ m) (k : nat) : n - k ≤ m - k
:=
  obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
  or_elim (le_total n k)
    (assume H2 : n ≤ k, subst (zero_le (m - k)) (symm (le_imp_sub_eq_zero H2)))
    (assume H2 : k ≤ n,
      have H3 : n - k + l = m - k, from
        calc
          n - k + l = l + (n - k) : by simp
            ... = l + n - k : symm (add_sub_assoc H2 l)
            ... = n + l - k : {add_comm l n}
            ... = m - k : {Hl},
      le_intro H3)

theorem sub_le_left {n m : ℕ} (H : n ≤ m) (k : nat) : k - m ≤ k - n
:=
  obtain (l : ℕ) (Hl : n + l = m), from le_elim H,
  sub_split
    (assume H2 : k ≤ m, zero_le (k - n))
    (take m' : ℕ,
      assume Hm : k = m + m',
      have H3 : n ≤ k, from le_trans H (le_intro (symm Hm)),
      have H4 : m' + l + n = k - n + n, from
        calc
          m' + l + n = n + l + m' : by simp_no_assump
            ... = m + m' : {Hl}
            ... = k : symm Hm
            ... = k - n + n : symm (add_sub_ge_left H3),
      le_intro (add_cancel_right H4))

-- theorem sub_lt_cancel_right {n m k : ℕ) (H : n - k < m - k) : n < m
-- :=
--   _

-- theorem sub_lt_cancel_left {n m k : ℕ) (H : n - m < n - k) : k < m
-- :=
--   _

theorem sub_triangle_inequality (n m k : ℕ) : n - k ≤ (n - m) + (m - k)
:=
  sub_split
    (assume H : n ≤ m, subst (sub_le_right H k) (symm (add_zero_left (m - k))))
    (take mn : ℕ,
      assume Hmn : n = m + mn,
      sub_split
        (assume H : m ≤ k,
          have H2 : n - k ≤ n - m, from sub_le_left H n,
          have H3 : n - k ≤ mn, from subst H2 (sub_intro (symm Hmn)),
          show n - k ≤ mn + 0, from subst H3 (symm (add_zero_right mn)))
        (take km : ℕ,
          assume Hkm : m = k + km,
          have H : k + (mn + km) = n, from
            calc
              k + (mn + km) = k + km + mn : by simp_no_assump
                ... = m + mn : {symm Hkm}
                ... = n : symm Hmn,
          have H2 : n - k = mn + km, from sub_intro H,
          subst (le_refl (n - k)) H2))


add_rewrite sub_self

-- Max, min, iteration, and absolute difference
-- --------------------------------------------

definition max (n m : ℕ) : ℕ := n + (m - n)
definition min (n m : ℕ) : ℕ := m - (m - n)

theorem max_le {n m : ℕ} (H : n ≤ m) : n + (m - n) = m := add_sub_le H

theorem max_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n := add_sub_ge H

theorem left_le_max (n m : ℕ) : n ≤ n + (m - n) := le_add_sub_left n m

theorem right_le_max (n m : ℕ) : m ≤ max n m := le_add_sub_right n m

-- ### absolute difference

-- This section is still incomplete

definition dist (n m : ℕ) := (n - m) + (m - n)

theorem dist_comm (n m : ℕ) : dist n m = dist m n
:= add_comm (n - m) (m - n)

theorem dist_self (n : ℕ) : dist n n = 0
:=
  calc
    (n - n) + (n - n) = 0 + 0 : by simp
      ... = 0 : by simp

theorem dist_eq_zero {n m : ℕ} (H : dist n m = 0) : n = m
:=
  have H2 : n - m = 0, from add_eq_zero_left H,
  have H3 : n ≤ m, from sub_eq_zero_imp_le H2,
  have H4 : m - n = 0, from add_eq_zero_right H,
  have H5 : m ≤ n, from sub_eq_zero_imp_le H4,
  le_antisym H3 H5

theorem dist_le {n m : ℕ} (H : n ≤ m) : dist n m = m - n
:=
  calc
    dist n m = 0 + (m - n) : {le_imp_sub_eq_zero H}
      ... = m - n : add_zero_left (m - n)

theorem dist_ge {n m : ℕ} (H : n ≥ m) : dist n m = n - m
:= subst (dist_le H) (dist_comm m n)

theorem dist_zero_right (n : ℕ) : dist n 0 = n
:= trans (dist_ge (zero_le n)) (sub_zero_right n)

theorem dist_zero_left (n : ℕ) : dist 0 n = n
:= trans (dist_le (zero_le n)) (sub_zero_right n)

theorem dist_intro {n m k : ℕ} (H : n + m = k) : dist k n = m
:=
  calc
    dist k n = k - n : dist_ge (le_intro H)
      ... = m : sub_intro H

theorem dist_add_right (n m k : ℕ) : dist (n + k) (m + k) = dist n m
:=
  calc
    dist (n + k) (m + k) = n - m + ((m + k) - (n + k)) : {sub_add_add_right n m k}
      ... = n - m + (m - n) : {sub_add_add_right m n k}

theorem dist_add_left (n m k : ℕ) : dist (k + n) (k + m) = dist n m
:= subst (subst (dist_add_right n m k) (add_comm n k)) (add_comm m k)

add_rewrite dist_add_right dist_add_left

theorem dist_ge_add_right {n m : ℕ} (H : n ≥ m) : dist n m + m = n
:=
  calc
    dist n m + m = n - m + m : {dist_ge H}
      ... = n : add_sub_ge_left H

theorem dist_eq {n m k l : ℕ} (H : n + m = k + l) : dist n k = dist l m
:=
  calc
    dist n k = dist (n + m) (k + m) : symm (dist_add_right n k m)
      ... = dist (k + l) (k + m) : {H}
      ... = dist l m : dist_add_left l m k

--triangle inequality formulated with dist
theorem triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k
:=
  have H : (n - m) + (m - k) + ((k - m) + (m - n)) = (n - m) + (m - n) + ((m - k) + (k - m)),
    by simp,
  subst (add_le (sub_triangle_inequality n m k) (sub_triangle_inequality k m n)) H

theorem dist_add_le_add_dist (n m k l : ℕ) : dist (n + m) (k + l) ≤ dist n k + dist m l
:=
  have H : dist (n + m) (k + m) + dist (k + m) (k + l) = dist n k + dist m l, from
    calc
      _ = dist n k + dist (k + m) (k + l) : {dist_add_right n k m}
    ... = _ : {dist_add_left m l k},
  subst (triangle_inequality (n + m) (k + m) (k + l)) H

set_opaque dist true

--- subst (subst (refl (((n + k) - (m + k)) + ((m + k) - (n + k))))
---   (sub_add_add_right n m k)) (sub_add_add_right m n k)
---
end --namespace nat