----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Jeremy Avigad. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad
--
-- This will ultimately be merged with nat.lean.
--
----------------------------------------------------------------------------------------------------

import kernel
import macros
import nat
import find
import tactic

using nat
unary_nat

namespace nat


-- some stuff for nat
-- ==================

-- suggestions:
--
-- zero_lt ~~> succ_lt_zero
-- le_zero ~~> zero_le
-- add_left_inj ~~> add_left_cancel etc.

add_rewrite succ_ne_zero
add_rewrite add_zero_left add_zero_right
add_rewrite add_succ_left add_succ_right
add_rewrite add_comm add_assoc add_comm_left
add_rewrite le_add_right le_add_left

add_rewrite mul_zero_left mul_zero_right
add_rewrite mul_succ_left mul_succ_right
add_rewrite mul_comm mul_assoc mul_comm_left

check mul_assoc
check mul_comm_right
check mul_comm_left

add_rewrite sub_add_left

theorem add_simp_test (x y z w : ℕ) : (x + w) + (z + y) = z + (y + x) + w
:= by simp

theorem add_simp_test2 (x y z w : ℕ) : z * y + x * w = w * x + y * z
:= by simp

theorem complete_induction_on {P : nat → Bool} (a : nat)
    (H : ∀(n : nat), (∀m, m < n → P m) → P n) : P a
:=
  have H1 : ∀n, ∀m, m < n → P m, from
    take n,
    induction_on n
      (show ∀m, m < 0 → P m, from take m H, absurd_elim _ H (lt_zero_inv _))
      (take n',
        assume IH : ∀m, m < n' → P m,
        have H2: P n', from H n' IH,
        show ∀m, m < succ n' → P m, from
          take m,
          assume H3 : m < succ n',
          or_elim (le_lt_or (lt_succ_le H3))
            (assume H4: m < n', IH _ H4)
            (assume H4: m = n', subst H2 (symm H4))),
  H1 _ _ (self_lt_succ a)

theorem complete_induction'_on {P : nat → Bool} (a : nat) (H0 : P 0)
    (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a
:=
  complete_induction_on a (
    take n,
    show (∀m, m < n → P m) → P n, from
      nat_case n
         (assume H : (∀m, m < 0 → P m), show P 0, from H0)
         (take n,
           assume H : (∀m, m < succ n → P m),
           show P (succ n), from
             Hind n (take m, assume H1 : m ≤ n, H _ (le_lt_succ H1))))

theorem nat_case' {P : ℕ → Bool} (y : ℕ) (H0 : P 0) (H1 : ∀y, y > 0 → P y) : P y
:= nat_case y H0 (take y', H1 _ (lt_zero _))

theorem sub_lt {x y : ℕ} (xpos : x > 0) (ypos : y > 0) : x - y < x
:=
  obtain (x' : ℕ) (xeq : x = succ x'), from positive_succ xpos,
  obtain (y' : ℕ) (yeq : y = succ y'), from positive_succ ypos,
  have xsuby_eq : x - y = x' - y', from
    calc
      x - y = succ x' - y : {xeq}
        ... = succ x' - succ y' : {yeq}
        ... = x' - y' : sub_succ_succ _ _,
  have H1 : x' - y' ≤ x', from sub_le_self _ _,
  have H2 : x' < succ x', from self_lt_succ _,
  show x - y < x, from subst (subst (le_lt_trans H1 H2) (symm xsuby_eq)) (symm xeq)


-- A general recursion principle
-- =============================
--
-- Data:
--
--   dom, codom : Type
--   default : codom
--   measure : dom → ℕ
--   rec_val : dom → (dom → codom) → codom
--
-- and a proof
--
--   rec_decreasing : ∀m, m ≥ measure x, rec_val x f = rec_val x (restrict f m)
--
-- ... which says that the recursive call only depends on f at values with measure less than x,
-- in the sense that changing other values to the default value doesn't change the result.
--
-- The result is a function f = rec_measure, satisfying
--
--   f x = rec_val x f

definition restrict {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom)
:= if measure x < m then f x else default

theorem restrict_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom) (H : measure x < m) :
  restrict default measure f m x = f x
:= imp_if_eq H _ _

theorem restrict_not_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (f : dom → codom) (m : ℕ) (x : dom) (H : ¬ measure x < m) :
  restrict default measure f m x = default
:= not_imp_if_eq H _ _

definition rec_measure_aux {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) : ℕ → dom → codom
:= nat_rec (λx, default) (λm g x, if measure x < succ m then rec_val x g else default)

definition rec_measure {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) (x : dom) : codom
:= rec_measure_aux default measure rec_val (succ (measure x)) x

theorem rec_measure_aux_spec {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom)
    (rec_decreasing : ∀g m x, m ≥ measure x →
        rec_val x g = rec_val x (restrict default measure g m))
    (m : ℕ) :
  let f' := rec_measure_aux default measure rec_val in
  let f := rec_measure default measure rec_val in
  f' m = restrict default measure f m
:=
  let f' := rec_measure_aux default measure rec_val in
  let f := rec_measure default measure rec_val in
  complete_induction'_on m
    (have H1 : f' 0 = (λx, default), from nat_rec_zero _ _,
      have H2 : restrict default measure f 0 = (λx, default), from
        funext
          (take x,
            have H3: ¬ measure x < 0, from lt_zero_inv _,
            show restrict default measure f 0 x = default, from not_imp_if_eq H3 _ _),
      show f' 0 = restrict default measure f 0, from trans H1 (symm H2))
    (take m,
      assume IH: ∀n, n ≤ m → f' n = restrict default measure f n,
      funext
        (take x : dom,
          show f' (succ m) x = restrict default measure f (succ m) x, from
            by_cases (measure x < succ m)
              (assume H1 : measure x < succ m,
                have H2 : f' (succ m) x = rec_val x f, from
                  calc
                    f' (succ m) x = if measure x < succ m then rec_val x (f' m) else default :
                        congr1 (nat_rec_succ _ _ _) x
                      ... = rec_val x (f' m) : imp_if_eq H1 _ _
                      ... = rec_val x (restrict default measure f m) : {IH m (le_refl m)}
                      ... = rec_val x f : symm (rec_decreasing _ _ _ (lt_succ_le H1)),
                have H3 : restrict default measure f (succ m) x = rec_val x f, from
                  let m' := measure x in
                  calc
                    restrict default measure f (succ m) x = f x : imp_if_eq H1 _ _
                      ... = f' (succ m') x : refl _
                      ... = if measure x < succ m' then rec_val x (f' m') else default :
                          congr1 (nat_rec_succ _ _ _) x
                      ... = rec_val x (f' m') : imp_if_eq (self_lt_succ _) _ _
                      ... = rec_val x (restrict default measure f m') : {IH m' (lt_succ_le H1)}
                      ... = rec_val x f : symm (rec_decreasing _ _ _ (le_refl _)),
                show f' (succ m) x = restrict default measure f (succ m) x,
                  from trans H2 (symm H3))
              (assume H1 : ¬ measure x < succ m,
                have H2 : f' (succ m) x = default, from
                  calc
                    f' (succ m) x = if measure x < succ m then rec_val x (f' m) else default :
                        congr1 (nat_rec_succ _ _ _) x
                      ... = default : not_imp_if_eq H1 _ _,
                have H3 : restrict default measure f (succ m) x = default,
                  from not_imp_if_eq H1 _ _,
                show f' (succ m) x = restrict default measure f (succ m) x,
                  from trans H2 (symm H3))))

theorem rec_measure_spec {dom codom : Type} {default : codom} {measure : dom → ℕ}
    (rec_val : dom → (dom → codom) → codom)
    (rec_decreasing : ∀g m x, m ≥ measure x →
      rec_val x g = rec_val x (restrict default measure g m))
    (x : dom):
  let f := rec_measure default measure rec_val in
  f x = rec_val x f
:=
  let f' := rec_measure_aux default measure rec_val in
  let f := rec_measure default measure rec_val in
  let m := measure x in
  calc
    f x = f' (succ m) x : refl _
      ... = if measure x < succ m then rec_val x (f' m) else default :
                          congr1 (nat_rec_succ _ _ _) x
      ... = rec_val x (f' m) : imp_if_eq (self_lt_succ _) _ _
      ... = rec_val x (restrict default measure f m) : {rec_measure_aux_spec _ _ _ rec_decreasing _}
      ... = rec_val x f : symm (rec_decreasing _ _ _ (le_refl _))


-- div and mod
-- ===========

-- the definition of div
-- ---------------------

-- for fixed y, recursive call for x div y
definition div_aux_rec (y : ℕ) (x : ℕ) (div_aux' : ℕ → ℕ) : ℕ
:= if (y = 0 ∨ x < y) then 0 else succ (div_aux' (x - y))

definition div_aux (y : ℕ) : ℕ → ℕ := rec_measure 0 (fun x, x) (div_aux_rec y)

theorem div_aux_decreasing (y : ℕ) (g : ℕ → ℕ) (m : ℕ) (x : ℕ) (H : m ≥ x) :
    div_aux_rec y x g = div_aux_rec y x (restrict 0 (fun x, x) g m)
:=
  let lhs := div_aux_rec y x g in
  let rhs := div_aux_rec y x (restrict 0 (fun x, x) g m) in
  show lhs = rhs, from
    by_cases (y = 0 ∨ x < y)
      (assume H1 : y = 0 ∨ x < y,
        calc
          lhs = 0 : imp_if_eq H1 _ _
            ... = rhs : symm (imp_if_eq H1 _ _))
      (assume H1 : ¬ (y = 0 ∨ x < y),
        have H2 : y ≠ 0 ∧ ¬ x < y, from not_or _ _ ◂ H1,
        have ypos : y > 0, from ne_zero_positive (and_elim_left H2),
        have xgey : x ≥ y, from not_lt_imp_le (and_elim_right H2),
        have H4 : x - y < x, from sub_lt (lt_le_trans ypos xgey) ypos,
        have H5 : x - y < m, from lt_le_trans H4 H,
        symm (calc
          rhs = succ (restrict 0 (fun x, x) g m (x - y)) : not_imp_if_eq H1 _ _
            ... = succ (g (x - y)) : {restrict_lt_eq _ _ _ _ _ H5}
            ... = lhs : symm (not_imp_if_eq H1 _ _)))

theorem div_aux_spec (y : ℕ) (x : ℕ) :
    div_aux y x = if (y = 0 ∨ x < y) then 0 else succ (div_aux y (x - y))
:= rec_measure_spec (div_aux_rec y) (div_aux_decreasing y) x

definition idivide (x : ℕ) (y : ℕ) : ℕ := div_aux y x

infixl 70 div : idivide    -- copied from Isabelle

theorem div_zero (x : ℕ) : x div 0 = 0
:= trans (div_aux_spec _ _) (imp_if_eq (or_intro_left _ (refl _)) _ _)

theorem div_less {x y : ℕ} (H : x < y) : x div y = 0
:= trans (div_aux_spec _ _) (imp_if_eq (or_intro_right _ H) _ _)

theorem zero_div (y : ℕ) : 0 div y = 0
:= nat_case y (div_zero 0) (take y', div_less (lt_zero _))

theorem div_rec {x y : ℕ} (H1 : y > 0) (H2 : x ≥ y) : x div y = succ ((x - y) div y)
:=
  have H3 : ¬ (y = 0 ∨ x < y), from
    not_intro
      (assume H4 : y = 0 ∨ x < y,
        or_elim H4
          (assume H5 : y = 0, not_elim (lt_irrefl _) (subst H1 H5))
          (assume H5 : x < y, not_elim (lt_le_antisym H5) H2)),
  trans (div_aux_spec _ _) (not_imp_if_eq H3 _ _)

add_rewrite div_zero div_less zero_div

theorem div_add_self (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) div z = succ (x div z)
:=
  have H1 : z ≤ x + z, by simp,
  let H2 := div_rec H H1 in
  by simp

theorem div_add_mul_self (x y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) div z = x div z + y
:=
  induction_on y (by simp)
    (take y,
      assume IH : (x + y * z) div z = x div z + y,
      calc
        (x + succ y * z) div z = (x + y * z + z) div z : by simp
          ... = succ ((x + y * z) div z) : div_add_self _ H
          ... = x div z + succ y : by simp)


-- the definition of mod
-- ---------------------

-- for fixed y, recursive call for x mod y
definition mod_aux_rec (y : ℕ) (x : ℕ) (mod_aux' : ℕ → ℕ) : ℕ
:= if (y = 0 ∨ x < y) then x else mod_aux' (x - y)

definition mod_aux (y : ℕ) : ℕ → ℕ := rec_measure 0 (fun x, x) (mod_aux_rec y)

theorem mod_aux_decreasing (y : ℕ) (g : ℕ → ℕ) (m : ℕ) (x : ℕ) (H : m ≥ x) :
    mod_aux_rec y x g = mod_aux_rec y x (restrict 0 (fun x, x) g m)
:=
  let lhs := mod_aux_rec y x g in
  let rhs := mod_aux_rec y x (restrict 0 (fun x, x) g m) in
  show lhs = rhs, from
    by_cases (y = 0 ∨ x < y)
      (assume H1 : y = 0 ∨ x < y,
        calc
          lhs = x : imp_if_eq H1 _ _
            ... = rhs : symm (imp_if_eq H1 _ _))
      (assume H1 : ¬ (y = 0 ∨ x < y),
        have H2 : y ≠ 0 ∧ ¬ x < y, from not_or _ _ ◂ H1,
        have ypos : y > 0, from ne_zero_positive (and_elim_left H2),
        have xgey : x ≥ y, from not_lt_imp_le (and_elim_right H2),
        have H4 : x - y < x, from sub_lt (lt_le_trans ypos xgey) ypos,
        have H5 : x - y < m, from lt_le_trans H4 H,
        symm (calc
          rhs = restrict 0 (fun x, x) g m (x - y) : not_imp_if_eq H1 _ _
            ... = g (x - y) : restrict_lt_eq _ _ _ _ _ H5
            ... = lhs : symm (not_imp_if_eq H1 _ _)))

theorem mod_aux_spec (y : ℕ) (x : ℕ) :
    mod_aux y x = if (y = 0 ∨ x < y) then x else mod_aux y (x - y)
:= rec_measure_spec (mod_aux_rec y) (mod_aux_decreasing y) x

definition modulo (x : ℕ) (y : ℕ) : ℕ := mod_aux y x

infixl 70 mod : modulo

theorem mod_zero (x : ℕ) : x mod 0 = x
:= trans (mod_aux_spec _ _) (imp_if_eq (or_intro_left _ (refl _)) _ _)

theorem mod_less {x y : ℕ} (H : x < y) : x mod y = x
:= trans (mod_aux_spec _ _) (imp_if_eq (or_intro_right _ H) _ _)

theorem zero_mod (y : ℕ) : 0 mod y = 0
:= nat_case y (mod_zero 0) (take y', mod_less (lt_zero _))

theorem mod_rec {x y : ℕ} (H1 : y > 0) (H2 : x ≥ y) : x mod y = (x - y) mod y
:=
  have H3 : ¬ (y = 0 ∨ x < y), from
    not_intro
      (assume H4 : y = 0 ∨ x < y,
        or_elim H4
          (assume H5 : y = 0, not_elim (lt_irrefl _) (subst H1 H5))
          (assume H5 : x < y, not_elim (lt_le_antisym H5) H2)),
  trans (mod_aux_spec _ _) (not_imp_if_eq H3 _ _)

theorem mod_add_self (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) mod z = x mod z
:=
  have H1 : z ≤ x + z, by simp,
  let H2 := mod_rec H H1 in
  by simp

theorem mod_add_mul_self (x y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) mod z = x mod z
:=
  induction_on y (by simp)
    (take y,
      assume IH : (x + y * z) mod z = x mod z,
      calc
        (x + succ y * z) mod z = (x + y * z + z) mod z : by simp
          ... = (x + y * z) mod z : mod_add_self _ H
          ... = x mod z : IH)

add_rewrite mod_zero mod_less zero_mod

-- properties of div and mod together
-- ----------------------------------

theorem mod_lt (x : ℕ) {y : ℕ} (H : y > 0) : x mod y < y
:=
  complete_induction'_on x
    (show 0 mod y < y, from subst H (symm (zero_mod _)))
    (take x,
      assume IH : ∀x', x' ≤ x → x' mod y < y,
      show succ x mod y < y, from
        by_cases (succ x < y)
          (assume H1 : succ x < y,
            have H2 : succ x mod y = succ x, from mod_less H1,
            show succ x mod y < y, from subst H1 (symm H2))
          (assume H1 : ¬ succ x < y,
            have H2 : y ≤ succ x, from not_lt_imp_le H1,
            have H3 : succ x mod y = (succ x - y) mod y, from mod_rec H H2,
            have H4 : succ x - y < succ x, from sub_lt (lt_zero _) H,
            have H5 : succ x - y ≤ x, from lt_succ_le H4,
            show succ x mod y < y, from subst (IH _ H5) (symm H3)))

theorem div_mod_eq (x y : ℕ) : x = x div y * y + x mod y
:=
  nat_case' y
    (show x = x div 0 * 0 + x mod 0, from
      symm (calc
        x div 0 * 0 + x mod 0 = 0 + x mod 0 : {mul_zero_right _}
          ... = x mod 0 : add_zero_left _
          ... = x : mod_zero _))
    (take y,
      assume H : y > 0,
      show x = x div y * y + x mod y, from
        complete_induction'_on x
          (show 0 = (0 div y) * y + 0 mod y, by simp)
          (take x,
            assume IH : ∀x', x' ≤ x → x' = x' div y * y + x' mod y,
            show succ x = succ x div y * y + succ x mod y, from
              by_cases (succ x < y)
                (assume H1 : succ x < y,
                  have H2 : succ x div y = 0, from div_less H1,
                  have H3 : succ x mod y = succ x, from mod_less H1,
                  by simp)
                (assume H1 : ¬ succ x < y,
                  have H2 : y ≤ succ x, from not_lt_imp_le H1,
                  have H3 : succ x div y = succ ((succ x - y) div y), from div_rec H H2,
                  have H4 : succ x mod y = (succ x - y) mod y, from mod_rec H H2,
                  have H5 : succ x - y < succ x, from sub_lt (lt_zero _) H,
                  have H6 : succ x - y ≤ x, from lt_succ_le H5,
                  symm (calc
                    succ x div y * y + succ x mod y = succ ((succ x - y) div y) * y + succ x mod y :
                        {H3}
                      ... = ((succ x - y) div y) * y + y + succ x mod y : {mul_succ_left _ _}
                      ... = ((succ x - y) div y) * y + y + (succ x - y) mod y : {H4}
                      ... = ((succ x - y) div y) * y + (succ x - y) mod y + y : add_comm_right _ _ _
                      ... = succ x - y + y : {symm (IH _ H6)}
                      ... = succ x : add_sub_left H2))))

theorem mod_le (x y : ℕ) : x mod y ≤ x
:= subst (le_add_left (x mod y) _) (symm (div_mod_eq _ _))

axiom sorry {P : Bool} : P

-- a good example where simplifying using the context causes problems
theorem remainder_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
    (H3 : q1 * y + r1 = q2 * y + r2) : r1 = r2
:=
  calc
    r1 = r1 mod y : by simp
      ... = (r1 + q1 * y) mod y : symm (mod_add_mul_self _ _ H)
      ... = (q1 * y + r1) mod y : {add_comm _ _}
      ... = (r2 + q2 * y) mod y : by simp
      ... = r2 mod y : mod_add_mul_self _ _ H
      ... = r2 : by simp

theorem quotient_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
    (H3 : q1 * y + r1 = q2 * y + r2) : q1 = q2
:=
  have H4 : q1 * y + r2 = q2 * y + r2, from subst H3 (remainder_unique H H1 H2 H3),
  have H5 : q1 * y = q2 * y, from add_left_inj H4,
  have H6 : y > 0, from le_lt_trans (le_zero _) H1,
  show q1 = q2, from mul_right_inj H6 H5

theorem div_mul_mul {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) div (z * y) = x div y
:=
  by_cases (y = 0)
    (assume H : y = 0, by simp)
    (assume H : y ≠ 0,
      have ypos : y > 0, from ne_zero_positive H,
      have zypos : z * y > 0, from mul_positive zpos ypos,
      have H1 : (z * x) mod (z * y) < z * y, from mod_lt _ zypos,
      have H2 : z * (x mod y) < z * y, from mul_lt_left zpos (mod_lt _ ypos),
      quotient_unique zypos H1 H2
        (calc
          ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : symm (div_mod_eq _ _)
            ... = z * (x div y * y + x mod y) : {div_mod_eq _ _}
            ... = z * (x div y * y) + z * (x mod y) : mul_add_distr_left _ _ _
            ... = (x div y) * (z * y) + z * (x mod y) : {mul_comm_left _ _ _}))
-- something wrong with the term order
--            ... = (x div y) * (z * y) + z * (x mod y) : by simp))

theorem mod_mul_mul {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) mod (z * y) = z * (x mod y)
:=
  by_cases (y = 0)
    (assume H : y = 0, by simp)
    (assume H : y ≠ 0,
      have ypos : y > 0, from ne_zero_positive H,
      have zypos : z * y > 0, from mul_positive zpos ypos,
      have H1 : (z * x) mod (z * y) < z * y, from mod_lt _ zypos,
      have H2 : z * (x mod y) < z * y, from mul_lt_left zpos (mod_lt _ ypos),
      remainder_unique zypos H1 H2
        (calc
          ((z * x) div (z * y)) * (z * y) + (z * x) mod (z * y) = z * x : symm (div_mod_eq _ _)
            ... = z * (x div y * y + x mod y) : {div_mod_eq _ _}
            ... = z * (x div y * y) + z * (x mod y) : mul_add_distr_left _ _ _
            ... = (x div y) * (z * y) + z * (x mod y) : {mul_comm_left _ _ _}))

theorem mod_1 (x : ℕ) : x mod 1 = 0
:=
  have H1 : x mod 1 < 1, from mod_lt _ (lt_zero 0),
  le_zero_inv (lt_succ_le H1)

add_rewrite mod_1

theorem div_1 (x : ℕ) : x div 1 = x
:=
  symm(calc
    x = x div 1 * 1 + x mod 1 : div_mod_eq _ _
     ... = x div 1 : by simp)

-- divides
-- =======

definition dvd (x y : ℕ) : Bool := y mod x = 0

infix 50 | : dvd

theorem dvd_iff_mod_eq_zero (x y : ℕ) : y | x ↔ x mod y = 0
:= refl _

theorem dvd_imp_div_mul_eq {x y : ℕ} (H : y | x) : x div y * y = x
:=
  symm (calc
    x = x div y * y + x mod y : div_mod_eq _ _
      ... = x div y * y + 0 : {(dvd_iff_mod_eq_zero _ _) ◂ H}
      ... = x div y * y : add_zero_right _)

theorem mul_eq_imp_dvd {z x y : ℕ} (H : z * y = x) :  y | x
:=
  have H1 : z * y = x mod y + x div y * y, from trans (trans H (div_mod_eq x y)) (add_comm _ _),
  have H2 : (z - x div y) * y = x mod y, from
    calc
      (z - x div y) * y = z * y - x div y * y : mul_sub_distr_right _ _ _
         ... = x mod y + x div y * y - x div y * y : {H1}
         ... = x mod y : sub_add_left _ _,
  show x mod y = 0, from
    by_cases (y = 0)
      (assume yz : y = 0,
        have xz : x = 0, from
          calc
            x = z * y : symm H
              ... = z * 0 : {yz}
              ... = 0 : mul_zero_right _,
        calc
          x mod y = x mod 0 : {yz}
            ... = x : mod_zero _
            ... = 0 : xz)
      (assume ynz : y ≠ 0,
        have ypos : y > 0, from ne_zero_positive ynz,
        have H3 : (z - x div y) * y < y, from subst (mod_lt x ypos) (symm H2),
        have H4 : (z - x div y) * y < 1 * y, from subst H3 (symm (mul_one_left y)),
        have H5 : z - x div y < 1, from mul_lt_right_inv H4,
        have H6 : z - x div y = 0, from le_zero_inv (lt_succ_le H5),
        calc
          x mod y = (z - x div y) * y : symm H2
            ... = 0 * y : {H6}
            ... = 0 : mul_zero_left _)

theorem dvd_iff_exists_mul (x y : ℕ) : x | y ↔ ∃z, z * x = y
:=
  iff_intro
    (assume H : x | y,
      show ∃z, z * x = y, from exists_intro _ (dvd_imp_div_mul_eq H))
    (assume H : ∃z, z * x = y,
      obtain (z : ℕ) (zx_eq : z * x = y), from H,
      show x | y, from mul_eq_imp_dvd zx_eq)


-- gcd and lcm
-- ===========

-- definition of gcd
-- -----------------

definition gcd_aux_measure (p : ℕ ## ℕ) : ℕ
:= tproj2 p

definition gcd_aux_rec (p : ℕ ## ℕ) (gcd_aux' : ℕ ## ℕ → ℕ) : ℕ
:=
  let x := tproj1 p, y := tproj2 p in
  if y = 0 then x else gcd_aux' (tpair y (x mod y))

definition gcd_aux : ℕ ## ℕ → ℕ := rec_measure 0 gcd_aux_measure gcd_aux_rec

theorem gcd_aux_decreasing (g : ℕ ## ℕ → ℕ) (m : ℕ) (p : ℕ ## ℕ) (H : m ≥ gcd_aux_measure p) :
    gcd_aux_rec p g = gcd_aux_rec p (restrict 0 gcd_aux_measure g m)
:=
  let x := tproj1 p, y := tproj2 p in
  let p' := tpair y (x mod y) in
  let lhs := gcd_aux_rec p g in
  let rhs := gcd_aux_rec p (restrict 0 gcd_aux_measure g m) in
  show lhs = rhs, from
    by_cases (y = 0)
      (assume H1 : y = 0,
        calc
          lhs = x : imp_if_eq H1 _ _
            ... = rhs : symm (imp_if_eq H1 _ _))
      (assume H1 : y ≠ 0,
        have ypos : y > 0, from ne_zero_positive H1,
        have H2 : gcd_aux_measure p' = x mod y, from tproj2_tpair _ _,
        have H3 : gcd_aux_measure p' < gcd_aux_measure p, from subst (mod_lt _ ypos) (symm H2),
        have H4: gcd_aux_measure p' < m, from lt_le_trans H3 H,
        symm (calc
          rhs = restrict 0 gcd_aux_measure g m p' : not_imp_if_eq H1 _ _
            ... = g p' : restrict_lt_eq _ _ _ _ _ H4
            ... = lhs : symm (not_imp_if_eq H1 _ _)))

theorem gcd_aux_spec (p : ℕ ## ℕ) : gcd_aux p =
  let x := tproj1 p, y := tproj2 p in
  if y = 0 then x else gcd_aux (tpair y (x mod y))
:= rec_measure_spec gcd_aux_rec gcd_aux_decreasing p

definition gcd (x y : ℕ) : ℕ := gcd_aux (tpair x y)

theorem gcd_def (x y : ℕ) : gcd x y = if y = 0 then x else gcd y (x mod y)
:=
  let x' := tproj1 (tpair x y), y' := tproj2 (tpair x y) in
  calc
    gcd x y = if y' = 0 then x' else gcd_aux (tpair y' (x' mod y'))
        : gcd_aux_spec (tpair x y)
      ... = if y = 0 then x' else gcd_aux (tpair y (x' mod y)) : {tproj2_tpair x y}
      ... = if y = 0 then x else gcd_aux (tpair y (x mod y)) : {tproj1_tpair x y}
      ... = if y = 0 then x else gcd y (x mod y) : refl _

theorem gcd_zero (x : ℕ) : gcd x 0 = x
:= trans (gcd_def x 0) (imp_if_eq (refl _) _ _)

add_rewrite gcd_zero

theorem gcd_zero_left (x : ℕ) : gcd 0 x = x
:= nat_case x (by simp) (take x, trans (gcd_def _ _) (by simp))
