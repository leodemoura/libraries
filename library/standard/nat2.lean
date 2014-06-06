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

--
-- some stuff for nat
--

add_rewrite add_zero_left add_zero_right
add_rewrite mul_zero_left mul_zero_right

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

   
--
-- div and mod
--

-- computes (succ x) divmod (succ y) from x divmod y
definition divmod_aux' (y : ℕ) (p : ℕ ## ℕ) : ℕ ## ℕ
:=
  let q := tproj1 p,    --  q = x div (succ y)
    r := tproj2 p in    --  r = x mod (succ y)
  if r < y then tpair q (succ r) else tpair (succ q) 0

-- computes x divmod (succ y)
definition divmod_aux (y : ℕ) : ℕ → ℕ ## ℕ
:= nat_rec (tpair 0 0) (fun x' p, divmod_aux' y p)

theorem divmod_aux_zero (y : ℕ) : divmod_aux y 0 = tpair 0 0
:= nat_rec_zero _ _

theorem divmod_aux_succ (y x : ℕ) : divmod_aux y (succ x) = divmod_aux' y (divmod_aux y x)
:= nat_rec_succ _ _ _

definition divmod (x : ℕ) : ℕ → ℕ ## ℕ
:= nat_rec (tpair 0 x) (fun y' h, divmod_aux y' x)

theorem divmod_zero (x : ℕ) : divmod x 0 = tpair 0 x
:= nat_rec_zero _ _

theorem divmod_succ (x y : ℕ) : divmod x (succ y) = divmod_aux y x
:= nat_rec_succ _ _ _

theorem divmod_zero_succ (y : ℕ) : divmod 0 (succ y) = tpair 0 0
:= trans (divmod_succ _ _) (divmod_aux_zero _)

theorem divmod_succ_succ (x y : ℕ) : divmod (succ x) (succ y) = divmod_aux' y (divmod x (succ y))
:=
  calc
    divmod (succ x) (succ y) = divmod_aux y (succ x) : divmod_succ _ _
    ... = divmod_aux' y (divmod_aux y x) : divmod_aux_succ _ _
    ... = divmod_aux' y (divmod x (succ y)) : {symm (divmod_succ x y)}

definition idivide x y := tproj1 (divmod x y)
definition modulo x y := tproj2 (divmod x y)

infixl 70 div : idivide    -- copied from Isabelle
infixl 70 mod : modulo

theorem div_zero (x : ℕ) : x div 0 = 0
:= trans (congr2 tproj1 (divmod_zero _)) (tproj1_tpair _ _)

theorem mod_zero (x : ℕ) : x mod 0 = x
:= trans (congr2 tproj2 (divmod_zero _)) (tproj2_tpair _ _)

theorem zero_div (y : ℕ) : 0 div y = 0
:= nat_case y (div_zero 0) (take y', trans (congr2 tproj1 (divmod_zero_succ _)) (tproj1_tpair _ _))

theorem zero_mod (y : ℕ) : 0 mod y = 0
:= nat_case y (mod_zero 0) (take y', trans (congr2 tproj2 (divmod_zero_succ _)) (tproj2_tpair _ _))

theorem div_succ_succ (x y : ℕ) : (succ x) div (succ y) =
    if (x mod (succ y) < y) then x div (succ y) else succ (x div (succ y))
:=
  let p := divmod x (succ y), q := tproj1 p, r := tproj2 p in
  calc
    (succ x) div (succ y) = tproj1 (divmod_aux' y (divmod x (succ y))) : {divmod_succ_succ x y}
      ... = if r < y then tproj1 (tpair q (succ r)) else tproj1 (tpair (succ q) 0) :
          app_if_distribute _ _ _ _
      ... = if r < y then q else succ q : by simp
      ... = if (x mod (succ y) < y) then x div (succ y) else succ (x div (succ y)) : refl _

theorem mod_succ_succ (x y : ℕ) : (succ x) mod (succ y) =
    if (x mod (succ y) < y) then succ (x mod (succ y)) else 0
:=
  let p := divmod x (succ y), q := tproj1 p, r := tproj2 p in
  calc
    (succ x) mod (succ y) = tproj2 (divmod_aux' y (divmod x (succ y))) : {divmod_succ_succ x y}
      ... = if r < y then tproj2 (tpair q (succ r)) else tproj2 (tpair (succ q) 0) :
          app_if_distribute _ _ _ _
      ... = if r < y then succ r else 0 : by simp
      ... = if (x mod (succ y) < y) then succ (x mod (succ y)) else 0 : refl _

add_rewrite div_zero mod_zero zero_div zero_mod div_succ_succ mod_succ_succ

theorem mod_lt (x y : ℕ) (H : y > 0) : x mod y < y
:=
  obtain (y' : ℕ) (H1 : y = succ y'), from positive_succ H,
  have H2 : x mod succ y' < succ y', from
    induction_on x
      (subst (lt_zero y') (symm (zero_mod (succ y'))))
      (take x',
        let t1 := x' mod succ y' in
        let t2 := if t1 < y' then succ t1 else 0 in
        assume IH : t1 < succ y',
        have H3 : succ x' mod succ y' = t2, from mod_succ_succ _ _,
        have H4 : t2 < succ y', from
          by_cases (t1 < y')
            (assume H5 : t1 < y',
              have H6 : t2 = succ t1, from imp_if_eq H5 _ _,
              have H7 : succ t1 < succ y', from succ_lt H5,
              show t2 < succ y', from subst H7 (symm H6))
            (assume H5 : ¬ t1 < y',
              have H6 : t2 = 0, from not_imp_if_eq H5 _ _,
              have H7 : 0 < succ y', from lt_zero _,
              show t2 < succ y', from subst H7 (symm H6)),
        show succ x' mod succ y' < succ y', from subst H4 (symm H3)),
  show x mod y < y, from subst H2 (symm H1)

theorem div_mod_eq (x y : ℕ) : x = (x div y) * y + x mod y
:=
  nat_case y
    (show x = x div 0 * 0 + x mod 0, from
      symm (calc
        x div 0 * 0 + x mod 0 = 0 + x mod 0 : {mul_zero_right _}
          ... = x mod 0 : add_zero_left _
          ... = x : mod_zero _))
    (take y',
      show x = (x div succ y') * succ y' + x mod succ y', from
        induction_on x
          (show 0 = (0 div succ y') * succ y' + 0 mod succ y', by simp)
          (take x',
            assume IH : x' = x' div succ y' * (succ y') + x' mod succ y',
            show succ x' = (succ x' div succ y') * succ y' + succ x' mod succ y', from
              by_cases (x' mod succ y' < y')
                (assume H1 : x' mod succ y' < y',
                  have H2 : succ x' div succ y' = x' div succ y',
                    from (trans (div_succ_succ _ _) (imp_if_eq H1 _ _)),
                  have H3 : succ x' mod succ y' = succ (x' mod (succ y')),
                    from (trans (mod_succ_succ _ _) (imp_if_eq H1 _ _)),
                  symm (calc
                    (succ x' div succ y') * succ y' + succ x' mod succ y' =
                        (x' div succ y') * succ y' + succ x' mod succ y' : {H2}
                      ... = (x' div succ y') * succ y' + succ (x' mod succ y') : {H3}
                      ... = succ (x' div succ y' * succ y' + x' mod succ y') : add_succ_right _ _
                      ... = succ x' : {symm IH}))
                (assume H1 : ¬ x' mod succ y' < y',
                  have H2 : succ x' div succ y' = succ (x' div succ y'),
                    from (trans (div_succ_succ _ _) (not_imp_if_eq H1 _ _)),
                  have H3 : succ x' mod succ y' = 0,
                    from (trans (mod_succ_succ _ _) (not_imp_if_eq H1 _ _)),
                  have H4 : x' mod succ y' = y', from
                    le_antisym
                      (show x' mod succ y' ≤ y', from lt_succ_le (mod_lt _ _ (lt_zero _)))
                      (show y' ≤ x' mod succ y', from not_lt_imp_le H1),
                  symm (calc
                    (succ x' div succ y') * succ y' + succ x' mod succ y' =
                        succ (x' div succ y') * succ y' + succ x' mod succ y' : {H2}
                      ... = succ (x' div succ y') * succ y' + 0 : {H3}
                      ... = succ (x' div succ y') * succ y' : add_zero_right _
                      ... = x' div succ y' * succ y' + succ y' : mul_succ_left _ _
                      ... = succ (x' div succ y' * succ y' + y') : add_succ_right _ _
                      ... = succ (x' div succ y' * succ y' + x' mod succ y') : {symm H4}
                      ... = succ x' : {symm IH}))))


--
-- A general recursion principle.
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
--

definition restrict {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom) 
    (m : ℕ) (x : dom)
:= if measure x < m then f x else default

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

theorem rec_measure_spec {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) 
    (rec_decreasing : ∀g m x, m ≥ measure x → 
        rec_val x g = rec_val x (restrict default measure g m)) 
    (m : ℕ) (x : dom):
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
