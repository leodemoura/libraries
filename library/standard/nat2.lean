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
-- temporary definition of the product of two types
--

definition tprod (A B : Type) := A ⨯ B
definition tpair {A B : Type} (a : A) (b : B) : tprod A B := pair a b
definition tproj1 {A B : Type} (p : tprod A B) := proj1 p
definition tproj2 {A B : Type} (p : tprod A B) := proj2 p

theorem tproj1_tpair {A B : Type} (a : A) (b : B) : tproj1 (tpair a b) = a
:= refl _

theorem tproj2_tpair {A B : Type} (a : A) (b : B) : tproj2 (tpair a b) = b
:= refl _

set_opaque tprod true
set_opaque tpair true
set_opaque tproj1 true
set_opaque tproj2 true

infix 60 ## : tprod

add_rewrite tproj1_tpair tproj2_tpair


--
-- some stuff for the kernel
-- TODO: come up with better names?
--

theorem imp_eq_true {b : Bool} : b → b = ⊤
:= case _ (take H, refl _) (take H, false_elim _ H) b

theorem not_imp_eq_false {b : Bool} : ¬ b → b = ⊥
:= case (λx, ¬ x → x = ⊥) (take H, absurd_elim _ trivial H) (take H, refl _) b

theorem imp_if_eq {A : Type} {b : Bool} (H : b) (a a' : A) : (if b then a else a') = a
:= 
  calc
    (if b then a else a') = (if ⊤ then a else a') : {imp_eq_true H}
      ... = a : if_true _ _

theorem not_imp_if_eq {A : Type} {b : Bool} (H : ¬ b) (a a' : A) : (if b then a else a') = a'
:= 
  calc
    (if b then a else a') = (if ⊥ then a else a') : {not_imp_eq_false H}
      ... = a' : if_false _ _

-- allows "proof by cases"
theorem by_cases {P : Bool} (b : Bool) (H1 : b → P) (H2 : ¬ b → P) : P
:= or_elim (em b) H1 H2


--
-- some stuff nat
--

add_rewrite add_zero_left add_zero_right
add_rewrite mul_zero_left mul_zero_right

-- this seems to be the more natural formulation
theorem succ_positive' (x : ℕ) : succ x > 0 := succ_positive (refl _)

-- add to nat, and variations
theorem not_lt_imp_le {x y : ℕ} (H : ¬ x < y) : y ≤ x
:= resolve_left (le_or_lt _ _) H


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
      (subst (succ_positive' y') (symm (zero_mod (succ y'))))
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
              have H7 : 0 < succ y', from succ_positive' _,
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
                      (show x' mod succ y' ≤ y', from lt_succ_le (mod_lt _ _ (succ_positive' _)))
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
