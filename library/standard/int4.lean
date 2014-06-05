
----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import nat
import macros
import subtype


theorem eq_hcongr2 {A B : (Type U)} {a b : A} (f : A → B) (H : a = b) : f a == f b
:= subst (congr2 f H) (symm (heq_eq (f a) (f b)))

-------------------------------------------------- quotients

namespace quot

-- variable quotient (A : Type) (R : A → A → Bool) : Type
-- infix 100 // : quotient
-- variable abs {A : Type} {R : A → A → Bool} (a : A) : A//R
-- variable relate {A : Type} {R : A → A → Bool} {a b : A} (H : R a b) : (@abs A R a) = (abs b)
-- variable quotient_rec {A : Type} {R : A → A → Bool} {C : A//R → Type}
--     (f : forall (a : A), C (abs a))
--     (H : forall (a b : A) (r : R a b),
--         cast (eq_hcongr2 C (relate r)) (f a) = f b) (a : A//R) : (C a)
-- axiom quotient_comp {A : Type} {R : A → A → Bool} {C : A // R → Type}
--                                     (f : forall (a : A), C (abs a)) (H : forall (a b : A) (r : R a b), cast (eq_hcongr2 C (relate r)) (f a) = f b)
--                                           (a : A) :
--                quotient_rec f H (abs a) = f a

----------

-- definition is_quotient {A B : Type} (R : A → A → Bool) (abs : A → B) (rep : B → A) : Bool
-- :=
--   (∀b, abs (rep b) = b) ∧
--   (∀b, R (rep b) (rep b)) ∧
--   (∀r s, R r s <-> (R r r ∧ R s s ∧ abs r = abs s))

-- theorem quotient_intro {A B : Type} (R : A → A → Bool) {abs : A → B} {rep : B → A}
--     (H1 : ∀b, abs (rep b) = b) (H2 : ∀b, R (rep b) (rep b))
--     (H3 : ∀r s, R r s <-> (R r r ∧ R s s ∧ abs r = abs s)) : is_quotient R abs rep
-- := and_intro H1 (and_intro H2 H3)

-- theorem quotient_abs_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) (b : B) :  abs (rep b) = b
-- := and_elim_left H b

-- theorem quotient_refl_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) (b : B) : R (rep b) (rep b)
-- := and_elim_left (and_elim_right H) b

-- theorem quotient_R_iff {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) (r s : A) : R r s <-> (R r r ∧ R s s ∧ abs r = abs s)
-- := and_elim_right (and_elim_right H) r s

-- theorem quotient_refl_left {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) {r s : A} (H2 : R r s) : R r r
-- := and_elim_left (iff_elim_left (quotient_R_iff H r s) H2)

-- theorem quotient_refl_right {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) {r s : A} (H2 : R r s) : R s s
-- := and_elim_left (and_elim_right (iff_elim_left (quotient_R_iff H r s) H2))

-- theorem quotient_eq_abs {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) {r s : A} (H2 : R r s) : abs r = abs s
-- := and_elim_right (and_elim_right (iff_elim_left (quotient_R_iff H r s) H2))

-- theorem quotient_R {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H : is_quotient R abs rep) {r s : A} (H2 : R r r) (H3 : R s s) (H4 : abs r = abs s) : R r s
-- := iff_elim_right (quotient_R_iff H r s) (and_intro H2 (and_intro H3 H4))

-- definition quotient_rec2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H1 : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
--     (H2 : forall (r s : A) (H : R r s),
--         cast (eq_hcongr2 C (quotient_eq_abs H1 H)) (f r) = f s)
--     (b : B) : C b
-- := cast (eq_hcongr2 C (quotient_abs_rep H1 b)) (f (rep b))

-- theorem quotient_comp2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
--     (H1 : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
--     (H2 : forall (r s : A) (H : R r s),
--         cast (eq_hcongr2 C (quotient_eq_abs H1 H)) (f r) = f s)
--     (a : A) : quotient_rec2 H1 f H2 (abs a) = f a
-- := _

definition reflexive {A : Type} (R : A → A → Bool) : Bool := ∀a, R a a

definition is_quotient {A B : Type} (R : A → A → Bool) (abs : A → B) (rep : B → A) : Bool
:=
  (reflexive R) ∧
  (∀b, abs (rep b) = b) ∧
  (∀r s, R r s <-> abs r = abs s)

theorem quotient_intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
    (H3 : ∀r s, R r s <-> abs r = abs s) : is_quotient R abs rep
:= and_intro H1 (and_intro H2 H3)

theorem quotient_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H : is_quotient R abs rep) : reflexive R
:= and_elim_left H

theorem quotient_abs_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H : is_quotient R abs rep) (b : B) : abs (rep b) = b
:= and_elim_left (and_elim_right H) b

theorem quotient_R_iff {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H : is_quotient R abs rep) (r s : A) : R r s <-> abs r = abs s
:= and_elim_right (and_elim_right H) r s

theorem quotient_eq_abs {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : is_quotient R abs rep) {r s : A} (H2 : R r s) : abs r = abs s
:= iff_elim_left (quotient_R_iff H1 r s) H2

theorem quotient_R_intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : is_quotient R abs rep) {r s : A} (H2 : abs r = abs s) : R r s
:= iff_elim_right (quotient_R_iff H1 r s) (H2)

definition quotient_rec2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
    (H2 : forall (r s : A) (H : R r s),
        cast (eq_hcongr2 C (quotient_eq_abs H1 H)) (f r) = f s)
    (b : B) : C b
:= cast (eq_hcongr2 C (quotient_abs_rep H1 b)) (f (rep b))

theorem quotient_comp2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
    (H2 : forall (r s : A) (H : R r s),
        cast (eq_hcongr2 C (quotient_eq_abs H1 H)) (f r) = f s)
    (a : A) : quotient_rec2 H1 f H2 (abs a) = f a
:=
  have H3 : abs a = abs (rep (abs a)), from symm (quotient_abs_rep H1 (abs a)),
  have H4 : R a (rep (abs a)), from quotient_R_intro H1 H3,
  calc
    quotient_rec2 H1 f H2 (abs a) = cast _ (f (rep (abs a))) : refl _
      ... = cast _ (cast _ (f a)) : {symm (H2 _ _ H4)}
      ... = cast _ (f a) : cast_trans _ _ _
      ... = f a : cast_eq _ _

set_opaque quotient_rec2 true

end -- namespace quot

-------------------------------------------------- axioms


namespace int

using nat
using quot
using subtype
unary_nat

definition int := subtype (ℕ ## ℕ) (fun a, tproj1 a = 0 ∨ tproj2 a = 0)
alias ℤ : int

theorem int_inhabited : inhabited int
:= subtype_inhabited (tpair 0 0) (or_intro_left _ (tproj1_tpair 0 0))

definition int_rel (a b : ℕ ## ℕ) : Bool := tproj1 a + tproj2 b = tproj2 a + tproj1 b

definition int_abs (a : ℕ ## ℕ) : int
:=
  if tproj1 a ≥ tproj2 a
    then abst (tpair (tproj1 a - tproj2 a) 0) int_inhabited
    else abst (tpair 0 (tproj2 a - tproj1 a)) int_inhabited

axiom sorry (a b : ℕ ## ℕ) : int_rel a b ↔ int_abs a = int_abs b

theorem int_quotient : is_quotient int_rel int_abs rep
:=
  quotient_intro
    (show reflexive int_rel, from take a : ℕ ## ℕ, add_comm (tproj1 a) (tproj2 a))
    (take b : int,
      show int_abs (rep b) = b, from
      nat_discriminate
        (assume H : tproj2 (rep b) = 0,
          have H2 : tproj1 (rep b) ≥ tproj2 (rep b), from subst (le_zero _) (symm H),
          calc
            int_abs (rep b) = if true then _  else _ : {eqt_intro H2}
              ... = abst (tpair (tproj1 (rep b) - tproj2 (rep b)) 0) int_inhabited : if_true _ _
              ... = abst (tpair (tproj1 (rep b) - 0) 0) int_inhabited : {H}
              ... = abst (tpair (tproj1 (rep b)) 0) int_inhabited : {sub_zero_right _}
              ... = abst (tpair (tproj1 (rep b)) (tproj2 (rep b))) int_inhabited : {symm H}
              ... = abst (rep b) int_inhabited : {tpair_tproj_eq (rep b)}
              ... = b : abst_rep _ b)
        (take n : nat,
          assume H : tproj2 (rep b) = succ n,
          have H2 : tproj1 (rep b) = 0,
            from resolve_left (P_rep b) (subst (succ_ne_zero n) (symm H)),
          have H3 : tproj1 (rep b) < tproj2 (rep b),
            from subst (subst (lt_zero n) (symm H)) (symm H2),
          have H4 : ¬ tproj1 (rep b) ≥ tproj2 (rep b), from lt_le_antisym H3,
          calc
            int_abs (rep b) = if false then _  else _ : {eqf_intro H4}
              ... = abst (tpair 0 (tproj2 (rep b) - tproj1 (rep b))) int_inhabited : if_false _ _
              ... = abst (tpair 0 (tproj2 (rep b) - 0)) int_inhabited : {H2}
              ... = abst (tpair 0 (tproj2 (rep b))) int_inhabited : {sub_zero_right _}
              ... = abst (tpair (tproj1 (rep b)) (tproj2 (rep b))) int_inhabited : {symm H2}
              ... = abst (rep b) int_inhabited : {tpair_tproj_eq (rep b)}
              ... = b : abst_rep _ b))
    (take a b : ℕ ## ℕ,
      show int_rel a b ↔ int_abs a = int_abs b, from sorry a b) -- to be proven


--- everything below still needs to be changed

variable pos : nat → ℤ -- n ↦ n
variable neg : nat → ℤ -- n ↦ -n - 1
axiom int_rec {P : ℤ → Type} (f : ∀n : nat, P (pos n)) (g : ∀n : nat, P (neg n)) (z : ℤ) : P z
axiom int_rec_pos {P : ℤ → Type} (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) (n : nat) :  int_rec f g (pos n) = f n
axiom int_rec_neg {P : ℤ → Type} (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) (n : nat) :  int_rec f g (neg n) = g n





-------------------------------------------------- basics

coercion pos

--definition negation (z : int) := int_rec (fun n : nat, neg n) (fun n : nat, pos n) z

theorem induction {P : ℤ → Bool} (z : ℤ) (Hp : ∀n : nat, P (pos n))
    (Hn : ∀n : nat, P (neg n)) : P z
:= int_rec Hp Hn z

theorem pos_ne_neg (n m : nat) : pos n ≠ neg m
:=
  not_intro
    (take H : pos n = neg m,
      have H2 : true = false, from
        (let f : int → Bool := (int_rec (fun a,true) (fun b, false))
          in calc
            true = f (pos n) : symm (int_rec_pos _ _ _)
             ... = f (neg m) : {H}
	           ... = false : int_rec_neg _ _ _),
      absurd H2 true_ne_false)

theorem int_cases (z : int) : (exists n, z = pos n) ∨ (exists n, z = neg n)
:=
  induction z
    (take n, or_intro_left _ (exists_intro n (refl _)))
    (take n, or_intro_right _ (exists_intro n (refl _)))

theorem int_discriminate {B : Bool} {z : int} (Hp : ∀n, z = pos n → B)
    (Hn : ∀n, z = neg n → B) : B
:=
  or_elim (int_cases z)
    (take H, obtain (n : nat) (Hz : z = pos n), from H, Hp n Hz)
    (take H, obtain (n : nat) (Hz : z = neg n), from H, Hn n Hz)

definition abs (z : int) : nat := int_rec (fun n : nat, n) (fun n : nat, succ n) z

theorem abs_pos (n:nat) : abs (pos n) = n
:= int_rec_pos _ _ _
theorem abs_neg (n:nat) : abs (neg n) = succ n
:= int_rec_neg _ _ _

set_opaque abs true

theorem pos_inj {n m:nat} (H : pos n = pos m) : n = m
:=
  calc
    n = abs (pos n) : {symm (abs_pos n)}
  ... = abs (pos m) : {H}
  ... = m : {abs_pos m}

theorem neg_inj {n m:nat} (H : neg n = neg m) : n = m
:=
  calc
    n = pred (succ n) : symm (pred_succ n)
  ... = pred (abs (neg n)) : {symm (abs_neg n)}
  ... = pred (abs (neg m)) : {H}
  ... = pred (succ m) : {abs_neg m}
  ... = m : pred_succ m

-------------------------------------------------- add sub

-- the function λnm, n - succ m : nat → nat → int
definition nz_sub (n m : nat) : int := if (n > m) then pred (n - m) else neg (m - n)

theorem nz_sub_ge {n m : nat} (H : n > m) : nz_sub n m = pred (n - m)
:=
  calc
    nz_sub n m = if true then pred (n - m) else neg (m - n) : {eqt_intro H}
      ... = pred (n - m) : if_true _ _

theorem nz_sub_lt {n m : nat} (H : n ≤ m) : nz_sub n m = neg (m - n)
:=
  calc
    nz_sub n m = if false then pos (pred (n - m)) else neg (m - n) : {eqf_intro (le_lt_antisym H)}
      ... = neg (m - n) : if_false _ _

definition add (z w : int) : int :=
  int_rec
    (take m : nat, int_rec
      (take n : nat, pos (n + m))
      (take n : nat, nz_sub m n) z)
    (take m : nat, int_rec
      (take n : nat, nz_sub n m)
      (take n : nat, neg (succ (n + m))) z) w

infixl 65 + : int::add

theorem add_pos_pos (n m : nat) : pos n + pos m = pos (n + m)
:= trans (int_rec_pos _ _ m) (int_rec_pos _ _ n)

theorem add_pos_neg (n m : nat) : pos n + neg m = nz_sub n m
:= trans (int_rec_neg _ _ m) (int_rec_pos _ _ n)

theorem add_neg_pos (n m : nat) : neg n + pos m = nz_sub m n
:= trans (int_rec_pos _ _ m) (int_rec_neg _ _ n)

theorem add_neg_neg (n m : nat) : neg n + neg m = neg (succ (n + m))
:= trans (int_rec_neg _ _ m) (int_rec_neg _ _ n)

theorem add_comm (a b : int) : a + b = b + a
:=
  induction a
    (take n, induction b
      (take m,  calc
         pos n + pos m = pos (n + m) : add_pos_pos n m
           ... = pos (m + n) : {add_comm n m}
           ... = pos m + pos n : symm (add_pos_pos m n))
      (take m, trans (add_pos_neg n m) (symm (add_neg_pos m n))))
    (take n, induction b
      (take m, trans (add_neg_pos n m) (symm (add_pos_neg m n)))
      (take m, calc
         neg n + neg m = neg (succ (n + m)) : add_neg_neg n m
           ... = neg (succ (m + n)) : {add_comm n m}
           ... = neg m + neg n : symm (add_neg_neg m n)))

-- theorem add_assoc (a b c : int) : a + b + c = a + (b + c)
-- := _

end -- namespace int
