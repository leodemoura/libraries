----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-------------------------------------------------- axioms
import nat
import macros

variable int : Type
alias ℤ : int
--builtin numeral -- is this possible for int?

namespace int

using nat

--Inductive int : Type :=
--| pos : nat -> int
--| neg : nat -> int.

variable pos : nat -> ℤ -- n ↦ n
variable neg : nat -> ℤ -- n ↦ -n - 1
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
        (let f : int -> Bool := (int_rec (fun a,true) (fun b, false))
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

-------------------------------------------------- add minus

definition nat_int_minus (n m : nat) : int := if (n ≥ m) then n - m else neg (pred (m - n))
infixl 65 @ : nat_int_minus

check (zero-zero)

-- definition add (z w : int) : int :=
--   int_rec
--     (take m : nat, int_rec
--       (take n : nat, n + m)
--       (take n : nat, if n < m then m - succ n else neg (n - m)) z)
--     (take m : nat, int_rec
--       (take n : nat, if m < n then n - succ m else neg (m - n))
--       (take n : nat, neg (succ (succ (n + m)))) z) w

definition addz (z w : int) : int :=
  int_rec
    (take m : nat, int_rec
      (take n : nat, pos (n + m))
      (take n : nat, if n < m then pos (m - succ n) else neg (n - m)) z)
    (take m : nat, int_rec
      (take n : nat, if m < n then pos (n - succ m) else neg (m - n))
      (take n : nat, neg (succ (n + m))) z) w

infixl 65 + : addz

theorem addz_pos_pos (n m : nat) : pos n + pos m = pos (n + m)
:= trans (int_rec_pos _ _ m) (int_rec_pos _ _ n)

theorem addz_pos_neg (n m : nat) : pos n + neg m = if m < n then pos (n - succ m) else neg (m - n)
:= trans (int_rec_neg _ _ m) (int_rec_pos _ _ n)

theorem addz_neg_pos (n m : nat) : neg n + pos m = if n < m then pos (m - succ n) else neg (n - m)
:= trans (int_rec_pos _ _ m) (int_rec_neg _ _ n)

theorem addz_neg_neg (n m : nat) : neg n + neg m = neg (succ (n + m))
:= trans (int_rec_neg _ _ m) (int_rec_neg _ _ n)

theorem addz_pos_gt_neg {n m : nat} (H : n > m) : pos n + neg m = pos (n - succ m)
:=
  calc
    pos n + neg m = if m < n then pos (n - succ m) else neg (m - n) : addz_pos_neg n m
      ... = if true then pos (n - succ m) else neg (m - n) : {eqt_intro H}
      ... = pos (n - succ m) : if_true _ _

theorem addz_pos_le_neg {n m : nat} (H : n ≤ m) : pos n + neg m = neg (m - n)
:=
  have H2 : ¬ m < n, from le_lt_antisym H,
  calc
    pos n + neg m = if m < n then pos (n - succ m) else neg (m - n) : addz_pos_neg n m
      ... = if false then pos (n - succ m) else neg (m - n) : {eqf_intro H2}
      ... = neg (m - n) : if_false _ _

theorem addz_neg_lt_pos {n m : nat} (H : n < m) : neg n + pos m = pos (m - succ n)
:=
  calc
    neg n + pos m = if n < m then pos (m - succ n) else neg (n - m) : addz_neg_pos n m
      ... = if true then pos (m - succ n) else neg (n - m) : {eqt_intro H}
      ... = pos (m - succ n) : if_true _ _

theorem addz_neg_ge_pos {n m : nat} (H : n ≥ m) : neg n + pos m = neg (n - m)
:=
  have H2 : ¬ n < m, from le_lt_antisym H,
  calc
    neg n + pos m = if n < m then pos (m - succ n) else neg (n - m) : addz_neg_pos n m
      ... = if false then pos (m - succ n) else neg (n - m) : {eqf_intro H2}
      ... = neg (n - m) : if_false _ _

check @induction

theorem addz_comm (z w : int) : z + w = w + z
:=
  induction z  _
    _


-- theorem error (z w : int) : z + w = w + z
-- :=
--   have lemma : ∀n m, pos n + neg m = neg m + pos n,
--     from take n m,
--       or_elim (le_or_lt n m)
--         (take H : n ≤ m, calc
--           pos n + neg m = neg (m - n) : addz_pos_le_neg H
--             ... = neg m + pos n : symm (addz_neg_ge_pos H))
--         (take H : m < n, calc
--           pos n + neg m = pos (n - succ m) : addz_pos_gt_neg H
--             ... = neg m + pos n : symm (addz_neg_lt_pos H)),
--   induction z
--     (take n, induction w
--       (take m, calc
--         pos n + pos m = pos (n + m) : addz_pos_pos n m
--           ... = pos (m + n) : {add_comm n m}
--           ... = pos m + pos n : symm (addz_pos_pos m n))
--       (take m, lemma n m))
--     (take n, induction w
--       (take m, symm (lemma m n))
--       (take m, calc
--         neg n + neg m = neg (succ (n + m)) : addz_neg_neg n m
--           ... = neg (succ (m + n)) : {add_comm n m}
--           ... = neg m + neg n : symm (addz_neg_neg m n)))
--------------------------------------------------



end -- namespace int