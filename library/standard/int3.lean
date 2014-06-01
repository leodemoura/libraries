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

-------------------------------------------------- add sub

-- the function λnm, n - succ m : nat -> nat -> int
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

theorem add_assoc (a b c : int) : a + b + c = a + (b + c)
:= _

end -- namespace int