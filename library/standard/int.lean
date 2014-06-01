es----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-------------------------------------------------- axioms
import nat
import macros

using nat

variable int : Type
alias ℤ : int
--builtin numeral -- is this possible for int?

namespace int

--Inductive int : Type :=
--| intz : int
--| pos : nat -> int
--| neg : nat -> int.

variable intz : ℤ
variable pos : nat -> ℤ -- n ↦ n + 1
variable neg : nat -> ℤ -- n ↦ -n - 1
axiom int_rec {P : ℤ → Type} (x : P intz) (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) (z : ℤ) : P z
axiom int_rec_intz {P : ℤ → Type} (x : P intz) (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) : int_rec x f g intz = x
axiom int_rec_pos {P : ℤ → Type} (x : P intz) (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) (n : nat) :  int_rec x f g (pos n) = f n
axiom int_rec_neg {P : ℤ → Type} (x : P intz) (f : ∀n : nat, P (pos n))
    (g : ∀n : nat, P (neg n)) (n : nat) :  int_rec x f g (neg n) = g n

-------------------------------------------------- basics

---------- coercion
definition nat_int (n : nat) : int := nat_rec intz (fun m x, pos m) n
coercion nat_int

theorem nat_int_zero : nat_int zero = intz
:= nat_rec_zero _ _
theorem nat_int_succ (n:nat) : nat_int (succ n) = pos n
:= nat_rec_succ _ _ _

definition negation (z : int) := int_rec (zero) (fun n : nat, neg n) (fun n : nat, pos n) z

-- theorem neg_pos (n:nat) : neg (succ n) = neg n
-- :=
--   calc
--     neg (succ n) = neg (pos n) : {nat_int_succ n}
--       ... = neg n : int_rec_pos _ _ _ _

-- theorem induction {P : ℤ → Bool} (z : ℤ) (x : P zero) (f : ∀n : nat, P (succ n))
--     (g : ∀n : nat, P (neg (succ n))) : P z
-- :=
--   int_rec
--     (subst x nat_int_zero)
--     (take n : nat, subst (f n) (nat_int_succ n))
--     (take n : nat, subst (g n) (neg_pos n))
--     z


-- definition cast0 {P : ℤ → Type} : P zero == P intz
-- := symm (heq_eq _ _) ◂ congr2 P nat_int_zero
-- definition castpos {P : ℤ → Type} (n : nat) : P (succ n) == P (pos n)
-- := symm (heq_eq _ _) ◂ congr2 P (nat_int_succ n)
-- definition castneg {P : ℤ → Type} (n : nat) : P (neg(succ n)) == P (neg n)
-- := symm (heq_eq _ _) ◂ congr2 P (neg_pos n)

-- theorem int_recz {P : ℤ → Type} (x : P zero) (f : ∀n : nat, P (succ n))
--     (g : ∀n : nat, P (neg (succ n))) (z : ℤ) : P z
-- :=
--   int_rec
--     (cast cast0 x)
--     (take n : nat, cast (castpos n) (f n))
--     (take n : nat, cast (castneg n) (g n))
--     z

-- variable P : ℤ → Type
-- variable x : P zero
-- variable f : ∀n : nat, P (succ n)
-- variable g : ∀n : nat, P (neg (succ n))
-- variable n : nat

-- check (fun n, neg n)

-- check cast_heq (castpos n) (f n)

-- check
-- hcongr (hcongr
-- (hrefl int_rec)
-- (cast_heq cast0 x))
-- (_)


-- check (int::int_rec
--         (cast int::cast0 int::x)
--         (fun n : nat, cast (int::castpos n) (int::f n))
--         (fun n : nat, cast (int::castneg n) (int::g n))
--         int::intz =
--     cast int::cast0 int::x)

-- check   cast (hrefl _)
--     (int_rec_intz
--     (cast cast0 x)
--     (take n : nat, cast (castpos n) (f n))
--     (take n : nat, cast (castneg n) (g n)))

-- theorem int_rec_zero {P : ℤ → Type} (x : P zero) (f : ∀n : nat, P (succ n))
--     (g : ∀n : nat, P (neg (succ n))) : int_rec x f g intz = x
-- :=
--   int_rec_intz
--     (cast cast0 x)
--     (take n : nat, cast (castpos n) (f n))
--     (take n : nat, cast (castneg n) (g n))

-- theorem int_rec_posz {P : ℤ → Type} (x : P zero) (f : ∀n : nat, P (succ n))
--     (g : ∀n : nat, P (neg (succ n))) (n : nat) :  int_recz x f g (pos n) = f n
-- := _
-- theorem int_rec_negz {P : ℤ → Type} (x : P zero) (f : ∀n : nat, P (succ n))
--     (g : ∀n : nat, P (neg (succ n))) (n : nat) :  int_recz x f g (neg n) = g n
-- := _

theorem induction {P : ℤ → Bool} (z : ℤ) (H0 : P intz) (Hp : ∀n : nat, P (pos n))
    (Hn : ∀n : nat, P (neg n)) : P z
:= int_rec H0 Hp Hn z

theorem pos_ne_intz (n : nat) : pos n ≠ intz
:=
  not_intro
    (take H : pos n = intz,
      have H2 : true = false, from
        (let f : int -> Bool := (int_rec false (fun a,true) (fun b, true))
          in calc
            true = f (pos n) : symm (int_rec_pos _ _ _ _)
             ... = f intz : {H}
	           ... = false : int_rec_intz _ _ _),
      absurd H2 true_ne_false)

theorem neg_ne_intz (n : nat) : neg n ≠ intz
:=
  not_intro
    (take H : neg n = intz,
      have H2 : true = false, from
        (let f : int -> Bool := (int_rec false (fun a,true) (fun b, true))
          in calc
            true = f (neg n) : symm (int_rec_neg _ _ _ _)
             ... = f intz : {H}
	           ... = false : int_rec_intz _ _ _),
      absurd H2 true_ne_false)

theorem pos_ne_neg (n m : nat) : pos n ≠ neg m
:=
  not_intro
    (take H : pos n = neg m,
      have H2 : true = false, from
        (let f : int -> Bool := (int_rec false (fun a,true) (fun b, false))
          in calc
            true = f (pos n) : symm (int_rec_pos _ _ _ _)
             ... = f (neg m) : {H}
	           ... = false : int_rec_neg _ _ _ _),
      absurd H2 true_ne_false)

theorem int_cases (z : int) : z = intz ∨ (exists n, z = pos n) ∨ (exists n, z = neg n)
:=
  induction z
    (or_intro_left _ (refl intz))
    (take n, or_intro_right _ (or_intro_left _ (exists_intro n (refl _))))
    (take n, or_intro_right _ (or_intro_right _ (exists_intro n (refl _))))

theorem int_discriminate {B : Bool} {z : int} (H1: z = intz → B) (H2 : ∀n, z = pos n → B) (H3 : ∀n, z = neg n → B) : B
:=
  or_elim (int_cases z)
    (take Hz : z = intz, H1 Hz)
    (take H4, or_elim H4
      (take H5, obtain (n : nat) (Hz : z = pos n), from H5, H2 n Hz)
      (take H5, obtain (n : nat) (Hz : z = neg n), from H5, H3 n Hz))

definition abs (z : int) := int_rec zero (fun n : nat, succ n) (fun n : nat, succ n) z

theorem abs_intz : abs intz = zero
:= int_rec_intz _ _ _
theorem abs_pos (n:nat) : abs (pos n) = succ n
:= int_rec_pos _ _ _ _
theorem abs_neg (n:nat) : abs (neg n) = succ n
:= int_rec_neg _ _ _ _

theorem pos_inj {n m:nat} (H : pos n = pos m) : n = m
:=
  calc
    n = pred (succ n) : symm (pred_succ n)
  ... = pred (abs (pos n)) : {symm (abs_pos n)}
  ... = pred (abs (pos m)) : {H}
  ... = pred (succ m) : {abs_pos m}
  ... = m : pred_succ m

theorem neg_inj {n m:nat} (H : neg n = neg m) : n = m
:=
  calc
    n = pred (succ n) : symm (pred_succ n)
  ... = pred (abs (neg n)) : {symm (abs_neg n)}
  ... = pred (abs (neg m)) : {H}
  ... = pred (succ m) : {abs_neg m}
  ... = m : pred_succ m

-------------------------------------------------- add



--------------------------------------------------

set_opaque abs true

end -- namespace int