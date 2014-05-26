----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Carnegie Mellon University. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-------------------------------------------------- axioms
import kernel
import macros

variable nat : Type
alias ℕ : nat
--builtin numeral -- When transitioning to numerals, first replace "(succ zero)" and "succ zero" by "1" and then "zero" by "0" (except in names)
namespace nat
variable zero : nat
alias z : zero
variable succ : nat -> nat
alias s : succ
axiom nat_rec {P : nat → Type} (x : P zero)  (f : ∀ m : nat, P m → P (s m)) (m:nat) : P m
axiom nat_rec_zero {P : nat → Type} (x : P zero) (f : ∀ m : nat, P m → P (s m)) : nat_rec x f zero = x
axiom nat_rec_succ {P : nat → Type} (x : P zero) (f : ∀ m : nat, P m → P (s m)) (n : nat) : 
    nat_rec x f (succ n) = f n  (nat_rec x f n)

-------------------------------------------------- succ pred

theorem induction_on {P : nat → Bool} (a : nat) (H1 : P zero) (H2 : ∀ (n : nat) (IH : P n), P (succ n)) : P a
:= nat_rec H1 H2 a

theorem zero_ne_succ (n:nat) : zero ≠ succ n
:=
  not_intro 
    (take H: zero = succ n,
      have H2 : true = false, from      
        (let f : nat -> Bool := (nat_rec true (fun a b,false))
          in calc true = f zero : symm (nat_rec_zero _ _)
            ... = f (succ n) : {H}
	         ... = false : nat_rec_succ _ _ _),
      absurd H2 true_ne_false)

definition pred (a : nat) := nat_rec zero (fun m x, m) a

theorem pred_zero : pred zero = zero 
:= nat_rec_zero _ _
theorem pred_succ (n:nat) : pred (succ n) = n 
:= nat_rec_succ _ _ _

set_opaque pred true

theorem zero_or_succ (n:nat) : n = zero ∨ n = succ (pred n)
:= 
  induction_on n
    (or_intro_left _ (refl zero)) 
    (take m IH, or_intro_right _ 
      (show s m = s (pred (s m)), from congr2 s (symm (pred_succ m))))

theorem zero_or_succ2 (n:nat) : n = zero ∨ ∃k, n = succ k
:= or_elim (zero_or_succ n) (take H, or_intro_left _ H) (take H, or_intro_right _ (exists_intro (pred n) H))

theorem nat_discriminate {B : Bool} {n : nat} (H1: n = zero → B) (H2 : ∀ m, n = succ m → B) : B
:= 
  or_elim (zero_or_succ n)
    (take H3 : n = zero, H1 H3)
    (take H3 : n = succ (pred n), H2 (pred n) H3)

theorem succ_inj {n m:nat} (H : succ n = succ m) : n = m
:= 
  calc n = pred (succ n)    : symm (pred_succ n)
    ... = pred (succ m)  : {H}
    ... = m	   	       : pred_succ m

theorem succ_ne_self (n:nat) : n ≠ succ n
:= 
  not_intro (induction_on n
    (take H : zero = succ zero, 
      have neq : zero ≠ succ zero, from zero_ne_succ zero,
      absurd H neq)
    (take k IH H, IH (succ_inj H)))

-------------------------------------------------- add

definition add (a b : nat) := nat_rec a (fun m x, succ x) b
infixl 65 +  : add

theorem add_zero_right (n:nat) : n + zero = n 
:= nat_rec_zero _ _
theorem add_succ_right (n m:nat) : n + succ m = succ (n + m) 
:= nat_rec_succ _ _ _

set_opaque add true

theorem add_zero_left (n:nat) : zero + n = n
:= 
  induction_on n 
    (add_zero_right zero) 
    (take m IH, show zero + s m = s m, from
      calc 
        zero + succ m = succ (zero + m) : add_succ_right _ _
   	    ... = succ m : {IH})

theorem add_succ_left (n m:nat) : (succ n) + m = succ (n + m)
:= 
  induction_on m
    (calc 
      succ n + zero = succ n : add_zero_right (succ n)
        ... = succ (n + zero) : {symm (add_zero_right n)})
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
      (n + m) + zero = n + m : add_zero_right _
        ... = n + (m + zero) : {symm (add_zero_right m)})
    (take l IH, 
      calc 
        (n + m) + succ l = succ ((n + m) + l) : add_succ_right _ _
          ... = succ (n + (m + l)) : {IH}
          ... = n + succ (m + l) : symm (add_succ_right _ _)
          ... = n + (m + succ l) : {symm (add_succ_right _ _)})

theorem add_left_comm (n m k : nat) : n + (m + k) = m + (n + k)
:= left_comm add_comm add_assoc n m k

theorem add_left_inj {n m k : nat} : n + m = n + k → m = k
:=
  induction_on n
    (take H : zero + m = zero + k,
      calc 
        m = zero + m : symm (add_zero_left m)
          ... = zero + k : H
          ... = k : add_zero_left k)
    (take (n : nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
      have H2 : succ (n + m) = succ (n + k),
      from calc 
        succ (n + m) = succ n + m : symm (add_succ_left n m)
          ... = succ n + k : H
          ... = succ (n + k) : add_succ_left n k,
      have H3 : n + m = n + k, from succ_inj H2, 
      IH H3)

theorem add_right_inj {n m k : nat} (H : n + m = k + m) : n = k
:=
  have H2 : m + n = m + k,
    from calc 
      m + n = n + m : add_comm m n
      ... = k + m : H
      ... = m + k : add_comm k m,
    add_left_inj H2

theorem add_eq_zero_left {n m : nat} : n + m = zero → n = zero
:=
  induction_on n (take (H : zero + m = zero), refl zero)
    (take k IH,
      assume (H : succ k + m = zero), 
      absurd_elim (succ k = zero)
        (show zero = succ (k + m), from
          calc
            zero = succ k + m : symm H
              ... = succ (k + m) : add_succ_left k m)
        (zero_ne_succ (k + m)))

theorem add_eq_zero_right {n m : nat} (H : n + m = zero) : m = zero
:= add_eq_zero_left (trans (add_comm m n) H)

theorem add_eq_zero {n m : nat} (H : n + m = zero) : n = zero ∧ m = zero
:= and_intro (add_eq_zero_left H) (add_eq_zero_right H)

theorem add_one (n:nat) : n + succ zero = succ n
:= 
  calc 
    n + succ zero = succ (n + zero) : add_succ_right _ _
      ... = succ n : {add_zero_right _}

theorem add_one_rev (n:nat) : succ zero + n = succ n
:= 
  calc 
    succ zero + n = succ (zero + n) : add_succ_left _ _
      ... = succ n : {add_zero_left _}

--the following theorem has a terrible name, but since the name is not a substring or superstring of another name, it is at least easy to globally replace it
theorem induction_plus_one {P : nat → Bool} (a : nat) (H1 : P zero)
    (H2 : ∀ (n : nat) (IH : P n), P (n + succ zero)) : P a
:= nat_rec H1 (take n IH, subst (H2 n IH) (add_one n)) a

--definition one := succ zero
--theorem foo {P : nat → Bool} (a : nat) (H : P (one)) (H2 : false) : P (succ a)
--:= induction_on a H (false_elim (forall k IH, P (succ (succ k))) H2)

--definition zz := zero
--theorem foo_zz {P : nat → Bool} (a : nat) (H : P zz) (H2 : false) : P a
--:= induction_on a H (false_elim (forall k IH, P (succ k)) H2)

theorem two_step_induction_on {P : nat → Bool} (a : nat) (H1 : P zero) (H2 : P (succ zero)) 
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

-------------------------------------------------- mul

definition mul (n m : nat) := nat_rec zero (fun m x, x + n) m
infixl 70 *  : mul

theorem mul_zero_right (n:nat) : n * zero = zero 
:= nat_rec_zero _ _
theorem mul_succ_right (n m:nat) : n * succ m = n * m + n 
:= nat_rec_succ _ _ _

set_opaque mul true

theorem mul_zero_left (n:nat) : zero * n = zero
:= 
  induction_on n 
    (mul_zero_right zero) 
    (take m IH, 
      calc 
        zero * succ m = zero * m + zero : mul_succ_right _ _
          ... = zero * m : add_zero_right _
          ... = zero : IH)

theorem mul_succ_left (n m:nat) : (succ n) * m = (n * m) + m
:= 
  induction_on m
    (calc 
      succ n * zero = zero : mul_zero_right _
        ... = n * zero : symm (mul_zero_right _)
        ... = n * zero + zero 	: symm (add_zero_right _))
    (take k IH, 
      calc 
        succ n * succ k = (succ n * k) + succ n : mul_succ_right _ _
            ... = (n * k) + k + succ n : { IH }
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

theorem mul_add_distr_left  (n m k : nat) : (n + m) * k = n * k + m * k
:= 
  induction_on k
    (calc 
      (n + m) * zero = zero : mul_zero_right _
        ... = zero + zero : symm (add_zero_right _)
        ... = n * zero + zero : {symm (mul_zero_right _)}
        ... = n * zero + m * zero : {symm (mul_zero_right _)})
    (take l IH, 
      calc 
        (n + m) * succ l = (n + m) * l + (n + m) : mul_succ_right _ _
          ... = n * l + m * l + (n + m) : {IH}
          ... = n * l + m * l + n + m : symm (add_assoc _ _ _)
          ... = n * l + (m * l + n) + m : {add_assoc _ _ _}
          ... = n * l + (n + m * l) + m : {add_comm _ _}
          ... = n * l + n + m * l + m : {symm (add_assoc _ _ _)}
          ... = n * l + n + (m * l + m) : add_assoc _ _ _
          ... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
          ... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})


theorem mul_add_distr_right  (n m k : nat) : n * (m + k) = n * m + n * k
:= 
  calc 
    n * (m + k) = (m + k) * n : mul_comm _ _
      ... = m * n + k * n : mul_add_distr_left _ _ _
      ... = n * m + k * n : {mul_comm _ _}
      ... = n * m + n * k : {mul_comm _ _}

theorem mul_assoc (n m k:nat) : (n * m) * k = n * (m * k)
:= 
  induction_on k 
    (calc 
      (n * m) * zero = zero : mul_zero_right _
        ... = n * zero : symm (mul_zero_right _)
        ... = n * (m * zero) : {symm (mul_zero_right _)})
    (take l IH, 
      calc 
        (n * m) * succ l = (n * m) * l + n * m : mul_succ_right _ _
          ... = n * (m * l) + n * m : {IH}
          ... = n * (m * l + m) : symm (mul_add_distr_right _ _ _)
          ... = n * (m * succ l) : {symm (mul_succ_right _ _)})

theorem mul_left_comm (n m k : nat) : n * (m * k) = m * (n * k)
:= left_comm mul_comm mul_assoc n m k

theorem mul_one_right (n : nat) : n * succ zero = n
:=
  calc
    n * succ zero = n * zero + n : mul_succ_right n zero
      ... = zero + n : {mul_zero_right n}
      ... = n : add_zero_left n

theorem mul_one_left (n : nat) : succ zero * n = n
:=
  calc
    succ zero * n = n * succ zero : mul_comm _ _
      ... = n : mul_one_right n

theorem mul_eq_zero {n m : nat} (H : n * m = zero) : n = zero ∨ m = zero
:= 
  nat_discriminate 
    (take Hn : n = zero, or_intro_left _ Hn)
    (take (k : nat),
      assume (Hk : n = succ k),
      nat_discriminate 
        (take (Hm : m = zero), or_intro_right _ Hm)
        (take (l : nat),
          assume (Hl : m = succ l),
          have Heq : succ (k * succ l + l) = n * m, from
            symm (calc
              n * m = n * succ l : { Hl }
                ... = succ k * succ l : { Hk }
                ... = k * succ l + succ l : mul_succ_left _ _
                ... = succ (k * succ l + l) : add_succ_right _ _),
          absurd_elim _  (symm (trans Heq H)) (zero_ne_succ _)))

theorem mul_eq_succ_left {n m k : nat} (H : n * m = succ k) : exists l, n = succ l
:= 
  nat_discriminate
    (assume H2 : n = zero,
      absurd_elim _
        (calc
          zero = zero * m : symm (mul_zero_left m)
            ... = n * m : {symm H2}
            ... = succ k : H)
        (zero_ne_succ k))
    (take l Hl, exists_intro l Hl)

theorem mul_eq_succ_right {n m k : nat} (H : n * m = succ k) : exists l, m = succ l
:= mul_eq_succ_left (subst H (mul_comm n m))

theorem mul_left_inj {n m k : nat} (H : succ n * m = succ n * k) : m = k
:=
  have general : ∀ m, succ n * m = succ n * k → m = k, from
    induction_on k
      (take m:nat,
        assume H : succ n * m = succ n * zero,
        have H2 : succ n * m = zero,
          from calc
            succ n * m = succ n * zero : H
              ... = zero : mul_zero_right (succ n),
        have H3 : succ n = zero ∨ m = zero, from mul_eq_zero H2,
        resolve_right H3 (ne_symm (zero_ne_succ n)))
      (take (l : nat),
        assume (IH : ∀ m, succ n * m = succ n * l → m = l),
        take (m : nat),
        assume (H : succ n * m = succ n * succ l), 
        have H2 : succ n * m = succ (succ n * l + n),
          from calc
            succ n * m = succ n * succ l : H
              ... = succ n * l + succ n : mul_succ_right (succ n) l
              ... = succ (succ n * l + n) : add_succ_right _ n,
        obtain (l2:nat) (Hm : m = succ l2), from mul_eq_succ_right H2,
        have H3 : succ n * l2 + succ n = succ n * l + succ n,
          from calc
            succ n * l2 + succ n = succ n * succ l2 : symm (mul_succ_right (succ n) l2)
              ... = succ n * m :  {symm Hm} --doesn't work
              ... = succ n * succ l : H
              ... = succ n * l + succ n : mul_succ_right (succ n) l,
        have H4 : succ n * l2 = succ n * l, from add_right_inj H3,
        calc
          m = succ l2 : Hm
            ... = succ l : {IH l2 H4}),
  general m H

theorem mul_right_inj {n m k : nat} (H : n * succ m = k * succ m) : n = k
:=
  have H2 : succ m * n = succ m * k,
    from calc 
      succ m * n = n * succ m : mul_comm (succ m) n
      ... = k * succ m : H
      ... = succ m * k : mul_comm k (succ m),
    mul_left_inj H2

theorem mul_eq_one_left {n m : nat} (H : n * m = succ zero) : n = succ zero 
:= 
  obtain (k : nat) (Hm : m = succ k), from (mul_eq_succ_right H),
  obtain (l1 : nat) (Hn : n = succ l1), from (mul_eq_succ_left H),
    nat_discriminate
      (take Hl : l1 = zero, 
        calc 
          n = succ l1 : Hn
            ... = succ zero : {Hl})
      (take (l2 : nat), 
      assume (Hl : l1 = succ l2), 
      have H2 : succ zero = succ (succ (succ (succ l2) * k + l2)), 
        from calc
          succ zero = n * m : symm H
            ... = n * succ k : { Hm }
            ... = succ l1 * succ k : { Hn }
            ... = succ (succ l2) * succ k : { Hl }
            ... = succ (succ l2) * k + succ (succ l2) : { mul_succ_right _ _ }
            ... = succ (succ (succ l2) * k + succ l2): add_succ_right _ _
            ... = succ (succ (succ (succ l2) * k + l2)) : { add_succ_right _ _ },
        absurd_elim _ (succ_inj H2) (zero_ne_succ _))

theorem mul_eq_one_right {n m : nat} (H : n * m = succ zero) : m = succ zero 
:= mul_eq_one_left (subst H (mul_comm n m))

theorem mul_eq_one {n m : nat} (H : n * m = succ zero) : n = succ zero ∧ m = succ zero 
:= and_intro (mul_eq_one_left H) (mul_eq_one_right H)

-------------------------------------------------- le

definition le (n m:nat) : Bool := exists k:nat, n + k = m
infix  50 <= : le
infix  50 ≤  : le

theorem le_intro {n m k : nat} (H : n + k = m) : n ≤ m
:= exists_intro k H

theorem le_elim {n m : nat} (H : n ≤ m) : ∃ k, n + k = m
:= H

set_opaque le true

theorem le_refl (n : nat) : n ≤ n 
:= le_intro (add_zero_right n)

theorem zero_le (n : nat) : zero ≤ n 
:= le_intro (add_zero_left n)

theorem zero_le_inv {n:nat} (H : n ≤ zero) : n = zero
:=
  obtain (k : nat) (Hk : n + k = zero), from le_elim H,
  add_eq_zero_left Hk

theorem le_trans {n m k : nat} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k
:= 
  obtain (l1 : nat) (Hl1 : n + l1 = m), from le_elim H1,
  obtain (l2 : nat) (Hl2 : m + l2 = k), from le_elim H2,
  le_intro 
    (calc 
      n + (l1 + l2) =  n + l1 + l2 : symm (add_assoc n l1 l2)
        ... = m + l2 : { Hl1 }
        ... = k : Hl2)

theorem le_antisym {n m : nat} (H1 : n ≤ m) (H2 : m ≤ n) : n = m
:= 
  obtain (k : nat) (Hk : n + k = m), from (le_elim H1),
  obtain (l : nat) (Hl : m + l = n), from (le_elim H2),
  have L1 : k + l = zero, from
    add_left_inj
      (calc 
        n + (k + l) = n + k + l : { symm (add_assoc n k l) }
          ... = m + l : { Hk }
          ... = n : Hl
          ... = n + zero : symm (add_zero_right n)),
  have L2 : k = zero, from add_eq_zero_left L1,
    calc 
      n = n + zero : symm (add_zero_right n)
        ... = n  + k : { symm L2 }
        ... = m : Hk

axiom le_total (n m : nat) : n ≤ m ∨ m ≤ n

theorem add_le_left {n m : nat} (H : n ≤ m) (k : nat) : k + n ≤ k + m
:= 
  obtain (l : nat) (Hl : n + l = m), from (le_elim H),
  le_intro 
    (calc 
        k + n + l  = k + (n + l) : add_assoc k n l
          ... = k + m : { Hl })

theorem add_le_right {n m : nat} (H : n ≤ m) (k : nat) : n + k ≤ m + k
:= subst (subst (add_le_left H k) (add_comm k n)) (add_comm k m)

theorem add_le {n m k l : nat} (H1 : n ≤ k) (H2 : m ≤ l) : n + m ≤ k + l
:= le_trans (add_le_right H1 m) (add_le_left H2 k)

theorem add_le_left_inv {n m k : nat} (H : k + n ≤ k + m) : n ≤ m
:=
  obtain (l : nat) (Hl : k + n + l = k + m), from (le_elim H),
  le_intro (add_left_inj
    calc 
        k + (n + l)  = k + n + l : symm (add_assoc k n l)
          ... = k + m : Hl )

theorem add_le_right_inv {n m k : nat} (H : n + k ≤ m + k) : n ≤ m
:= add_le_left_inv (subst (subst H (add_comm n k)) (add_comm m k))

theorem succ_le {n m : nat} (H : n ≤ m) : succ n ≤ succ m
:= subst (subst (add_le_right H (succ zero)) (add_one n)) (add_one m)

theorem succ_le_inv {n m : nat} (H : succ n ≤ succ m) :  n ≤ m
:= add_le_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem self_le_succ {n : nat} : n ≤ succ n
:= le_intro (add_one n)

axiom mul_le_left {n m : nat} (H : n ≤ m) (k : nat) : k * n ≤ k * m
-- := 
--   obtain (l : nat) (Hl : n + l = m), from (le_elim H),
--   le_intro 
--     (calc 
--         k + n + l  = k + (n + l) : add_assoc k n l
--           ... = k + m : { Hl })

theorem mul_le_right {n m : nat} (H : n ≤ m) (k : nat) : n * k ≤ m * k
:= subst (subst (mul_le_left H k) (mul_comm k n)) (mul_comm k m)

theorem mul_le {n m k l : nat} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l
:= le_trans (mul_le_right H1 m) (mul_le_left H2 k)

axiom mul_le_left_inv {n m k : nat} (H : succ k * n ≤ succ k * m) : n ≤ m
-- :=
--   obtain (l : nat) (Hl : k + n + l = k + m), from (le_elim H),
--   le_intro (add_left_inj
--     calc 
--         k + (n + l)  = k + n + l : symm (add_assoc k n l)
--           ... = k + m : Hl )

theorem mul_le_right_inv {n m k : nat} (H : n * succ k ≤ m * succ k) : n ≤ m
:= mul_le_left_inv (subst (subst H (mul_comm n (succ k))) (mul_comm m (succ k)))


-------------------------------------------------- lt ge gt

definition ge (n m : nat) := m ≤ n
infix 50 >= : ge
infix 50 ≥  : ge

definition lt (n m : nat) := succ n ≤ m
infix 50 <  : lt

definition gt (n m : nat) := m < n
infix 50 >  : gt

theorem lt_intro {n m k : nat} (H : succ n + k = m) : n < m
:= le_intro H

theorem lt_elim {n m : nat} (H : n < m) : ∃ k, succ n + k = m
:= le_elim H

theorem lt_le_succ {n m : nat} (H : n < m) : succ n ≤ m
:= H

set_opaque lt true

theorem lt_ne {n m : nat} (H : n < m) : n ≠ m
:=
  not_intro 
    (assume H1 : n = m,
    obtain (k : nat) (Hk : succ n + k = m), from (lt_elim H),
    have H2 : n + zero = n + succ k, from 
      calc 
        n + zero = n : add_zero_right n
          ... = m : H1
          ... = succ n + k : symm Hk
          ... = n + succ k : add_move_succ n k,
      absurd (add_left_inj H2) (zero_ne_succ k))

theorem lt_irrefl (n : nat) : ¬ n < n
:= not_intro (assume H : n < n, absurd (refl n) (lt_ne H))

theorem lt_zero (n : nat) : ¬ n < zero
:= 
  not_intro 
    (assume H : n < zero,
    obtain (m : nat) (Hm : succ n + m = zero), from (lt_elim H),
    absurd
      (calc zero = succ n + m : symm Hm
        ...  =  succ (n + m) : add_succ_left n m)
      (zero_ne_succ (n + m)))

theorem lt_le {n m : nat} (H : n < m) : n ≤ m
:= 
  obtain (k : nat) (Hk : succ n + k = m), from (lt_elim H),
  le_intro 
    (calc 
      n + succ k =  succ (n + k) : add_succ_right n k
        ... = succ n + k : symm (add_succ_left n k)
        ... = m : Hk)

theorem le_lt_or {n m : nat} (H : n ≤ m) : n < m ∨ n = m
:=
  obtain (k : nat) (Hk : n + k = m), from (le_elim H),
  nat_discriminate
    (assume H3 : k = zero,
      have Heq : n = m,
        from calc
          n = n + zero : symm (add_zero_right n)
            ... = n + k : {symm H3}
            ... = m : Hk,
      or_intro_right _ Heq)
    (take l:nat, 
      assume H3 : k = succ l,
      have Hlt : n < m, from
        (lt_intro 
          (calc
            succ n + l = n + succ l : add_move_succ n l
              ... = n + k : {symm H3}
              ... = m : Hk)),
      or_intro_left _ Hlt)

theorem le_lt {n m : nat} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m
:=
  obtain (k : nat) (Hk : n + k = m), from (le_elim H1),
  nat_discriminate
    (assume H3 : k = zero,
    absurd_elim _
      (show n = m, from 
        calc
          n = n + zero : symm (add_zero_right n)
            ... = n + k : {symm H3}
            ... = m : Hk)
      H2)
    (take l:nat, assume H3 : k = succ l,
    lt_intro 
      (calc
        succ n + l = n + succ l : add_move_succ n l
          ... = n + k : {symm H3}
          ... = m : Hk))
  
theorem lt_le_trans {n m k : nat} (H1 : n < m) (H2 : m ≤ k) : n < k
:=
  obtain (l1 : nat) (Hl1 : succ n + l1 = m), from lt_elim H1,
  obtain (l2 : nat) (Hl2 : m + l2 = k), from le_elim H2,
  lt_intro 
    (calc 
      succ n + (l1 + l2) =  succ n + l1 + l2 : symm (add_assoc _ _ _)
        ... = m + l2 : { Hl1 }
        ... = k : Hl2)

theorem lt_trans {n m k : nat} (H1 : n < m) (H2 : m < k) : n < k
:= lt_le_trans H1 (lt_le H2)

theorem le_lt_trans {n m k : nat} (H1 : n ≤ m) (H2 : m < k) : n < k
:= 
  obtain (l1 : nat) (Hl1 : n + l1 = m), from le_elim H1,
  obtain (l2 : nat) (Hl2 : succ m + l2 = k), from lt_elim H2,
  lt_intro 
    (calc 
      succ n + (l1 + l2) = succ (n + (l1 + l2)) : add_succ_left _ _
        ... = succ (n + l1 + l2) : {symm (add_assoc _ _ _)}
        ... = succ (m + l2) : { Hl1 }
        ... = succ m + l2 : symm (add_succ_left m l2)
        ... = k : Hl2)

axiom trichotomy (n m : nat) : n < m ∨ n = m ∨ m < n

axiom le_or_lt (n m : nat) : n ≤ m ∨ m < n

theorem add_lt_left {n m : nat} (H : n < m) (k : nat) : k + n < k + m
:= 
  obtain (l : nat) (Hl : succ n + l = m), from (lt_elim H),
  lt_intro 
    (calc 
        succ (k + n) + l  = k + succ n + l : {symm (add_succ_right k n)}
          ... = k + (succ n + l) : add_assoc k (succ n) l
          ... = k + m : { Hl })

theorem add_lt_right {n m : nat} (H : n < m) (k : nat) : n + k < m + k
:= subst (subst (add_lt_left H k) (add_comm k n)) (add_comm k m)

theorem add_le_lt {n m k l : nat} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l
:= le_lt_trans (add_le_right H1 m) (add_lt_left H2 k)

theorem add_lt_le {n m k l : nat} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l
:= lt_le_trans (add_lt_right H1 m) (add_le_left H2 k)

theorem add_lt {n m k l : nat} (H1 : n < k) (H2 : m < l) : n + m < k + l
:= add_lt_le H1 (lt_le H2)

theorem add_lt_left_inv {n m k : nat} (H : k + n < k + m) : n < m
:=
  obtain (l : nat) (Hl : succ (k + n) + l = k + m), from (lt_elim H),
  lt_intro (add_left_inj
    calc 
        k + (succ n + l)  = k + succ n + l : symm (add_assoc k (succ n) l)
          ... = succ (k + n) + l : {add_succ_right k n}
          ... = k + m : Hl )

theorem add_lt_right_inv {n m k : nat} (H : n + k < m + k) : n < m
:= add_lt_left_inv (subst (subst H (add_comm n k)) (add_comm m k))

theorem succ_lt {n m : nat} (H : n < m) : succ n < succ m
:= subst (subst (add_lt_right H (succ zero)) (add_one n)) (add_one m)

theorem succ_lt_inv {n m : nat} (H : succ n < succ m) :  n < m
:= add_lt_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem self_lt_succ {n : nat} : n < succ n
:= lt_intro (add_zero_right (succ n))

theorem mul_lt_left {n m : nat} (H : n < m) (k : nat) : succ k * n < succ k * m
:= 
  induction_on k
    (subst (subst H (symm (mul_one_left n))) (symm (mul_one_left m)))
    (take (l:nat) (IH : succ l * n < succ l * m),
    have H2 : succ l * n + n < succ l * m + m, from add_lt IH H,
      subst (subst H2 (symm (mul_succ_left (succ l) n))) (symm (mul_succ_left (succ l) m)))

theorem mul_lt_right {n m : nat} (H : n < m) (k : nat) : n * succ k < m * succ k
:= subst (subst (mul_lt_left H k) (mul_comm (succ k) n)) (mul_comm (succ k) m)

axiom mul_lt {n m k l : nat} (H1 : n < k) (H2 : m < l) : n * m < k * l
--:= le_trans (mul_le_right H1 m) (mul_le_left H2 k)

axiom mul_lt_left_inv {n m k : nat} (H : k * n < k * m) : n < m
-- :=
--   obtain (l : nat) (Hl : k + n + l = k + m), from (le_elim H),
--   le_intro (add_left_inj
--     calc 
--         k + (n + l)  = k + n + l : symm (add_assoc k n l)
--           ... = k + m : Hl )

theorem mul_lt_right_inv {n m k : nat} (H : n * k < m * k) : n < m
:= mul_lt_left_inv (subst (subst H (mul_comm n k)) (mul_comm m k))


axiom ne_lt_succ {n m : nat} (H1 : n ≠ m) (H2 : n < succ m) : n < m
-- := obtain (w : nat) (Hw : n + 1 + w = m + 1), from (lt_elim H2),
--      let L : n + w = m := add_left_inj (calc n + w + 1  =  n + (w + 1)  : add_assoc _ _ _
--                                                 ... =  n + (1 + w)  : { add_comm _ _ }
--                                                 ... =  n + 1 + w    : symm (add_assoc _ _ _)
--                                                 ... =  m + 1        : Hw)
--      in nat_discriminate (λ Hz : w = 0, absurd_elim (n < m) (calc n   = n + 0  : symm (add_zero_right _)
--                                                               ... = n + w  : { symm Hz }
--                                                               ... = m      : L)
--                                                          H1)
--                      (λ (p : nat) (Hp : w = p + 1), lt_intro (calc n + 1 + p =  n + (1 + p)   : add_assoc _ _ _
--                                                                         ...  =  n + (p + 1)   : { add_comm _ _ }
--                                                                         ...  =  n + w         : { symm Hp }
--                                                                         ...  =  m             : L))

axiom strong_induction {P : nat → Bool} (H : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n
-- := take n,
--     let stronger : P n ∧ ∀ m, m < n → P m :=
--       -- we prove a stronger result by regular induction on n
--       induction_on n
--         (show P 0 ∧ ∀ m, m < 0 → P m, from
--             let c2 : ∀ m, m < 0 → P m := λ (m : nat) (Hlt : m < 0), absurd_elim (P m) Hlt (not_lt_0 m),
--                 c1 : P 0                := H 0 c2
--             in and_intro c1 c2)
--         (λ (n : nat) (iH : P n ∧ ∀ m, m < n → P m),
--             show P (n + 1) ∧ ∀ m, m < n + 1 → P m, from
--               let iH1 : P n                    := and_eliml iH,
--                   iH2 : ∀ m, m < n → P m     := and_elimr iH,
--                   c2  : ∀ m, m < n + 1 → P m := λ (m : nat) (Hlt : m < n + 1),
--                                                     or_elim (em (m = n))
--                                                       (λ Heq : m = n, subst iH1 (symm Heq))
--                                                       (λ Hne : m ≠ n, iH2 m (ne_lt_succ Hne Hlt)),
--                   c1  : P (n + 1)              := H (n + 1) c2
--               in and_intro c1 c2)
--     in and_eliml stronger


end --namespace nat