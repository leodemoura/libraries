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

theorem succ_ne_zero (n:nat) : succ n ≠ zero
:=
  not_intro
    (take H: succ n = zero,
      have H2 : true = false, from
        (let f : nat -> Bool := (nat_rec false (fun a b,true))
          in calc true = f (succ n) : symm (nat_rec_succ _ _ _)
            ... = f zero : {H}
	         ... = false : nat_rec_zero _ _),
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
      (show succ m = succ (pred (succ m)), from congr2 succ (symm (pred_succ m))))

theorem zero_or_succ2 (n:nat) : n = zero ∨ ∃k, n = succ k
:= or_imp_or (zero_or_succ n) (assume H, H) (assume H : n = succ (pred n), exists_intro (pred n) H)

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

theorem succ_ne_self (n:nat) : succ n ≠ n
:=
  not_intro (induction_on n
    (take H : succ zero = zero,
      have ne : succ zero ≠ zero, from succ_ne_zero zero,
      absurd H ne)
    (take k IH H, IH (succ_inj H)))

theorem decidable_equality (n m : nat) : n = m ∨ n ≠ m
:=
  have general : ∀n, n = m ∨ n ≠ m, from
    induction_on m
      (take n : nat,
        nat_discriminate
          (assume H : n = zero, or_intro_left _ H)
          (take l : nat,
            assume H : n = succ l,
            have H2 : n ≠ zero, from subst (succ_ne_zero l) (symm H),
            or_intro_right _ H2))
      (take k : nat,
        assume IH : ∀n, n = k ∨ n ≠ k,
        take n : nat,
        nat_discriminate
          (assume H : n = zero,
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

-------------------------------------------------- add

definition add (a b : nat) := nat_rec a (fun m x, succ x) b
infixl 65 +  : add

theorem add_zero_right (n:nat) : n + zero = n
:= nat_rec_zero _ _
theorem add_succ_right (n m:nat) : n + succ m = succ (n + m)
:= nat_rec_succ _ _ _

set_opaque add true

---------- comm, assoc

theorem add_zero_left (n:nat) : zero + n = n
:=
  induction_on n
    (add_zero_right zero)
    (take m IH, show zero + succ m = succ m, from
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

theorem add_comm_left (n m k : nat) : n + (m + k) = m + (n + k)
:= left_comm add_comm add_assoc n m k

theorem add_comm_right (n m k : nat) : n + m + k = n + k + m
:= right_comm add_comm add_assoc n m k

---------- inversion

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
  induction_on n
    (take (H : zero + m = zero), refl zero)
    (take k IH,
      assume (H : succ k + m = zero),
      absurd_elim (succ k = zero)
        (show succ (k + m) = zero, from
          calc
            succ (k + m) = succ k + m : symm (add_succ_left k m)
              ... = zero : H)
        (succ_ne_zero (k + m)))

theorem add_eq_zero_right {n m : nat} (H : n + m = zero) : m = zero
:= add_eq_zero_left (trans (add_comm m n) H)

theorem add_eq_zero {n m : nat} (H : n + m = zero) : n = zero ∧ m = zero
:= and_intro (add_eq_zero_left H) (add_eq_zero_right H)

---------- misc

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
--alias one : succ zero
--axiom false_induction {P : nat → Type} (x : P zero) (a : nat) : P a
--theorem foo {P : nat → Bool} (a : nat) (H : P one) : P (succ a)
--:= false_induction H a

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

---------- comm, distr, assoc, identity

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
          ... = n * l + n + m * l + m : {add_comm_right _ _ _}
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

theorem mul_comm_left (n m k : nat) : n * (m * k) = m * (n * k)
:= left_comm mul_comm mul_assoc n m k

theorem mul_comm_right (n m k : nat) : n * m * k = n * k * m
:= right_comm mul_comm mul_assoc n m k

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

---------- inversion

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
          absurd_elim _  (trans Heq H) (succ_ne_zero _)))

theorem mul_eq_succ_left {n m k : nat} (H : n * m = succ k) : exists l, n = succ l
:=
  nat_discriminate
    (assume H2 : n = zero,
      absurd_elim _
        (calc
          succ k = n * m : symm H
            ... = zero * m : {H2}
            ... = zero : mul_zero_left m)
        (succ_ne_zero k))
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
        resolve_right H3 (succ_ne_zero n))
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
              ... = succ n * m : {symm Hm}
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
        have H3 : zero = succ (succ (succ l2) * k + l2), from succ_inj H2,
        absurd_elim _ (symm H3) (succ_ne_zero _))

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

---------- partial order (totality is part of lt)

theorem le_intro2 (n m : nat) : n ≤ n + m
:= le_intro (refl (n + m))

theorem le_refl (n : nat) : n ≤ n
:= le_intro (add_zero_right n)

theorem le_zero (n : nat) : zero ≤ n
:= le_intro (add_zero_left n)

theorem le_zero_inv {n:nat} (H : n ≤ zero) : n = zero
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

---------- interaction with add

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

---------- interaction with succ

theorem succ_le {n m : nat} (H : n ≤ m) : succ n ≤ succ m
:= subst (subst (add_le_right H (succ zero)) (add_one n)) (add_one m)

theorem succ_le_inv {n m : nat} (H : succ n ≤ succ m) :  n ≤ m
:= add_le_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

theorem le_self_succ (n : nat) : n ≤ succ n
:= le_intro (add_one n)

theorem succ_le_right {n m : nat} (H : n ≤ m) : n ≤ succ m
:= le_trans H (le_self_succ m)

theorem succ_le_right_inv {n m : nat} (H : n ≤ succ m) : n ≤ m ∨ n = succ m
:=
  obtain (k : nat) (H2 : n + k = succ m), from (le_elim H),
  nat_discriminate
    (assume (Hk : k = zero),
      have H3 : n = succ m,
        from calc
          n = n + zero : symm (add_zero_right n)
            ... = n + k : {symm Hk}
            ... = succ m : H2,
      or_intro_right _ H3)
    (take (l : nat),
      assume (Hk : k = succ l),
      have H3 : succ (n + l) = succ m,
        from calc
          succ (n + l) = n + succ l : symm (add_succ_right n l)
            ... = n + k : {symm Hk}
            ... = succ m : H2,
      have H4 : n + l = m, from succ_inj H3,
      have H5 : n ≤ m, from le_intro H4,
      or_intro_left _ H5)

theorem succ_le_left_or {n m : nat} (H : n ≤ m) : succ n ≤ m ∨ n = m
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
      have Hlt : succ n ≤ m, from
        (le_intro
          (calc
            succ n + l = n + succ l : add_move_succ n l
              ... = n + k : {symm H3}
              ... = m : Hk)),
      or_intro_left _ Hlt)

theorem succ_le_left {n m : nat} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m
:= resolve_left (succ_le_left_or H1) H2

theorem succ_le_left_inv {n m : nat} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m
:=
  obtain (k : nat) (H2 : succ n + k = m), from (le_elim H),
  and_intro
    (have H3 : n + succ k = m,
      from calc
        n + succ k = succ n + k : symm (add_move_succ n k)
          ... = m : H2,
      show n ≤ m, from le_intro H3)
    (not_intro
      (assume H3 : n = m,
        have H4 : succ n ≤ n, from subst H (symm H3),
        have H5 : succ n = n, from le_antisym H4 (le_self_succ n),
        show false, from absurd H5 (succ_ne_self n)))

---------- interaction with mul

theorem mul_le_left {n m : nat} (H : n ≤ m) (k : nat) : k * n ≤ k * m
:=
  obtain (l : nat) (Hl : n + l = m), from (le_elim H),
  induction_on k
    (have H2 : zero * n = zero * m,
      from calc
        zero * n = zero : mul_zero_left n
          ... = zero * m : symm (mul_zero_left m),
      show zero * n ≤ zero * m, from subst (le_refl (zero * n)) H2)
    (take (l : nat),
      assume IH : l * n ≤ l * m,
      have H2 : l * n + n ≤ l * m + m, from add_le IH H,
      have H3 : succ l * n ≤ l * m + m, from subst H2 (symm (mul_succ_left l n)),
      show succ l * n ≤ succ l * m, from subst H3 (symm (mul_succ_left l m)))

theorem mul_le_right {n m : nat} (H : n ≤ m) (k : nat) : n * k ≤ m * k
:= subst (subst (mul_le_left H k) (mul_comm k n)) (mul_comm k m)

theorem mul_le {n m k l : nat} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l
:= le_trans (mul_le_right H1 m) (mul_le_left H2 k)

theorem mul_le_left_inv {n m k : nat} (H : succ n * m ≤ succ n * k) : m ≤ k
:=
  have general : ∀ k, succ n * m ≤ succ n * k → m ≤ k, from
    induction_on m
      (take k:nat,
        assume H2,
        show zero ≤ k, from le_zero k)
      (take l : nat,
        assume IH : ∀ k, succ n * l ≤ succ n * k → l ≤ k,
        take k : nat,
        assume H2 : succ n * succ l ≤ succ n * k,
        obtain (l2 : nat) (Hl2 : succ n * succ l + l2 = succ n * k), from (le_elim H2),
        have H3 : succ n * k = succ (succ n * l + n + l2),
          from calc
            succ n * k = succ n * succ l + l2 : symm Hl2
              ... = succ n * l + succ n + l2 : {mul_succ_right (succ n) l}
              ... = succ (succ n * l + n) + l2 : {add_succ_right _ _}
              ... = succ (succ n * l + n + l2) : add_succ_left _ _,
        obtain (l3 : nat) (Hl3 : k = succ l3), from mul_eq_succ_right H3,
        have H4 : succ n * l + l2 + succ n = succ n * l3 + succ n,
          from calc
            succ n * l + l2 + succ n = succ n * l + succ n + l2 : add_comm_right _ _ _
              ... = succ n * succ l + l2 : {symm (mul_succ_right (succ n) l)}
              ... = succ n * k : Hl2
              ... = succ n * succ l3 : {Hl3}
              ... = succ n * l3 + succ n : mul_succ_right (succ n) l3,
        have H5 : succ n * l + l2 = succ n * l3, from add_right_inj H4,
        have H6 : succ n * l ≤ succ n * l3, from le_intro H5,
        have H7 : l ≤ l3, from IH l3 H6,
        have H8 : succ l ≤ succ l3, from succ_le H7,
        show succ l ≤ k, from subst H8 (symm Hl3)),
  general k H

theorem mul_le_right_inv {n m k : nat} (H : n * succ m ≤ k * succ m) : n ≤ k
:= mul_le_left_inv (subst (subst H (mul_comm n (succ m))) (mul_comm k (succ m)))


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

theorem lt_zero (n : nat) : zero < succ n
:= succ_le (le_zero n)

theorem lt_zero_inv (n : nat) : ¬ n < zero
:=
  not_intro
    (assume H : n < zero,
      have H2 : succ n = zero, from le_zero_inv H,
      absurd H2 (succ_ne_zero n))

theorem lt_exists {n m : nat} (H : n < m) : exists k, m = succ k
:=
  nat_discriminate
    (take (Hm : m = zero), absurd_elim _ (subst H Hm) (lt_zero_inv n))
    (take (l : nat) (Hm : m = succ l), exists_intro l Hm)

---------- interaction with le

theorem lt_le_succ {n m : nat} (H : n < m) : succ n ≤ m
:= H

theorem le_succ_lt {n m : nat} (H : succ n ≤ m) : n < m
:= H

theorem lt_le {n m : nat} (H : n < m) : n ≤ m
:= and_elim_left (succ_le_left_inv H)

theorem le_lt_or {n m : nat} (H : n ≤ m) : n < m ∨ n = m
:= succ_le_left_or H

theorem le_lt {n m : nat} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m
:= resolve_left (le_lt_or H1) H2

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

theorem lt_antisym {n m : nat} (H1 : n < m) (H2 : m < n) : false
:= absurd (lt_trans H1 H2) (lt_irrefl n)

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

---------- interaction with succ

theorem succ_lt {n m : nat} (H : n < m) : succ n < succ m
:= subst (subst (add_lt_right H (succ zero)) (add_one n)) (add_one m)

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
            (assume H2 : l = zero,
              have H3 : m = k,
                from calc
                  m = k + l : symm Hl
                    ... = k + zero : {H2}
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

theorem trichotomy (n m : nat) : (n < m ∨ n = m) ∨ m < n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, le_lt_or H) (assume H : m < n, H)

theorem le_total (n m : nat) : n ≤ m ∨ m ≤ n
:= or_imp_or (le_or_lt n m) (assume H : n ≤ m, H) (assume H : m < n, lt_le H)


---------- interaction with mul

theorem mul_lt_left {n m : nat} (H : n < m) (k : nat) : succ k * n < succ k * m
:=
  lt_le_trans
    (show succ k * n < succ k * n + succ k, from lt_intro2 _ _)
    (show succ k * n + succ k ≤ succ k * m,
      from subst (mul_le_left H (succ k)) (mul_succ_right (succ k) n))

theorem mul_lt_right {n m : nat} (H : n < m) (k : nat) : n * succ k < m * succ k
:= subst (subst (mul_lt_left H k) (mul_comm (succ k) n)) (mul_comm (succ k) m)

theorem mul_le_lt {n m k l : nat} (H1 : n ≤ succ k) (H2 : m < l) : n * m < succ k * l
:= le_lt_trans (mul_le_right H1 m) (mul_lt_left H2 k)

theorem mul_lt_le {n m k l : nat} (H1 : n < k) (H2 : m ≤ succ l) : n * m < k * succ l
:= le_lt_trans (mul_le_left H2 n) (mul_lt_right H1 l)

theorem mul_lt {n m k l : nat} (H1 : n < k) (H2 : m < l) : n * m < k * l
:=
  obtain (k2 : nat) (Hk : k = succ k2), from lt_exists H1,
  have H3 : n * m ≤ k * m, from mul_le_right (lt_le H1) m,
  have H4 : k * m < k * l, from subst (mul_lt_left H2 k2) (symm Hk),
  le_lt_trans H3 H4

-- move mul_le_left_inv below this?
axiom mul_lt_left_inv {n m k : nat} (H : k * n < k * m) : n < m
-- :=
--   obtain (l : nat) (Hl : k + n + l = k + m), from (le_elim H),
--   le_intro (add_left_inj
--     calc
--         k + (n + l)  = k + n + l : symm (add_assoc k n l)
--           ... = k + m : Hl )

theorem mul_lt_right_inv {n m k : nat} (H : n * k < m * k) : n < m
:= mul_lt_left_inv (subst (subst H (mul_comm n k)) (mul_comm m k))

-- stronger : ∀m, m ≤ n → P n
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

set_opaque lt true

-------------------------------------------------- ge, gt

definition ge (n m : nat) := m ≤ n
infix 50 >= : ge
infix 50 ≥  : ge

definition gt (n m : nat) := m < n
infix 50 >  : gt


--------------------------------------------------

end --namespace nat