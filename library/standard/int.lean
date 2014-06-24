----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

-- Theory int
-- ==========

import nat quotient macros tactic

namespace int
using nat
using quot
using subtype
unary_nat

-- ## The defining equivalence relation on ℕ × ℕ

definition rel (a b : ℕ ## ℕ) : Bool := xx a + yy b = yy a + xx b

theorem rel_comp (n m k l : ℕ) : (rel (tpair n m) (tpair k l)) ↔ (n + l = m + k)
:=
  have H : (xx (tpair n m) + yy (tpair k l) = yy (tpair n m) + xx (tpair k l)) = (n + l = m + k),
    by simp, H

add_rewrite rel_comp --local

theorem rel_refl (a : ℕ ## ℕ) : rel a a
:= add_comm (xx a) (yy a)

theorem rel_symm {a b : ℕ ## ℕ} (H : rel a b) : rel b a
:=
  calc
    xx b + yy a = yy a + xx b : add_comm _ _
      ... = xx a + yy b : symm H
      ... = yy b + xx a : add_comm _ _

theorem rel_trans {a b c : ℕ ## ℕ} (H1 : rel a b) (H2 : rel b c) : rel a c
:=
  have H3 : xx a + yy c + yy b = yy a + xx c + yy b, from
    calc
     xx a + yy c + yy b = xx a + yy b + yy c : by simp
      ... = yy a + xx b + yy c : {H1}
      ... = yy a + (xx b + yy c) : by simp
      ... = yy a + (yy b + xx c) : {H2}
      ... = yy a + xx c + yy b : by simp,
  show xx a + yy c = yy a + xx c, from add_cancel_right H3

theorem rel_equiv : equivalence rel
:= equivalence_intro rel_refl @rel_symm @rel_trans

theorem rel_flip {a b : ℕ ## ℕ} (H : rel a b) : rel (flip a) (flip b)
:=
  calc
    xx (flip a) + yy (flip b) = yy a + xx b : by simp
      ... = xx a + yy b : symm H
      ... = yy (flip a) + xx (flip b) : by simp

-- ## The canonical representative of each equivalence class

definition proj (a : ℕ ## ℕ) : ℕ ## ℕ
:= if xx a ≥ yy a then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a)

theorem proj_ge {a : ℕ ## ℕ} (H : xx a ≥ yy a) : proj a = tpair (xx a - yy a) 0
:= imp_if_eq H _ _

theorem proj_lt {a : ℕ ## ℕ} (H : xx a < yy a) : proj a = tpair 0 (yy a - xx a)
:=
  have H2 : ¬ xx a ≥ yy a, from lt_imp_not_ge H,
  not_imp_if_eq H2 _ _

theorem proj_le {a : ℕ ## ℕ} (H : xx a ≤ yy a) : proj a = tpair 0 (yy a - xx a)
:=
  or_elim (le_or_gt (yy a) (xx a))
    (assume H2 : yy a ≤ xx a,
      have H3 : xx a = yy a, from le_antisym H H2,
      calc
        proj a = tpair (xx a - yy a) 0 : proj_ge H2
          ... = tpair (xx a - yy a) (xx a - xx a) : {symm (sub_self (xx a))}
          ... = tpair (yy a - yy a) (yy a - xx a) : {H3}
          ... = tpair 0 (yy a - xx a) : {sub_self (yy a)})
    (assume H2 : xx a < yy a, proj_lt H2)

theorem proj_ge_xx {a : ℕ ## ℕ} (H : xx a ≥ yy a) : xx (proj a) = xx a - yy a
:=
  calc
    xx (proj a) = xx (tpair (xx a - yy a) 0) : {proj_ge H}
      ... = xx a - yy a : tproj1_tpair (xx a - yy a) 0

theorem proj_ge_yy {a : ℕ ## ℕ} (H : xx a ≥ yy a) : yy (proj a) = 0
:=
  calc
    yy (proj a) = yy (tpair (xx a - yy a) 0) : {proj_ge H}
      ... = 0 : tproj2_tpair (xx a - yy a) 0

theorem proj_le_xx {a : ℕ ## ℕ} (H : xx a ≤ yy a) : xx (proj a) = 0
:=
  calc
    xx (proj a) = xx (tpair 0 (yy a - xx a)) : {proj_le H}
      ... = 0 : tproj1_tpair 0 (yy a - xx a)

theorem proj_le_yy {a : ℕ ## ℕ} (H : xx a ≤ yy a) : yy (proj a) = yy a - xx a
:=
  calc
    yy (proj a) = yy (tpair 0 (yy a - xx a)) : {proj_le H}
      ... = yy a - xx a : tproj2_tpair 0 (yy a - xx a)

theorem proj_flip (a : ℕ ## ℕ) : proj (flip a) = flip (proj a)
:=
  have special : ∀a, yy a ≤ xx a → proj (flip a) = flip (proj a), from
    take a,
    assume H : yy a ≤ xx a,
    have H2 : xx (flip a) ≤ yy (flip a), from P_flip H,
    have H3 : xx (proj (flip a)) = xx (flip (proj a)), from
      calc
        xx (proj (flip a)) = 0 : proj_le_xx H2
          ... = yy (proj a) : symm (proj_ge_yy H)
          ... = xx (flip (proj a)) : symm (flip_xx (proj a)),
    have H4 : yy (proj (flip a)) = yy (flip (proj a)), from
      calc
        yy (proj (flip a)) = yy (flip a) - xx (flip a) : proj_le_yy H2
          ... = xx a - xx (flip a) : {flip_yy a}
          ... = xx a - yy a : {flip_xx a}
          ... = xx (proj a) : symm (proj_ge_xx H)
          ... = yy (flip (proj a)) : symm (flip_yy (proj a)),
    tpairext H3 H4,
  or_elim (le_total (yy a) (xx a))
    (assume H : yy a ≤ xx a, special a H)
    (assume H : xx a ≤ yy a,
      have H2 : yy (flip a) ≤ xx (flip a), from P_flip H,
      calc
        proj (flip a) = flip (flip (proj (flip a))) : symm (flip_flip (proj (flip a)))
          ... = flip (proj (flip (flip a))) : {symm (special (flip a) H2)}
          ... = flip (proj a) : {flip_flip a})

theorem proj_rel (a : ℕ ## ℕ) : rel a (proj a)
:=
  or_elim (le_total (yy a) (xx a))
    (assume H : yy a ≤ xx a,
      calc
        xx a + yy (proj a) = xx a + 0 : {proj_ge_yy H}
          ... = xx a : add_zero_right (xx a)
          ... = yy a + (xx a - yy a) : symm (add_sub_le H)
          ... = yy a + xx (proj a) : {symm (proj_ge_xx H)})
    (assume H : xx a ≤ yy a,
      calc
        xx a + yy (proj a) = xx a + (yy a - xx a) : {proj_le_yy H}
          ... = yy a : add_sub_le H
          ... = yy a + 0 : symm (add_zero_right (yy a))
          ... = yy a + xx (proj a) : {symm (proj_le_xx H)})

theorem proj_congr {a b : ℕ ## ℕ} (H : rel a b) : proj a = proj b
:=
  have special : ∀a b, yy a ≤ xx a → rel a b → proj a = proj b, from
    take a b,
    assume H2 : yy a ≤ xx a,
    assume H : rel a b,
    have H3 : xx a + yy b ≤ yy a + xx b, from subst (le_refl (xx a + yy b)) H,
    have H4 : yy b ≤ xx b, from add_le_inv H3 H2,
    have H5 : xx (proj a) = xx (proj b), from
      calc
        xx (proj a) = xx a - yy a : proj_ge_xx H2
          ... = xx a + yy b - yy b - yy a : {symm (sub_add_left (xx a) (yy b))}
          ... = yy a + xx b - yy b - yy a : {H}
          ... = yy a + xx b - yy a - yy b : {sub_comm _ _ _}
          ... = xx b - yy b : {sub_add_left2 (yy a) (xx b)}
          ... = xx (proj b) : symm (proj_ge_xx H4),
    have H6 : yy (proj a) = yy (proj b), from
      calc
        yy (proj a) = 0 : proj_ge_yy H2
          ... = yy (proj b) : {symm (proj_ge_yy H4)},
    tpairext H5 H6,
  or_elim (le_total (yy a) (xx a))
    (assume H2 : yy a ≤ xx a, special a b H2 H)
    (assume H2 : xx a ≤ yy a,
      have H3 : yy (flip a) ≤ xx (flip a), from P_flip H2,
      have H4 : proj (flip a) = proj (flip b), from special (flip a) (flip b) H3 (rel_flip H),
      have H5 : flip (proj a) = flip (proj b), from subst (subst H4 (proj_flip a)) (proj_flip b),
      show proj a = proj b, from flip_inj H5)

theorem proj_inj {a b : ℕ ## ℕ} (H : proj a = proj b) : rel a b
:= representative_map_equiv_inj rel_equiv proj_rel @proj_congr H

theorem proj_zero_or (a : ℕ ## ℕ) : xx (proj a) = 0 ∨ yy (proj a) = 0
:=
  or_elim (le_total (yy a) (xx a))
    (assume H : yy a ≤ xx a, or_intro_right _ (proj_ge_yy H))
    (assume H : xx a ≤ yy a, or_intro_left _ (proj_le_xx H))

theorem proj_idempotent (a : ℕ ## ℕ) : proj (proj a) = proj a
:= representative_map_idempotent_equiv rel proj_rel @proj_congr a

-- ## Definition of ℤ and basic theorems and definitions

definition int := image proj
alias ℤ : int

definition psub : ℕ ## ℕ → ℤ := fun_image proj
definition rep : ℤ → ℕ ## ℕ := subtype::rep

theorem quotient : is_quotient rel psub rep
:= representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

theorem psub_rep (a : ℤ) : psub (rep a) = a
:= abs_rep quotient a

theorem destruct (a : ℤ) : ∃n m : ℕ, a = psub (tpair n m)
:=
  exists_intro (xx (rep a))
    (exists_intro (yy (rep a))
      (calc
        a = psub (rep a) : symm (psub_rep a)
      ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}))

definition of_nat (n : ℕ) : ℤ := psub (tpair n 0)
coercion of_nat

theorem eq_zero_intro (n : ℕ) : psub (tpair n n) = 0
:=
  have H : rel (tpair n n) (tpair 0 0), by simp,
  eq_abs quotient H

-- ## absolute value

definition abs : ℤ → ℕ := rec_constant quotient (fun v, dist (xx v) (yy v))

notation | _ | : abs

---move to other library or remove
add_rewrite tpair_tproj_eq
theorem tpair_translate {A B : Type} (P : A → B → A ## B → Bool)
    : (∀v, P (tproj1 v) (tproj2 v) v) ↔ (∀a b, P a b (tpair a b))
:=
  iff_intro
    (assume H, take a b, subst (H (tpair a b)) (by simp))
    (assume H, take v, subst (H (tproj1 v) (tproj2 v)) (by simp))

theorem abs_comp (n m : ℕ) : |psub (tpair n m)| = dist n m
:=
  have H : ∀v w : ℕ ## ℕ, rel v w → dist (xx v) (yy v) = dist (xx w) (yy w),
    from take v w H, dist_eq_intro H,
  have H2 : ∀v : ℕ ## ℕ, |psub v| = dist (xx v) (yy v),
    from take v, (comp_constant quotient H (rel_refl v)),
  (by simp) ◂ H2 (tpair n m)

add_rewrite abs_comp --local

  --the following theorem includes abs_zero
theorem abs_of_nat (n : ℕ) : |n| = n
:=
  calc
    |psub (tpair n 0)| = dist n 0 : by simp
      ... = n : by simp

theorem of_nat_inj {n m : ℕ} (H : of_nat n = of_nat m) : n = m
:=
  calc
    n = |n| : symm (abs_of_nat n)
  ... = |m| : {H}
  ... = m : abs_of_nat m

theorem abs_eq_zero {a : ℤ} (H : |a| = 0) : a = 0
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  have H2 : dist xa ya = 0, from
    calc
      dist xa ya = |psub (tpair xa ya)| : by simp_no_assump
        ... = |a| : {symm Ha}
        ... = 0 : H,
  have H3 : xa = ya, from dist_eq_zero H2,
  calc
    a = psub (tpair xa ya) : Ha
  ... = psub (tpair ya ya) : {H3}
  ... = 0 : eq_zero_intro ya

add_rewrite abs_of_nat

-- ## neg

definition neg : ℤ → ℤ := quotient_map quotient flip
notation 80 - _ : neg

theorem neg_comp (n m : ℕ) : -psub (tpair n m) = psub (tpair m n)
:=
  have H : ∀a, -psub a = psub (flip a),
    from take a, comp_quotient_map quotient @rel_flip (rel_refl _),
  calc
    -psub (tpair n m) = psub (flip (tpair n m)) : H (tpair n m)
      ... = psub (tpair m n) : by simp

add_rewrite neg_comp --local

---note: "-0" is interpreted as invalid numeral
theorem neg_zero : - 0 = 0
:= calc -psub (tpair 0 0) = psub (tpair 0 0) : neg_comp 0 0

theorem neg_neg (a : ℤ) : -(-a) = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  by simp

add_rewrite neg_neg neg_zero

theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b
:= (by simp_no_assump) ◂ congr2 neg H

theorem neg_move {a b : ℤ} (H : -a = b) : -b = a
:= subst (neg_neg a) H

theorem abs_neg (a : ℤ) : | -a| = |a|
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  by simp

theorem pos_eq_neg {n m : ℕ} (H : n = -m) : n = 0 ∧ m = 0
:=
  have H2 : ∀n : ℕ, n = psub (tpair n 0), from take n : ℕ, refl n,
  have H3 : psub (tpair n 0) = psub (tpair 0 m), from (by simp) ◂ H,
  have H4 : rel (tpair n 0) (tpair 0 m), from R_intro_refl quotient rel_refl H3,
  have H5 : n + m = 0, from
    calc
      n + m = xx (tpair n 0) + yy (tpair 0 m) : by simp
        ... = yy (tpair n 0) + xx (tpair 0 m) : H4
        ... = 0 : by simp,
   add_eq_zero H5

add_rewrite abs_neg

---reverse equalities
theorem cases (a : ℤ) : (∃n : ℕ, a = n) ∨ (∃n : ℕ, a = -n)
:=
  have Hrep : proj (rep a) = rep a, from @idempotent_image_fix _ proj proj_idempotent a,
  or_imp_or (or_flip (proj_zero_or (rep a)))
    (assume H : yy (proj (rep a)) = 0,
      have H2 : yy (rep a) = 0, from subst H Hrep,
      exists_intro (xx (rep a))
        (calc
          a = psub (rep a) : symm (psub_rep a)
            ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = psub (tpair (xx (rep a)) 0) : {H2}
            ... = of_nat (xx (rep a)) : refl _))
    (assume H : xx (proj (rep a)) = 0,
      have H2 : xx (rep a) = 0, from subst H Hrep,
      exists_intro (yy (rep a))
        (calc
          a = psub (rep a) : symm (psub_rep a)
            ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = psub (tpair 0 (yy (rep a))) : {H2}
            ... = -psub (tpair (yy (rep a)) 0) : by simp
            ... = -of_nat (yy (rep a)) : refl _))

---rename to by_cases in Lean 0.2 (for now using this to avoid name clash)
theorem int_by_cases {P : ℤ → Bool} (a : ℤ) (H1 : ∀n : ℕ, P n) (H2 : ∀n : ℕ, P (-n)) : P a
:=
  or_elim (cases a)
    (assume H, obtain (n : ℕ) (H3 : a = n), from H, subst (H1 n) (symm H3))
    (assume H, obtain (n : ℕ) (H3 : a = -n), from H, subst (H2 n) (symm H3))

---reverse equalities, rename
theorem cases_succ (a : ℤ) : (∃n : ℕ, a = n) ∨ (∃n : ℕ, a = -succ n)
:=
  or_elim (cases a)
    (assume H : (∃n : ℕ, a = n), or_intro_left _ H)
    (assume H,
      obtain (n : ℕ) (H2 : a = -n), from H,
      discriminate
        (assume H3 : n = 0,
          have H4 : a = 0, from
            calc
              a = -n : H2
            ... = - 0 : {H3}
            ... = 0 : neg_zero,
          or_intro_left _ (exists_intro 0 H4))
        (take k : ℕ,
          assume H3 : n = succ k,
          have H4 : a = -succ k, from subst H2 H3,
          or_intro_right _ (exists_intro k H4)))

theorem int_by_cases_succ {P : ℤ → Bool} (a : ℤ) (H1 : ∀n : ℕ, P n) (H2 : ∀n : ℕ, P (-succ n)) : P a
:=
  or_elim (cases_succ a)
    (assume H, obtain (n : ℕ) (H3 : a = n), from H, subst (H1 n) (symm H3))
    (assume H, obtain (n : ℕ) (H3 : a = -succ n), from H, subst (H2 n) (symm H3))

theorem of_nat_eq_neg_of_nat {n m : ℕ} (H : n = - m) : n = 0 ∧ m = 0
:=
  have H2 : n = psub (tpair 0 m), from
    calc
      n = -m : H
        ... = -psub (tpair m 0) : refl (-m)
        ... = psub (tpair 0 m) : by simp,
  have H3 : rel (tpair n 0) (tpair 0 m), from R_intro_refl quotient rel_refl H2,
  have H4 : n + m = 0, from
    calc
      n + m = xx (tpair n 0) + yy (tpair 0 m) : by simp
        ... = yy (tpair n 0) + xx (tpair 0 m) : H3
        ... = 0 : by simp,
  add_eq_zero H4

--some of these had to be transparent for theorem cases
set_opaque int true
set_opaque psub true
set_opaque proj true

-- ## add

theorem rel_add {a a' b b' : ℕ ## ℕ} (Ha : rel a a') (Hb : rel b b')
    : rel (map_pair2 add a b) (map_pair2 add a' b')
:=
  calc
    xx (map_pair2 add a b) + yy (map_pair2 add a' b')  = xx a + yy a' + (xx b + yy b') : by simp
      ... = yy a + xx a' + (xx b + yy b') : {Ha}
      ... = yy a + xx a' + (yy b + xx b') : {Hb}
      ... = yy (map_pair2 add a b) + xx (map_pair2 add a' b') : by simp

definition add : ℤ → ℤ → ℤ := quotient_map_binary quotient (map_pair2 nat::add)
infixl 65 + : add

theorem add_comp (n m k l : ℕ) : psub (tpair n m) + psub (tpair k l) = psub (tpair (n + k) (m + l))
:=
  have H : ∀a b, psub a + psub b = psub (map_pair2 nat::add a b),
    from comp_quotient_map_binary_refl rel_refl quotient @rel_add,
  trans (H (tpair n m) (tpair k l)) (by simp)

add_rewrite add_comp --local

theorem add_comm (a b : ℤ) : a + b = b + a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  by simp

theorem add_assoc (a b c : ℤ) : a + b + c = a + (b + c)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from destruct c,
  by simp

theorem add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c)
:= left_comm add_comm add_assoc a b c

theorem add_right_comm (a b c : ℤ) : a + b + c = a + c + b
:= right_comm add_comm add_assoc a b c

-- ### interaction of add with other functions and constants

theorem add_zero_right (a : ℤ) : a + 0 = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  have H0 : 0 = psub (tpair 0 0), from refl 0,
  by simp

theorem add_zero_left (a : ℤ) : 0 + a = a
:= subst (add_zero_right a) (add_comm a 0)

theorem add_inverse_right (a : ℤ) : a + -a = 0
:=
 have H : ∀n, psub (tpair n n) = 0, from eq_zero_intro,
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  by simp

theorem add_inverse_left (a : ℤ) : -a + a = 0
:= subst (add_inverse_right a) (add_comm a (-a))

theorem neg_add_distr (a b : ℤ) : -(a + b) = -a + -b
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  by simp

theorem triangle_inequality (a b : ℤ) : |a + b| ≤ |a| + |b| --note: ≤ is nat::≤
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  have H : dist (xa + xb) (ya + yb) ≤ dist xa ya + dist xb yb,
    from dist_add_le_add_dist xa xb ya yb,
  by simp

theorem add_of_nat (n m : ℕ) : of_nat n + of_nat m = n + m -- this is of_nat (n + m)
:=
  have H : ∀n : ℕ, n = psub (tpair n 0), from take n : ℕ, refl n,
  by simp

add_rewrite add_of_nat

theorem of_nat_succ (n : ℕ) : of_nat (succ n) = of_nat n + 1
:= by simp

-- ## sub
definition sub (a b : ℤ) : ℤ := a + -b
infixl 65 - : sub

theorem sub_def (a b : ℤ) : a - b = a + -b
:= refl (a - b)

theorem add_neg_right (a b : ℤ) : a + -b = a - b
:= refl (a - b)

theorem add_neg_left (a b : ℤ) : -a + b = b - a
:= add_comm (-a) b

theorem sub_neg_right (a b : ℤ) : a - (-b) = a + b
:= subst (refl (a - (-b))) (neg_neg b)

theorem sub_neg_neg (a b : ℤ) : -a - (-b) = b - a
:= subst (add_comm (-a) (-(-b))) (neg_neg b)

theorem sub_self (a : ℤ) : a - a = 0
:= add_inverse_right a

theorem sub_zero_right (a : ℤ) : a - 0 = a
:= substp (fun x, a + x = a) (add_zero_right a) (symm neg_zero)
---this doesn't work without explicit P

theorem sub_zero_left (a : ℤ) : 0 - a = -a
:= add_zero_left (-a)

theorem neg_sub  (a b : ℤ) : -(a - b) = -a + b
:=
  calc
    -(a - b) = -a + -(-b) : neg_add_distr a (-b)
      ... = -a + b : {neg_neg b}

theorem neg_sub_flip (a b : ℤ) : -(a - b) = b - a
:=
  calc
    -(a - b) = -a + b : neg_sub a b
      ... = b - a : add_comm (-a) b

theorem sub_sub_assoc (a b c : ℤ) : a - b - c = a - (b + c)
:=
  calc
    a - b - c = a + (-b + -c) : add_assoc a (-b) (-c)
      ... = a + -(b + c) : {symm (neg_add_distr b c)}

theorem sub_add_assoc (a b c : ℤ) : a - b + c = a - (b - c)
:=
  calc
    a - b + c = a + (-b + c) : add_assoc a (-b) c
      ... = a + -(b - c) : {symm (neg_sub b c)}

theorem add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c)
:= add_assoc a b (-c)

theorem add_sub_inverse (a b : ℤ) : a + b - b = a
:=
  calc
    a + b - b = a + (b - b) : add_assoc a b (-b)
      ... = a + 0 : {sub_self b}
      ... = a : add_zero_right a

theorem add_sub_inverse2 (a b : ℤ) : a + b - a = b
:= subst (add_sub_inverse b a) (add_comm b a)

theorem sub_add_inverse (a b : ℤ) : a - b + b = a
:= subst (add_sub_inverse a b) (add_right_comm a b (-b))

add_rewrite add_zero_left add_zero_right
add_rewrite add_comm add_assoc add_left_comm
add_rewrite sub_def add_inverse_right add_inverse_left
add_rewrite neg_add_distr
--add_rewrite sub_sub_assoc sub_add_assoc add_sub_assoc
--add_rewrite add_neg_right add_neg_left
--add_rewrite sub_self

-- ### inversion theorems for add and sub

-- a + a = 0 -> a = 0
-- a = -a -> a = 0

theorem add_cancel_right {a b c : ℤ} (H : a + c = b + c) : a = b
:=
  calc
    a = a + c - c : symm (add_sub_inverse a c)
  ... = b + c - c : {H}
  ... = b : add_sub_inverse b c

theorem add_cancel_left {a b c : ℤ} (H : a + b = a + c) : b = c
:= add_cancel_right (subst (subst H (add_comm a b)) (add_comm a c))

theorem add_eq_zero_right {a b : ℤ} (H : a + b = 0) : -a = b
:=
  have H2 : a + -a = a + b, from subst (symm H) (symm (add_inverse_right a)),
  show -a = b, from add_cancel_left H2

theorem add_eq_zero_left {a b : ℤ} (H : a + b = 0) : -b = a
:= neg_move (add_eq_zero_right H)

theorem add_eq_self {a b : ℤ} (H : a + b = a) : b = 0
:= add_cancel_left (trans H (symm (add_zero_right a)))

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c
:= neg_inj (add_cancel_left H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c
:= add_cancel_right H

theorem sub_eq_zero {a b : ℤ} (H : a - b = 0) : a = b
:= neg_inj (add_eq_zero_right H)

theorem add_imp_sub_right {a b c : ℤ} (H : a + b = c) : c - b = a
:=
  have H2 : c - b + b = a + b, from trans (sub_add_inverse c b) (symm H),
  add_cancel_right H2

theorem add_imp_sub_left {a b c : ℤ} (H : a + b = c) : c - a = b
:= add_imp_sub_right (subst H (add_comm a b))

theorem sub_imp_add {a b c : ℤ} (H : a - b = c) : c + b = a
:= subst (add_imp_sub_right H) (neg_neg b)

theorem sub_imp_sub {a b c : ℤ} (H : a - b = c) : a - c = b
:= have H2 : c + b = a, from sub_imp_add H, add_imp_sub_left H2

theorem sub_add_add_right (a b c : ℤ) : a + c - (b + c) = a - b
:=
  calc
    a + c - (b + c) = a + (c - (b + c)) : add_sub_assoc a c (b + c)
      ... = a + (c - b - c) : {symm (sub_sub_assoc c b c)}
      ... = a + -b : {add_sub_inverse2 c (-b)}

theorem sub_add_add_left (a b c : ℤ) : c + a - (c + b) = a - b
:= subst (subst (sub_add_add_right a b c) (add_comm a c)) (add_comm b c)

theorem dist_def (n m : ℕ) : dist n m = |of_nat n - m|
:=
  have H : of_nat n - m = psub (tpair n m), from
    calc
      psub (tpair n 0) + -psub (tpair m 0) = psub (tpair (n + 0) (0 + m)) : by simp
        ... = psub (tpair n m) : by simp,
  calc
    dist n m = |psub (tpair n m)| : by simp
      ... = |of_nat n - m| : {symm H}

-- ## mul

theorem rel_mul_prep {xa ya xb yb xn yn xm ym : ℕ} (H1 : xa + yb = ya + xb) (H2 : xn + ym = yn + xm)
  : xa * xn + ya * yn + (xb * ym + yb * xm) = xa * yn + ya * xn + (xb * xm + yb * ym)
:=
 have H3 : xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
         = xa * yn + ya * xn + (xb * xm + yb * ym) + (yb * xn + xb * yn + (xb * xn + yb * yn)), from
    calc
      xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
    = xa * xn + yb * xn + (ya * yn + xb * yn) + (xb * xn + xb * ym + (yb * yn + yb * xm)) : by simp
... = (xa + yb) * xn + (ya + xb) * yn + (xb * (xn + ym) + yb * (yn + xm)) : by simp_no_assump
... = (ya + xb) * xn + (xa + yb) * yn + (xb * (yn + xm) + yb * (xn + ym)) : by simp
... = ya * xn + xb * xn + (xa * yn + yb * yn) + (xb * yn + xb * xm + (yb*xn + yb*ym))
        : by simp_no_assump
... = xa * yn + ya * xn + (xb * xm + yb * ym) + (yb * xn + xb * yn + (xb * xn + yb * yn)) : by simp,
  nat::add_cancel_right H3

theorem rel_mul {u u' v v' : ℕ ## ℕ} (H1 : rel u u') (H2 : rel v v')
    : rel (tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v))
          (tpair (xx u' * xx v' + yy u' * yy v') (xx u' * yy v' + yy u' * xx v'))
:=
  calc
      xx (tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v))
    + yy (tpair (xx u' * xx v' + yy u' * yy v') (xx u' * yy v' + yy u' * xx v'))
    = (xx u * xx v + yy u * yy v) + (xx u' * yy v' + yy u' * xx v') : by simp
... = (xx u * yy v + yy u * xx v) + (xx u' * xx v' + yy u' * yy v') : rel_mul_prep H1 H2
... = yy (tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v))
    + xx (tpair (xx u' * xx v' + yy u' * yy v') (xx u' * yy v' + yy u' * xx v')) : by simp

definition mul : ℤ → ℤ → ℤ := quotient_map_binary quotient
    (fun u v : ℕ ## ℕ, tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v))
infixl 70 *  : mul

theorem mul_comp (n m k l : ℕ)
    : psub (tpair n m) * psub (tpair k l) = psub (tpair (n * k + m * l) (n * l + m * k))
:=
  have H : ∀u v,
      psub u * psub v = psub (tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v)),
    from comp_quotient_map_binary_refl rel_refl quotient @rel_mul,
  trans (H (tpair n m) (tpair k l)) (by simp)

add_rewrite mul_comp

theorem mul_comm (a b : ℤ) : a * b = b * a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  by simp

theorem mul_assoc (a b c : ℤ) : (a * b) * c = a * (b * c)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from destruct c,
  by simp

theorem mul_left_comm : ∀a b c : ℤ, a * (b * c) = b * (a * c)
:= left_comm mul_comm mul_assoc

theorem mul_right_comm : ∀a b c : ℤ, a * b * c = a * c * b
:= right_comm mul_comm mul_assoc

-- ### interaction with other objects

theorem mul_zero_right (a : ℤ) : a * 0 = 0
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  have H0 : 0 = psub (tpair 0 0), from refl 0,
  by simp

theorem mul_zero_left (a : ℤ) : 0 * a = 0
:= subst (mul_zero_right a) (mul_comm a 0)

theorem mul_one_right (a : ℤ) : a * 1 = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  have H1 : 1 = psub (tpair 1 0), from refl 1,
  by simp

theorem mul_one_left (a : ℤ) : 1 * a = a
:= subst (mul_one_right a) (mul_comm a 1)

theorem mul_neg_right (a b : ℤ) : a * -b = -(a * b)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  by simp

theorem mul_neg_left (a b : ℤ) : -a * b = -(a * b)
:= subst (subst (mul_neg_right b a) (mul_comm b (-a))) (mul_comm b a)

add_rewrite mul_neg_right mul_neg_left

theorem mul_neg_neg (a b : ℤ) : -a * -b = a * b
:= by simp

theorem mul_distr_right (a b c : ℤ) : (a + b) * c = a * c + b * c
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from destruct c,
  by simp

theorem mul_distr_left (a b c : ℤ) : a * (b + c) = a * b + a * c
:=
  calc
    a * (b + c) = (b + c) * a : mul_comm a (b + c)
      ... = b * a + c * a : mul_distr_right b c a
      ... = a * b + c * a : {mul_comm b a}
      ... = a * b + a * c : {mul_comm c a}

theorem mul_sub_distr_right (a b c : ℤ) : (a - b) * c = a * c - b * c
:=
  calc
    (a + -b) * c = a * c + -b * c : mul_distr_right a (-b) c
      ... = a * c + - (b * c) : {mul_neg_left b c}

theorem mul_sub_distr_left (a b c : ℤ) : a * (b - c) = a * b - a * c
:=
  calc
    a * (b + -c) = a * b + a * -c : mul_distr_left a b (-c)
      ... = a * b + - (a * c) : {mul_neg_right a c}

theorem mul_of_nat (n m : ℕ) : of_nat n * of_nat m = n * m
:=
  have H : ∀n : ℕ, n = psub (tpair n 0), from take n : ℕ, refl n,
  by simp

theorem mul_abs (a b : ℤ) : |a * b| = |a| * |b|
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from destruct b,
  have H : dist xa ya * dist xb yb = dist (xa * xb + ya * yb) (xa * yb + ya * xb),
    from dist_mul_dist xa ya xb yb,
  by simp

add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
add_rewrite mul_comm mul_assoc mul_left_comm
add_rewrite mul_distr_right mul_distr_left mul_of_nat
--mul_sub_distr_left mul_sub_distr_right

-- ---------- inversion

theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0
:=
  have H2 : |a| * |b| = 0, from
    calc
      |a| * |b| = |a * b| : symm (mul_abs a b)
        ... = |0| : {H}
        ... = 0 : abs_of_nat 0,
  have H3 : |a| = 0 ∨ |b| = 0, from mul_eq_zero H2,
  or_imp_or H3
    (assume H : |a| = 0, abs_eq_zero H)
    (assume H : |b| = 0, abs_eq_zero H)

theorem mul_cancel_left_or {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c
:=
  have H2 : a * (b - c) = 0, by simp,
  have H3 : a = 0 ∨ b - c = 0, from mul_eq_zero H2,
  or_imp_or_right H3 (assume H4 : b - c = 0, sub_eq_zero H4)

theorem mul_cancel_left {a b c : ℤ} (H1 : a ≠ 0) (H2 : a * b = a * c) : b = c
:= resolve_right (mul_cancel_left_or H2) H1

theorem mul_cancel_right_or {a b c : ℤ} (H : b * a = c * a) : a = 0 ∨ b = c
:= mul_cancel_left_or (subst (subst H (mul_comm b a)) (mul_comm c a))

theorem mul_cancel_right {a b c : ℤ} (H1 : c ≠ 0) (H2 : a * c = b * c) : a = b
:= resolve_right (mul_cancel_right_or H2) H1

theorem mul_ne_zero {a b : ℤ} (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0
:=
  not_intro
    (assume H : a * b = 0,
      or_elim (mul_eq_zero H)
        (assume H2 : a = 0, absurd H2 Ha)
        (assume H2 : b = 0, absurd H2 Hb))

theorem mul_ne_zero_left {a b : ℤ} (H : a * b ≠ 0) : a ≠ 0
:=
  not_intro
    (assume H2 : a = 0,
      have H3 : a * b = 0, by simp,
      absurd H3 H)

theorem mul_ne_zero_right {a b : ℤ} (H : a * b ≠ 0) : b ≠ 0
:= mul_ne_zero_left (subst H (mul_comm a b))

-- ## le
definition le (a b : ℤ) : Bool := ∃n : ℕ, a + n = b
infix  50 <= : le
infix  50 ≤  : le

-- definition le : ℤ → ℤ → Bool := rec_binary quotient (fun a b, xx a + yy b ≤ yy a + xx b)
-- theorem le_comp_alt (u v : ℕ ## ℕ) : (psub u ≤ psub v) ↔ (xx u + yy v ≤ yy u + xx v)
-- :=
--   comp_binary_refl quotient rel_refl
--   (take u u' v v' : ℕ ## ℕ,
--     assume Hu : rel u u',
--     assume Hv : rel v v',)

--   u v

-- theorem le_intro {a b : ℤ} {n : ℕ} (H : a + of_nat n = b) : a ≤ b
-- :=
--   have lemma : ∀u v, rel (map_pair2 nat::add u (tpair n 0)) v → xx u + yy v + n = yy u + xx v, from
--     take u v,
--     assume H : rel (map_pair2 nat::add u (tpair n 0)) v,
--     calc
--       xx u + yy v + n = xx u + n + yy v : nat::add_right_comm (xx u) (yy v) n
--         ... = xx (map_pair2 nat::add u (tpair n 0)) + yy v : by simp
--         ... = yy (map_pair2 nat::add u (tpair n 0)) + xx v : H
--         ... = yy u + 0 + xx v : by simp
--         ... = yy u + xx v : {nat::add_zero_right (yy u)},
--   have H2 :

theorem le_intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b
:= exists_intro n H

theorem le_elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b
:= H

-- ### partial order

theorem le_refl (a : ℤ) : a ≤ a
:= le_intro (add_zero_right a)

theorem le_of_nat (n m : ℕ) : (of_nat n ≤ of_nat m) ↔ (n ≤ m)
:=
  iff_intro
    (assume H : of_nat n ≤ of_nat m,
      obtain (k : ℕ) (Hk : of_nat n + of_nat k = of_nat m), from le_elim H,
      have H2 : n + k = m, from of_nat_inj (trans (symm (add_of_nat n k)) Hk),
      nat::le_intro H2)
    (assume H : n ≤ m,
      obtain (k : ℕ) (Hk : n + k = m), from nat::le_elim H,
      have H2 : of_nat n + of_nat k = of_nat m, from subst (add_of_nat n k) Hk,
      le_intro H2)

theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = c), from le_elim H2,
  have H3 : a + (n + m) = c, from
    calc
      a + (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = c : Hm,
  le_intro H3

theorem le_antisym {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = a), from le_elim H2,
  have H3 : a + (n + m) = a + 0, from
    calc
      a + (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = a : Hm
        ... = a + 0 : symm (add_zero_right a),
  have H4 : of_nat (n + m) = of_nat 0, from add_cancel_left H3,
  have H5 : n + m = 0, from of_nat_inj H4,
  have H6 : n = 0, from nat::add_eq_zero_left H5,
  show a = b, from
    calc
      a = a + of_nat 0 : symm (add_zero_right a)
        ... = a + n : {symm H6}
        ... = b : Hn

-- ### interaction with add

theorem le_add_of_nat_right (a : ℤ) (n : ℕ) : a ≤ a + n
:= le_intro (refl (a + n))

theorem le_add_of_nat_left (a : ℤ) (n : ℕ) : a ≤ n + a
:= le_intro (add_comm a n)

theorem add_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
  have H2 : c + a + n = c + b, from
    calc
      c + a + n = c + (a + n) : add_assoc c a n
        ... = c + b : {Hn},
  le_intro H2

theorem add_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a + c ≤ b + c
:= subst (subst (add_le_left H c) (add_comm c a)) (add_comm c b)

theorem add_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : c ≤ d) : a + c ≤ b + d
:= le_trans (add_le_right H1 c) (add_le_left H2 b)

theorem add_le_cancel_right {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b
:=
  have H2 : a + c - c ≤ b + c - c, from add_le_right H (-c),
  subst (subst H2 (add_sub_inverse a c)) (add_sub_inverse b c)

theorem add_le_cancel_left {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b
:= add_le_cancel_right (subst (subst H (add_comm c a)) (add_comm c b))

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d
:=
  obtain (n : ℕ) (Hn : c + n = a), from le_elim H2,
  have H3 : c + (n + b) ≤ c + d, from subst (subst H1 (symm Hn)) (add_assoc c n b),
  have H4 : n + b ≤ d, from add_le_cancel_left H3,
  show b ≤ d, from le_trans (le_add_of_nat_left b n) H4

theorem le_add_of_nat_right_trans {a b : ℤ} (H : a ≤ b) (n : ℕ) : a ≤ b + n
:= le_trans H (le_add_of_nat_right b n)

theorem le_imp_succ_le_or_eq {a b : ℤ} (H : a ≤ b) : a + 1 ≤ b ∨ a = b
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
  discriminate
    (assume H2 : n = 0,
      have H3 : a = b, from
        calc
          a = a + 0 : symm (add_zero_right a)
            ... = a + n : {symm H2}
            ... = b : Hn,
      or_intro_right _ H3)
    (take k : ℕ,
      assume H2 : n = succ k,
      have H3 : a + 1 + k = b, from
        calc
          a + 1 + k = a + succ k : by simp
            ... = a + n : by simp
            ... = b : Hn,
      or_intro_left _ (le_intro H3))

-- ### interaction with neg and sub

theorem le_neg {a b : ℤ} (H : a ≤ b) : -b ≤ -a
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
  have H2 : b - n = a, from add_imp_sub_right Hn,
  have H3 : -b + n = -a, from
    calc
      -b + n = -b + -(-n) : {symm (neg_neg n)}
        ... = -(b - n) : symm (neg_add_distr b (-n))
        ... = -a : {H2},
  le_intro H3

theorem neg_le_zero {a : ℤ} (H : 0 ≤ a) : -a ≤ 0
:= subst (le_neg H) neg_zero

theorem zero_le_neg {a : ℤ} (H : a ≤ 0) : 0 ≤ -a
:= subst (le_neg H) neg_zero

theorem le_neg_inv {a b : ℤ} (H : -a ≤ -b) : b ≤ a
:= subst (subst (le_neg H) (neg_neg a)) (neg_neg b)

theorem le_sub_of_nat (a : ℤ) (n : ℕ) : a - n ≤ a
:= le_intro (sub_add_inverse a n)

theorem sub_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a - c ≤ b - c
:= add_le_right H (-c)

theorem sub_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c - b ≤ c - a
:= add_le_left (le_neg H) c

theorem sub_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : d ≤ c) : a - c ≤ b - d
:= add_le H1 (le_neg H2)

theorem sub_le_right_inv {a b c : ℤ} (H : a - c ≤ b - c) : a ≤ b
:= add_le_cancel_right H

theorem sub_le_left_inv {a b c : ℤ} (H : c - a ≤ c - b) : b ≤ a
:= le_neg_inv (add_le_cancel_left H)

-- Less than, Greater than, Greater than or equal
-- ----------------------------------------------

definition lt (a b : ℤ) := a + 1 ≤ b
infix 50 <  : lt

definition ge (a b : ℤ) := b ≤ a
infix 50 >= : ge
infix 50 ≥  : ge

definition gt (a b : ℤ) := b < a
infix 50 >  : gt

theorem lt_def (a b : ℤ) : a < b ↔ a + 1 ≤ b
:= refl (a < b)

theorem gt_def (n m : ℕ) : n > m ↔ m < n
:= refl (n > m)

theorem ge_def (n m : ℕ) : n ≥ m ↔ m ≤ n
:= refl (n ≥ m)

add_rewrite gt_def ge_def --it might be possible to remove this in Lean 0.2

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n
:= le_intro (show a + 1 + n = a + succ n, by simp)

theorem lt_intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b
:= subst (lt_add_succ a n) H

theorem lt_elim {a b : ℤ} (H : a < b) : ∃n : ℕ, a + succ n = b
:=
  obtain (n : ℕ) (Hn : a + 1 + n = b), from le_elim H,
  have H2 : a + succ n = b, from
    calc
      a + succ n = a + 1 + n : by simp_no_assump
        ... = b : Hn,
  exists_intro n H2

-- -- ### basic facts

theorem lt_irrefl (a : ℤ) : ¬ a < a
:=
  not_intro
    (assume H : a < a,
      obtain (n : ℕ) (Hn : a + succ n = a), from lt_elim H,
      have H2 : a + succ n = a + 0, from
        calc
          a + succ n = a : Hn
            ... = a + 0 : by simp,
      have H3 : succ n = 0, from add_cancel_left H2,
      have H4 : succ n = 0, from of_nat_inj H3,
      absurd H4 (succ_ne_zero n))

theorem lt_imp_ne {a b : ℤ} (H : a < b) : a ≠ b
:= not_intro (assume H2 : a = b, absurd (subst H H2) (lt_irrefl b))

theorem lt_of_nat (n m : ℕ) : (of_nat n < of_nat m) ↔ (n < m)
:=
  calc
    (of_nat n + 1 ≤ of_nat m) = (of_nat (succ n) ≤ of_nat m) : by simp
      ... = (succ n ≤ m) : le_of_nat (succ n) m
      ... = (n < m) : symm (nat::lt_def n m)

theorem gt_of_nat (n m : ℕ) : (of_nat n > of_nat m) ↔ (n > m)
:= lt_of_nat m n

-- ### interaction with le

theorem lt_imp_le_succ {a b : ℤ} (H : a < b) : a + 1 ≤ b
:= H

theorem le_succ_imp_lt {a b : ℤ} (H : a + 1 ≤ b) : a < b
:= H

theorem self_lt_succ (a : ℤ) : a < a + 1
:= le_refl (a + 1)

theorem lt_imp_le {a b : ℤ} (H : a < b) : a ≤ b
:=
  obtain (n : ℕ) (Hn : a + succ n = b), from lt_elim H,
  le_intro Hn

theorem le_imp_lt_or_eq {a b : ℤ} (H : a ≤ b) : a < b ∨ a = b
:= le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {a b : ℤ} (H1 : a ≤ b)  (H2 : a ≠ b) : a < b
:= resolve_left (le_imp_lt_or_eq H1) H2

theorem le_imp_lt_succ {a b : ℤ} (H : a ≤ b) : a < b + 1
:= add_le_right H 1

theorem lt_succ_imp_le {a b : ℤ} (H : a < b + 1) : a ≤ b
:= add_le_cancel_right H


-- ### transitivity, antisymmmetry

theorem lt_le_trans {a b c : ℤ} (H1 : a < b) (H2 : b ≤ c) : a < c
:= le_trans H1 H2

theorem le_lt_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b < c) : a < c
:= le_trans (add_le_right H1 1) H2

theorem lt_trans {a b c : ℤ} (H1 : a < b) (H2 : b < c) : a < c
:= lt_le_trans H1 (lt_imp_le H2)

theorem le_imp_not_gt {a b : ℤ} (H : a ≤ b) : ¬ a > b
:= not_intro (assume H2 : a > b, absurd (le_lt_trans H H2) (lt_irrefl a))

theorem lt_imp_not_ge {a b : ℤ} (H : a < b) : ¬ a ≥ b
:= not_intro (assume H2 : a ≥ b, absurd (lt_le_trans H H2) (lt_irrefl a))

theorem lt_antisym {a b : ℤ} (H : a < b) : ¬ b < a
:= le_imp_not_gt (lt_imp_le H)

-- ### interaction with addition

theorem add_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b
:= substp (fun x, x ≤ c + b) (add_le_left H c) (symm (add_assoc c a 1))

theorem add_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a + c < b + c
:= subst (subst (add_lt_left H c) (add_comm c a)) (add_comm c b)

theorem add_le_lt {a b c d : ℤ} (H1 : a ≤ c) (H2 : b < d) : a + b < c + d
:= le_lt_trans (add_le_right H1 b) (add_lt_left H2 c)

theorem add_lt_le {a b c d : ℤ} (H1 : a < c) (H2 : b ≤ d) : a + b < c + d
:= lt_le_trans (add_lt_right H1 b) (add_le_left H2 c)

theorem add_lt {a b c d : ℤ} (H1 : a < c) (H2 : b < d) : a + b < c + d
:= add_lt_le H1 (lt_imp_le H2)

theorem add_lt_cancel_left {a b c : ℤ} (H : c + a < c + b) : a < b
:= add_le_cancel_left (subst H (add_assoc c a 1))

theorem add_lt_cancel_right {a b c : ℤ} (H : a + c < b + c) : a < b
:= add_lt_cancel_left (subst (subst H (add_comm a c)) (add_comm b c))


-- ### interaction with neg and sub

theorem lt_neg {a b : ℤ} (H : a < b) : -b < -a
:=
  have H2 : -(a + 1) + 1 = -a, by simp,
  have H3 : -b ≤ -(a + 1), from le_neg H,
  have H4 : -b + 1 ≤ -(a + 1) + 1, from add_le_right H3 1,
  subst H4 H2

theorem neg_lt_zero {a : ℤ} (H : 0 < a) : -a < 0
:= subst (lt_neg H) neg_zero

theorem zero_lt_neg {a : ℤ} (H : a < 0) : 0 < -a
:= subst (lt_neg H) neg_zero

theorem lt_neg_inv {a b : ℤ} (H : -a < -b) : b < a
:= subst (subst (lt_neg H) (neg_neg a)) (neg_neg b)

theorem lt_sub_of_nat_succ (a : ℤ) (n : ℕ) : a - succ n < a
:= lt_intro (sub_add_inverse a (succ n))

theorem sub_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a - c < b - c
:= add_lt_right H (-c)

theorem sub_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c - b < c - a
:= add_lt_left (lt_neg H) c

theorem sub_lt {a b c d : ℤ} (H1 : a < b) (H2 : d < c) : a - c < b - d
:= add_lt H1 (lt_neg H2)

theorem sub_lt_right_inv {a b c : ℤ} (H : a - c < b - c) : a < b
:= add_lt_cancel_right H

theorem sub_lt_left_inv {a b c : ℤ} (H : c - a < c - b) : b < a
:= lt_neg_inv (add_lt_cancel_left H)

-- ### totality of lt and le

add_rewrite succ_pos zero_le --move some of these to nat.lean
add_rewrite le_of_nat lt_of_nat gt_of_nat --remove gt_of_nat in Lean 0.2
add_rewrite le_neg lt_neg neg_le_zero zero_le_neg zero_lt_neg neg_lt_zero

axiom sorry {P : Bool} : P

theorem neg_le_pos (n m : ℕ) : -n ≤ m
:=
  have H1 : of_nat 0 ≤ of_nat m, by simp,
  have H2 : -n ≤ 0, by simp,
  le_trans H2 H1

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b
:=
  int_by_cases a
    (take n : ℕ,
      int_by_cases_succ b
        (take m : ℕ,
          show of_nat n ≤ m ∨ of_nat n > m, from (by simp) ◂ (le_or_gt n m))
        (take m : ℕ,
          show n ≤ -succ m ∨ n > -succ m, from
            have H0 : -succ m < -m, from lt_neg (subst (self_lt_succ m) (symm (of_nat_succ m))),
            have H : -succ m < n, from lt_le_trans H0 (neg_le_pos m n),
            or_intro_right _ H))
    (take n : ℕ,
      int_by_cases_succ b
        (take m : ℕ,
          show -n ≤ m ∨ -n > m, from
            or_intro_left _ (neg_le_pos n m))
        (take m : ℕ,
          show -n ≤ -succ m ∨ -n > -succ m, from
            or_imp_or (le_or_gt (succ m) n)
              (assume H : succ m ≤ n,
                le_neg (symm (le_of_nat (succ m) n) ◂ H))
              (assume H : succ m > n,
                lt_neg (symm (lt_of_nat n (succ m)) ◂ H))))

theorem trichotomy_alt (a b : ℤ) : (a < b ∨ a = b) ∨ a > b
:= or_imp_or_left (le_or_gt a b) (assume H : a ≤ b, le_imp_lt_or_eq H)

theorem trichotomy (a b : ℤ) : a < b ∨ a = b ∨ a > b
:= iff_elim_left (or_assoc _ _ _) (trichotomy_alt a b)

theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a
:= or_imp_or_right (le_or_gt a b) (assume H : b < a, lt_imp_le H)

theorem not_lt_imp_le {a b : ℤ} (H : ¬ a < b) : b ≤ a
:= resolve_left (le_or_gt b a) H

theorem not_le_imp_lt {a b : ℤ} (H : ¬ a ≤ b) : b < a
:= resolve_right (le_or_gt a b) H

-- (non)positivity and (non)negativity
-- -------------------------------------

-- ### basic

-- see also "int_by_cases" and similar theorems

theorem pos_imp_exists_nat {a : ℤ} (H : a ≥ 0) : ∃n : ℕ, a = n
:=
  obtain (n : ℕ) (Hn : of_nat 0 + n = a), from le_elim H,
  exists_intro n (trans (symm Hn) (add_zero_left n))

theorem neg_imp_exists_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n
:=
  have H2 : -a ≥ 0, from zero_le_neg H,
  obtain (n : ℕ) (Hn : -a = n), from pos_imp_exists_nat H2,
  have H3 : a = -n, from symm (neg_move Hn),
  exists_intro n H3

theorem abs_pos {a : ℤ} (H : a ≥ 0) : |a| = a
:=
  obtain (n : ℕ) (Hn : a = n), from pos_imp_exists_nat H,
  subst (congr2 of_nat (abs_of_nat n)) (symm Hn)

--abs_neg is already taken... rename?
theorem abs_negative {a : ℤ} (H : a ≤ 0) : |a| = -a
:=
  obtain (n : ℕ) (Hn : a = -n), from neg_imp_exists_nat H,
  calc
    |a| = | -n| : {Hn}
    ... = |n| : {abs_neg n}
    ... = n : {abs_of_nat n}
    ... = -a : symm (neg_move (symm Hn))

theorem abs_cases (a : ℤ) : a = |a| ∨ a = - |a|
:=
  or_imp_or (le_total 0 a)
    (assume H : a ≥ 0, symm (abs_pos H))
    (assume H : a ≤ 0, symm (neg_move (symm (abs_negative H))))

-- ### interaction of mul with le and lt

theorem mul_le_left_nonneg {a b c : ℤ} (Ha : a ≥ 0) (H : b ≤ c) : a * b ≤ a * c
:=
  obtain (n : ℕ) (Hn : b + n = c), from le_elim H,
  have H2 : a * b + |a| * n = a * c, from
    calc
      a * b + |a| * n = a * b + |a| * of_nat n : by simp
        ... = a * b + a * n : {abs_pos Ha}
        ... = a * (b + n) : by simp_no_assump
        ... = a * c : by simp,
  le_intro H2

theorem mul_le_right_nonneg {a b c : ℤ} (Hb : b ≥ 0) (H : a ≤ c) : a * b ≤ c * b
:= subst (subst (mul_le_left_nonneg Hb H) (mul_comm b a)) (mul_comm b c)

theorem mul_le_left_nonpos {a b c : ℤ} (Ha : a ≤ 0) (H : b ≤ c) : a * c ≤ a * b
:=
  have H2 : -a * b ≤ -a * c, from mul_le_left_nonneg (zero_le_neg Ha) H,
  have H3 : -(a * b) ≤ -(a * c), from subst (subst H2 (mul_neg_left a b)) (mul_neg_left a c),
  le_neg_inv H3

theorem mul_le_right_nonpos {a b c : ℤ} (Hb : b ≤ 0) (H : c ≤ a) : a * b ≤ c * b
:= subst (subst (mul_le_left_nonpos Hb H) (mul_comm b a)) (mul_comm b c)

---this theorem can be made more general by replacing either Ha with 0 ≤ a or Hb with 0 ≤ d...
theorem mul_le_nonneg {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b ≤ d)
    : a * b ≤ c * d
:= le_trans (mul_le_right_nonneg Hb Hc) (mul_le_left_nonneg (le_trans Ha Hc) Hd)

theorem mul_le_nonpos {a b c d : ℤ} (Ha : a ≤ 0) (Hb : b ≤ 0) (Hc : c ≤ a) (Hd : d ≤ b)
    : a * b ≤ c * d
:= le_trans (mul_le_right_nonpos Hb Hc) (mul_le_left_nonpos (le_trans Hc Ha) Hd)

theorem mul_lt_left_pos {a b c : ℤ} (Ha : a > 0) (H : b < c) : a * b < a * c
:=
  have H2 : a * b < a * b + a, from subst (add_lt_left Ha (a * b)) (add_zero_right (a * b)),
  have H3 : a * b + a ≤ a * c, from subst (mul_le_left_nonneg (lt_imp_le Ha) H) (by simp),
  lt_le_trans H2 H3

theorem mul_lt_right_pos {a b c : ℤ} (Hb : b > 0) (H : a < c) : a * b < c * b
:= subst (subst (mul_lt_left_pos Hb H) (mul_comm b a)) (mul_comm b c)

theorem mul_lt_left_neg {a b c : ℤ} (Ha : a < 0) (H : b < c) : a * c < a * b
:=
  have H2 : -a * b < -a * c, from mul_lt_left_pos (zero_lt_neg Ha) H,
  have H3 : -(a * b) < -(a * c), from subst (subst H2 (mul_neg_left a b)) (mul_neg_left a c),
  lt_neg_inv H3

theorem mul_lt_right_neg {a b c : ℤ} (Hb : b < 0) (H : c < a) : a * b < c * b
:= subst (subst (mul_lt_left_neg Hb H) (mul_comm b a)) (mul_comm b c)

theorem mul_le_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b < d)
    : a * b < c * d
:= le_lt_trans (mul_le_right_nonneg Hb Hc) (mul_lt_left_pos (lt_le_trans Ha Hc) Hd)

theorem mul_lt_le_pos {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b > 0) (Hc : a < c) (Hd : b ≤ d)
    : a * b < c * d
:= lt_le_trans (mul_lt_right_pos Hb Hc) (mul_le_left_nonneg (le_trans Ha (lt_imp_le Hc)) Hd)

theorem mul_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b > 0) (Hc : a < c) (Hd : b < d)
    : a * b < c * d
:= mul_lt_le_pos (lt_imp_le Ha) Hb Hc (lt_imp_le Hd)

theorem mul_lt_neg {a b c d : ℤ} (Ha : a < 0) (Hb : b < 0) (Hc : c < a) (Hd : d < b)
    : a * b < c * d
:= lt_trans (mul_lt_right_neg Hb Hc) (mul_lt_left_neg (lt_trans Hc Ha) Hd)

-- theorem mul_le_lt_neg and mul_lt_le_neg?

theorem mul_lt_cancel_left_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : c * a < c * b) : a < b
:=
  or_elim (le_or_gt b a)
    (assume H2 : b ≤ a,
      have H3 : c * b ≤ c * a, from mul_le_left_nonneg Hc H2,
      absurd_elim _ H3 (lt_imp_not_ge H))
    (assume H2 : a < b, H2)

theorem mul_lt_cancel_right_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : a * c < b * c) : a < b
:= mul_lt_cancel_left_nonneg Hc (subst (subst H (mul_comm a c)) (mul_comm b c))

theorem mul_lt_cancel_left_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : c * b < c * a) : a < b
:=
  have H2 : -(c * a) < -(c * b), from lt_neg H,
  have H3 : -c * a < -c * b,
    from subst (subst H2 (symm (mul_neg_left c a))) (symm (mul_neg_left c b)),
  have H4 : -c ≥ 0, from zero_le_neg Hc,
  mul_lt_cancel_left_nonneg H4 H3

theorem mul_lt_cancel_right_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : b * c < a * c) : a < b
:= mul_lt_cancel_left_nonpos Hc (subst (subst H (mul_comm a c)) (mul_comm b c))

theorem mul_le_cancel_left_pos {a b c : ℤ} (Hc : c > 0) (H : c * a ≤ c * b) : a ≤ b
:=
  or_elim (le_or_gt a b)
    (assume H2 : a ≤ b, H2)
    (assume H2 : a > b,
      have H3 : c * a > c * b, from mul_lt_left_pos Hc H2,
      absurd_elim _ H3 (le_imp_not_gt H))

theorem mul_le_cancel_right_pos {a b c : ℤ} (Hc : c > 0) (H : a * c ≤ b * c) : a ≤ b
:= mul_le_cancel_left_pos Hc (subst (subst H (mul_comm a c)) (mul_comm b c))

theorem mul_le_cancel_left_neg {a b c : ℤ} (Hc : c < 0) (H : c * b ≤ c * a) : a ≤ b
:=
  have H2 : -(c * a) ≤ -(c * b), from le_neg H,
  have H3 : -c * a ≤ -c * b,
    from subst (subst H2 (symm (mul_neg_left c a))) (symm (mul_neg_left c b)),
  have H4 : -c > 0, from zero_lt_neg Hc,
  mul_le_cancel_left_pos H4 H3

theorem mul_le_cancel_right_neg {a b c : ℤ} (Hc : c < 0) (H : b * c ≤ a * c) : a ≤ b
:= mul_le_cancel_left_neg Hc (subst (subst H (mul_comm a c)) (mul_comm b c))

theorem mul_eq_one_left {a b : ℤ} (H : a * b = 1) : a = 1 ∨ a = - 1
:=
  have H2 : |a| * |b| = 1, from
    calc
      |a| * |b| = |a * b| : symm (mul_abs a b)
        ... = |1| : {H}
        ... = 1 : abs_of_nat 1,
  have H3 : |a| = 1, from mul_eq_one_left H2,
  or_imp_or (abs_cases a)
    (assume H4 : a = |a|, subst H4 H3)
    (assume H4 : a = - |a|, subst H4 H3)

theorem mul_eq_one_right {a b : ℤ} (H : a * b = 1) : b = 1 ∨ b = - 1
:= mul_eq_one_left (subst H (mul_comm a b))

-- sign function
-- -------------

definition sign (a : ℤ) : ℤ := if a > 0 then 1 else (if a < 0 then - 1 else 0)

--for kernel
theorem or_elim3 {a b c d : Bool} (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d
:= or_elim H Ha (assume H2,or_elim H2 Hb Hc)

theorem sign_pos {a : ℤ} (H : a > 0) : sign a = 1
:= imp_if_eq H _ _

theorem sign_negative {a : ℤ} (H : a < 0) : sign a = - 1
:= trans (not_imp_if_eq (lt_antisym H) _ _) (imp_if_eq H  _ _)

theorem sign_zero : sign 0 = 0
:= trans (not_imp_if_eq (lt_irrefl 0) _ _) (not_imp_if_eq (lt_irrefl 0)  _ _)

add_rewrite sign_negative sign_pos abs_negative abs_pos sign_zero mul_abs

theorem mul_sign_abs (a : ℤ) : sign a * |a| = a
:=
  have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
  have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
  or_elim3 (trichotomy a 0)
    (assume H : a < 0, by simp)
    (assume H : a = 0, by simp)
    (assume H : a > 0, by simp)

theorem sign_mul (a b : ℤ) : sign (a * b) = sign a * sign b
:=
  by_cases
    (assume Ha : a = 0, by simp)
    (assume Ha : a ≠ 0,
      by_cases
        (assume Hb : b = 0, by simp)
        (assume Hb : b ≠ 0,
          have H : sign (a * b) * |a * b| = sign a * sign b  * |a * b|, from
            calc
              sign (a * b) * |a * b| = a * b : mul_sign_abs (a * b)
                ... = sign a * |a| * b : {symm (mul_sign_abs a)}
                ... = sign a * |a| * (sign b * |b|) : {symm (mul_sign_abs b)}
                ... = sign a * sign b  * |a * b| : by simp,
          have H2 : |a * b| ≠ 0, from contrapos (@abs_eq_zero (a * b)) (mul_ne_zero Ha Hb),
          have H3 : |a * b| ≠ of_nat 0, from contrapos of_nat_inj H2,
          mul_cancel_right H3 H))

--set_option pp::coercion true

theorem sign_idempotent (a : ℤ) : sign (sign a) = sign a
:=
  have temp : of_nat 1 > 0, from symm (lt_of_nat 0 1) ◂ (succ_pos 0),--this should be done with simp
  or_elim3 (trichotomy a 0)
    (by simp)
    (by simp)
    (by simp)

theorem sign_succ (n : ℕ) : sign (succ n) = 1
:= sign_pos (symm (lt_of_nat 0 (succ n)) ◂ succ_pos n) --this should be done with simp

theorem sign_neg (a : ℤ) : sign (-a) = - sign a
:=
  have temp1 : a > 0 → -a < 0, from neg_lt_zero,
  have temp2 : a < 0 → -a > 0, from zero_lt_neg,
  or_elim3 (trichotomy a 0)
    (by simp)
    (by simp)
    (by simp)

add_rewrite sign_neg

theorem abs_sign_ne_zero {a : ℤ} (H : a ≠ 0) : |sign a| = 1
:=
  or_elim3 (trichotomy a 0)
    (by simp)
    (assume H2 : a = 0, absurd_elim _ H2 H)
    (by simp)

theorem sign_abs (a : ℤ) : sign (abs a) = abs (sign a)
:=
  have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
  have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
  or_elim3 (trichotomy a 0)
    (by simp)
    (by simp)
    (by simp)

set_opaque rel true
set_opaque rep true
set_opaque of_nat true
set_opaque abs true
set_opaque neg true
set_opaque add true
set_opaque mul true
set_opaque le true
set_opaque lt true
set_opaque sign true
--transparent: sub ge gt

end -- namespace int
