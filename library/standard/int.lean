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

theorem rel_comp2 (n m k l : ℕ) : (rel (tpair n m) (tpair k l)) ↔ (n + l = m + k)
:=
  have H : (xx (tpair n m) + yy (tpair k l) = yy (tpair n m) + xx (tpair k l)) = (n + l = m + k),
    by simp, H

add_rewrite rel_comp2 --local

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
:=
  calc
    proj a = if true then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a) : {eqt_intro H}
      ... = tpair (xx a - yy a) 0 : by simp

theorem proj_lt {a : ℕ ## ℕ} (H : xx a < yy a) : proj a = tpair 0 (yy a - xx a)
:=
  have H2 : ¬ xx a ≥ yy a, from lt_imp_not_le H,
  calc
    proj a = if false then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a) : {eqf_intro H2}
      ... = tpair 0 (yy a - xx a) : by simp

theorem proj_le {a : ℕ ## ℕ} (H : xx a ≤ yy a) : proj a = tpair 0 (yy a - xx a)
:=
  or_elim (le_or_lt (yy a) (xx a))
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

definition int := image proj --should this be defined outside the namespace?
alias ℤ : int

definition psub : ℕ ## ℕ → ℤ := fun_image proj
definition rep : ℤ → ℕ ## ℕ := subtype::rep

theorem quotient : is_quotient rel psub rep
:= representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

theorem psub_rep (a : ℤ) : psub (rep a) = a
:= abs_rep quotient a

definition to_int (n : ℕ) : ℤ := psub (tpair n 0)
coercion to_int

-- ### absolute value

definition abs : ℤ → ℕ := rec_constant quotient (fun v, dist (xx v) (yy v))

notation 90 | _ | : abs
---what level should be used? without level, superfluous parentheses are added to compilation output


--move to other library or remove
add_rewrite tpair_tproj_eq
theorem tpair_translate {A B : Type} (P : A → B → A ## B → Bool)
    : (∀v, P (tproj1 v) (tproj2 v) v) ↔ (∀a b, P a b (tpair a b))
:=
  iff_intro
    (assume H, take a b, subst (H (tpair a b)) (by simp))
    (assume H, take v, subst (H (tproj1 v) (tproj2 v)) (by simp))

theorem abs_comp (v : ℕ ## ℕ) : |psub v| = dist (xx v) (yy v)
:=
  comp_constant quotient
    (take v w : ℕ ## ℕ,
      assume H : rel v w,
      show dist (xx v) (yy v) = dist (xx w) (yy w), from dist_eq H)
    (rel_refl v)

theorem abs_comp2 (n m : ℕ) : |psub (tpair n m)| = dist n m
:= subst (abs_comp (tpair n m)) (by simp)

add_rewrite abs_comp2 --local

theorem abs_to_int (n : ℕ) : |n| = n
:=
  calc
    |psub (tpair n 0)| = dist n 0 : abs_comp2 n 0
      ... = n : dist_zero_right n

theorem to_int_inj {n m : ℕ} (H : to_int n = to_int m) : n = m
:=
  calc
    n = |n| : symm (abs_to_int n)
  ... = |m| : {H}
  ... = m : abs_to_int m

-- ### definition of neg, add

definition neg : ℤ → ℤ := quotient_map quotient flip
notation 80 - _ : neg

theorem neg_comp (a : ℕ ## ℕ) : -psub a = psub (flip a)
:= comp_quotient_map quotient @rel_flip (rel_refl a)

theorem neg_comp2 (n m : ℕ) : -psub (tpair n m) = psub (tpair m n)
:=
  calc
    -psub (tpair n m) = psub (flip (tpair n m)) : {neg_comp _}
      ... = psub (tpair m n) : by simp

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

theorem add_comp (a b : ℕ ## ℕ) : psub a + psub b = psub (map_pair2 nat::add a b)
:= comp_quotient_map_binary_refl rel_refl quotient @rel_add a b

theorem add_comp2 (n m k l : ℕ) : psub (tpair n m) + psub (tpair k l) = psub (tpair (n + k) (m + l))
:= trans (add_comp (tpair n m) (tpair k l)) (by simp)

add_rewrite psub_rep neg_comp2 add_comp2 --local

theorem int_destruct (a : ℤ) : ∃n m : ℕ, a = psub (tpair n m)
:=
  exists_intro (xx (rep a))
    (exists_intro (yy (rep a))
      (calc
        a = psub (rep a) : by simp
      ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}))

-- ## neg

theorem neg_zero : -to_int 0 = 0
:=
  calc
    -psub (tpair 0 0) = psub (flip (tpair 0 0)) : by simp
      ... = psub (tpair 0 0) : by simp

theorem neg_neg (a : ℤ) : -(-a) = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  by simp

add_rewrite neg_neg

theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b
:=
  calc
    a = -(-a) : by simp_no_assump
      ... = b : by simp

theorem cases (a : ℤ) : (∃n : ℕ, a = n) ∨ (∃n : ℕ, a = -n)
:=
  have Hrep : proj (rep a) = rep a, from @idempotent_image_fix _ proj proj_idempotent a,
  or_imp_or (or_flip (proj_zero_or (rep a)))
    (assume H : yy (proj (rep a)) = 0,
      have H2 : yy (rep a) = 0, from subst H Hrep,
      exists_intro (xx (rep a))
        (calc
          a = psub (rep a) : by simp
            ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = psub (tpair (xx (rep a)) 0) : {H2}
            ... = to_int (xx (rep a)) : refl _))
    (assume H : xx (proj (rep a)) = 0,
      have H2 : xx (rep a) = 0, from subst H Hrep,
      exists_intro (yy (rep a))
        (calc
          a = psub (rep a) : by simp
            ... = psub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = psub (tpair 0 (yy (rep a))) : {H2}
            ... = -psub (tpair (yy (rep a)) 0) : by simp
            ... = -to_int (yy (rep a)) : refl _))

set_opaque int true
set_opaque psub true
set_opaque proj true
set_opaque abs true

theorem to_int_eq_neg_to_int {n m : ℕ} (H : n = - m) : n = 0 ∧ m = 0
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

-- ## add

theorem add_comm (a b : ℤ) : a + b = b + a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  by simp

theorem add_assoc (a b c : ℤ) : a + b + c = a + (b + c)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from int_destruct c,
  by simp

theorem add_left_comm (a b c : ℤ) : a + (b + c) = b + (a + c)
:= left_comm add_comm add_assoc a b c

theorem add_right_comm (a b c : ℤ) : a + b + c = a + c + b
:= right_comm add_comm add_assoc a b c

-- ### interaction with other objects

theorem add_zero_right (a : ℤ) : a + 0 = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  calc
    a + psub (tpair 0 0) = psub (tpair (xa + 0) (ya + 0)) : by simp
      ... = a : by simp

theorem add_zero_left (a : ℤ) : 0 + a = a
:= subst (add_zero_right a) (add_comm a 0)

theorem add_inverse_right (a : ℤ) : a + -a = 0
:=
  have H : ∀n, rel (tpair n n) (tpair 0 0), by simp,
  have H2 : ∀n, psub (tpair n n) = psub (tpair 0 0), from take n, eq_abs quotient (H n),
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  calc
    a + -a = psub (tpair (xa + ya) (xa + ya)) : by simp
      ... = psub (tpair 0 0) : by simp

theorem add_inverse_left (a : ℤ) : -a + a = 0
:= subst (add_inverse_right a) (add_comm a (-a))

theorem neg_add_distr (a b : ℤ) : -(a + b) = -a + -b
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  by simp

---set_option pp::coercion true

theorem add_to_int (n m : ℕ) : to_int n + to_int m = n + m -- this is to_int (n + m)
:=
  calc
    psub (tpair n 0) + psub (tpair m 0) = psub (tpair (n + m) (0 + 0)) : by simp
      ... = psub (tpair (n + m) 0) : by simp

theorem triangle_inequality (a b : ℤ) : |(a + b)| ≤ |a| + |b| --note: ≤ is nat::≤
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  have H : dist (xa + xb) (ya + yb) ≤ dist xa ya + dist xb yb,
    from dist_add_le_add_dist xa xb ya yb,
  by simp

add_rewrite add_to_int

theorem to_int_succ (n : ℕ) : to_int (succ n) = to_int n + 1
:= by simp

-- ### inversion theorems for add

-- a + a = 0 -> a = 0
-- a = -a -> a = 0

theorem add_cancel_left {a b c : ℤ} (H : a + b = a + c) : b = c
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from int_destruct c,
  have H2 : psub (tpair (xa + xb) (ya + yb)) = psub (tpair (xa + xc) (ya + yc)), from
    calc
      psub (tpair (xa + xb) (ya + yb)) = a + b : by simp
        ... = a + c : H
        ... = psub (tpair (xa + xc) (ya + yc)) : by simp,
  have H3 : rel (tpair (xa + xb) (ya + yb)) (tpair (xa + xc) (ya + yc)),
    from R_intro_refl quotient rel_refl H2,
  have H4 : xa + ya + (xb + yc) = xa + ya + (yb + xc), from
    calc
      xa + ya + (xb + yc)
            = xx (tpair (xa + xb) (ya + yb)) + yy (tpair (xa + xc) (ya + yc)) : by simp
        ... = yy (tpair (xa + xb) (ya + yb)) + xx (tpair (xa + xc) (ya + yc)) : H3
        ... = xa + ya + (yb + xc) : by simp,
  have H5 : rel (tpair xb yb) (tpair xc yc), from
    calc
      xx (tpair xb yb) + yy (tpair xc yc) = xb + yc : by simp
        ... = yb + xc : add_cancel_left H4
        ... = yy (tpair xb yb) + xx (tpair xc yc) : by simp,
  show b = c, from
    calc
      b = psub (tpair xb yb) : Hb
    ... = psub (tpair xc yc) : eq_abs quotient H5
    ... = c : symm Hc

  -- have lemma : ∀(u v w : ℕ ## ℕ)
  --     (K : rel (map_pair2 nat::add u v) (map_pair2 nat::add u w)), rel v w, from
  --   take (u v w : ℕ ## ℕ), assume K,
  --   have Hlem : xx u + yy u + (xx v + yy w) = xx u + yy u + (yy v + xx w), from
  --     calc
  --       xx u + yy u + (xx v + yy w) = xx u + xx v + (yy u + yy w) : add_switch _ _ _ _
  --         ... = xx (map_pair2 nat::add u v) + (yy u + yy w)
  --                 : {symm (map_pair2_xx nat::add u v)}
  --         ... = xx (map_pair2 nat::add u v) + yy (map_pair2 nat::add u w)
  --                 : {symm (map_pair2_yy nat::add u w)}
  --         ... = yy (map_pair2 nat::add u v) + xx (map_pair2 nat::add u w) : K
  --         ... = yy u + yy v + xx (map_pair2 nat::add u w) : {map_pair2_yy nat::add u v}
  --         ... = yy u + yy v + (xx u + xx w) : {map_pair2_xx nat::add u w}
  --         ... = yy u + xx u + (yy v + xx w) : add_switch _ _ _ _
  --         ... = xx u + yy u + (yy v + xx w) : {nat::add_comm (yy u) (xx u)},
  --   show rel v w, from nat::add_cancel_left Hlem,
  -- have H2 : psub (map_pair2 nat::add (rep a) (rep b))
  --         = psub (map_pair2 nat::add (rep a) (rep c)), from
  --   calc
  --     psub (map_pair2 nat::add (rep a) (rep b)) = psub (rep a) + psub (rep b)
  --               : symm (add_comp (rep a) (rep b))
  --       ... = a + b : by simp
  --       ... = a + c : H
  --       ... = psub (rep a) + psub (rep c) : by simp
  --       ... = psub (map_pair2 nat::add (rep a) (rep c)) : add_comp (rep a) (rep c),
  -- have H3 : rel (rep b) (rep c),
  --   from lemma (rep a) (rep b) (rep c) (R_intro_refl quotient rel_refl H2),
  -- show b = c, from rep_eq quotient H3

theorem add_cancel_right {a b c : ℤ} (H : a + b = c + b) : a = c
:= add_cancel_left (subst (subst H (add_comm a b)) (add_comm c b))

theorem add_eq_zero_right {a b : ℤ} (H : a + b = 0) : b = -a
:=
  have H2 : a + b = a + -a, from subst H (symm (add_inverse_right a)),
  show b = -a, from add_cancel_left H2

theorem add_eq_zero_left {a b : ℤ} (H : a + b = 0) : a = -b
:=
  calc
    a = -(-a) : symm (neg_neg a)
  ... = -b : {symm (add_eq_zero_right H)}

-- ## sub
definition sub (a b : ℤ) : ℤ := a + - b
infixl 65 - : sub

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

theorem sub_flip (a b : ℤ) : -(a - b) = b - a
:=
  calc
    -(a - b) = -a + b : neg_sub a b
      ... = b - a : add_comm (-a) b

---should the following three theorems be reversed?
theorem sub_add_assoc (a b c : ℤ) : a - (b + c) = a - b - c
:=
  calc
    a - (b + c) = a + (-b + -c) : {neg_add_distr b c}
      ... = a - b - c : symm (add_assoc a (-b) (-c))

theorem sub_sub_assoc (a b c : ℤ) : a - (b - c) = a - b + c
:=
  calc
    a - (b - c) = a + (-b + c) : {neg_sub b c}
      ... = a - b + c : symm (add_assoc a (-b) c)

theorem add_sub_assoc (a b c : ℤ) : a + (b - c) = a + b - c
:= symm (add_assoc a b (-c))

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

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c
:= neg_inj (add_cancel_left H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c
:= add_cancel_right H

theorem sub_eq_zero {a b : ℤ} (H : a - b = 0) : a = b
:= trans (add_eq_zero_left H) (neg_neg b)

---should some of the equalities below be reversed?
theorem add_imp_sub_right {a b c : ℤ} (H : a + b = c) : a = c - b
:=
  have H2 : a + b = c - b + b, from trans H (symm (sub_add_inverse c b)),
  add_cancel_right H2

theorem add_imp_sub_left {a b c : ℤ} (H : a + b = c) : b = c - a
:= add_imp_sub_right (subst H (add_comm a b))

theorem sub_imp_add {a b c : ℤ} (H : a - b = c) : a = c + b
:= subst (add_imp_sub_right H) (neg_neg b)

theorem sub_imp_sub {a b c : ℤ} (H : a - b = c) : b = a - c
:= have H2 : a = c + b, from sub_imp_add H, add_imp_sub_left (symm H2)

theorem sub_add_add_right (a b c : ℤ) : a + c - (b + c) = a - b
:=
  calc
    a + c - (b + c) = a + (c - (b + c)) : symm (add_sub_assoc a c (b + c))
      ... = a + (c - b - c) : {sub_add_assoc c b c}
      ... = a + -b : {add_sub_inverse2 c (-b)}

theorem sub_add_add_left (a b c : ℤ) : c + a - (c + b) = a - b
:= subst (subst (sub_add_add_right a b c) (add_comm a c)) (add_comm b c)

theorem dist_def (n m : ℕ) : dist n m = |(to_int n - m)| --should this be nat::dist_def?
:=
  have H : to_int n - m = psub (tpair n m), from
    calc
      psub (tpair n 0) + -psub (tpair m 0) = psub (tpair (n + 0) (0 + m)) : by simp
        ... = psub (tpair n m) : by simp,
  calc
    dist n m = |psub (tpair n m)| : by simp
      ... = |(to_int n - m)| : {symm H}

add_rewrite add_zero_left add_zero_right
add_rewrite add_comm add_assoc add_left_comm
add_rewrite add_neg_right add_neg_left

-- ## mul

theorem rel_mul_prep {xa ya xb yb xn yn xm ym : ℕ} (H1 : xa + yb = ya + xb) (H2 : xn + ym = yn + xm)
  : xa * xn + ya * yn + (xb * ym + yb * xm) = xa * yn + ya * xn + (xb * xm + yb * ym)
:=
 have H3 : xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
         = xa * yn + ya * xn + (xb * xm + yb * ym) + (yb * xn + xb * yn + (xb * xn + yb * yn)), from
 calc xa * xn + ya * yn + (xb * ym + yb * xm) + (yb * xn + xb * yn + (xb * xn + yb * yn))
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

theorem mul_comp (u v : ℕ ## ℕ) : psub u * psub v =
    psub (tpair (xx u * xx v + yy u * yy v) (xx u * yy v + yy u * xx v))
:= comp_quotient_map_binary_refl rel_refl quotient @rel_mul u v

theorem mul_comp2 (n m k l : ℕ)
    : psub (tpair n m) * psub (tpair k l) = psub (tpair (n * k + m * l) (n * l + m * k))
:= trans (mul_comp (tpair n m) (tpair k l)) (by simp)

add_rewrite mul_comp2

theorem mul_comm (a b : ℤ) : a * b = b * a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  by simp

theorem mul_assoc (a b c : ℤ) : (a * b) * c = a * (b * c)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from int_destruct c,
  by simp

theorem mul_left_comm : ∀a b c : ℤ, a * (b * c) = b * (a * c)
:= left_comm mul_comm mul_assoc

theorem mul_right_comm : ∀a b c : ℤ, a * b * c = a * c * b
:= right_comm mul_comm mul_assoc

-- ### interaction with other objects

theorem mul_zero_right (a : ℤ) : a * 0 = 0
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  calc
    a * psub (tpair 0 0) =  psub (tpair xa ya) * psub (tpair 0 0) : by simp
      ... =  psub (tpair 0 0) : by simp

theorem mul_zero_left (a : ℤ) : 0 * a = 0
:= subst (mul_zero_right a) (mul_comm a 0)

theorem mul_one_right (a : ℤ) : a * 1 = a
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  calc
    a * psub (tpair 1 0) =  psub (tpair xa ya) * psub (tpair 1 0) : by simp
      ... = a : by simp

theorem mul_one_left (a : ℤ) : 1 * a = a
:= subst (mul_one_right a) (mul_comm a 1)

theorem mul_neg_right (a b : ℤ) : a * -b = -(a * b)
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  by simp

theorem mul_neg_left (a b : ℤ) : -a * b = -(a * b)
:= subst (subst (mul_neg_right b a) (mul_comm b (-a))) (mul_comm b a)

add_rewrite mul_neg_right mul_neg_left

theorem mul_neg_neg (a b : ℤ) : -a * -b = a * b
:= by simp

theorem mul_distr_right (a b c : ℤ) : (a + b) * c = a * c + b * c
:=
  obtain (xa ya : ℕ) (Ha : a = psub (tpair xa ya)), from int_destruct a,
  obtain (xb yb : ℕ) (Hb : b = psub (tpair xb yb)), from int_destruct b,
  obtain (xc yc : ℕ) (Hc : c = psub (tpair xc yc)), from int_destruct c,
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

theorem mul_to_int (n m : ℕ) : to_int n * to_int m = n * m
:=
  calc
    psub (tpair n 0) * psub (tpair m 0) = psub (tpair (n * m + 0 * 0) (n * 0 + 0 * m)) : by simp
      ... = psub (tpair (n * m) 0) : by simp

-- theorem mul_abs (a b c : ℤ) : |a| * |b| = |(a * b)|
-- := _

add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
add_rewrite mul_comm mul_assoc mul_left_comm
add_rewrite mul_distr_right mul_distr_left

-- ---------- inversion

-- theorem mul_eq_zero {a b : ℤ} (H : a * b = 0) : a = 0 ∨ b = 0
-- :=
--   _

-- theorem mul_eq_mul {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c
-- :=

-- theorem mul_ne_zero {a b : ℤ} (Hn : a ≠ 0) (Hm : b ≠ 0) : a * b ≠ 0
-- :=
--   _

-- theorem mul_ne_zero_left {n m : ℤ} (H : n * m ≠ 0) : n ≠ 0
-- :=
--   _

-- theorem mul_pos_imp_pos_right {n m : ℤ} (H : n * m > 0) : m > 0
-- := mul_pos_imp_pos_left (subst H (mul_comm n m))

-- theorem mul_cancel_left {n m k : ℤ} (Hn : n ≠ 0) (H : n * m = n * k) : m = k
-- :=
--   have general : ∀m, n * m = n * k → m = k, from
--     induction_on k
--       (take m : nat,
--         assume H : n * m = n * 0,
--         have H2 : n * m = 0,
--           from calc
--             n * m = n * 0 : H
--               ... = 0 : mul_zero_right n,
--         have H3 : n = 0 ∨ m = 0, from mul_eq_zero H2,
--         resolve_right H3 (ne_symm (lt_imp_ne Hn)))
--       (take (l : ℤ),
--         assume (IH : ∀ m, n * m = n * l → m = l),
--         take (m : ℤ),
--         assume (H : n * m = n * succ l),
--         have H2 :  n * succ l > 0, from mul_pos Hn (succ_pos l),
--         have H3 : m > 0, from mul_pos_imp_pos_right (subst H2 (symm H)),
--         obtain (l2 : ℤ) (Hm : m = succ l2), from pos_imp_eq_succ H3,
--         have H4 : n * l2 + n = n * l + n,
--           from calc
--             n * l2 + n = n * succ l2 : symm (mul_succ_right n l2)
--               ... = n * m : {symm Hm}
--               ... = n * succ l : H
--               ... = n * l + n : mul_succ_right n l,
--         have H5 : n * l2 = n * l, from add_cancel_right H4,
--         calc
--           m = succ l2 : Hm
--         ... = succ l : {IH l2 H5}),
--   general m H

-- theorem mul_cancel_right {n m k : ℤ} (Hm : m > 0) (H : n * m = k * m) : n = k
-- := mul_cancel_left Hm (subst (subst H (mul_comm n m)) (mul_comm k m))

-- theorem mul_lt_left {n m k : ℤ} (Hk : k > 0) (H : n < m) : k * n < k * m
-- :=
--   have H2 : k * n < k * n + k, from add_pos_right (k * n) Hk,
--   have H3 : k * n + k ≤ k * m, from subst (mul_le_left H k) (mul_succ_right k n),
--   lt_le_trans H2 H3

-- theorem mul_lt_right {n m k : ℤ} (Hk : k > 0) (H : n < m)  : n * k < m * k
-- := subst (subst (mul_lt_left Hk H) (mul_comm k n)) (mul_comm k m)

-- theorem mul_le_lt {n m k l : ℤ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) : n * m < k * l
-- := le_lt_trans (mul_le_right H1 m) (mul_lt_left Hk H2)

-- theorem mul_lt_le {n m k l : ℤ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) : n * m < k * l
-- := le_lt_trans (mul_le_left H2 n) (mul_lt_right Hl H1)

-- theorem mul_lt {n m k l : ℤ} (H1 : n < k) (H2 : m < l) : n * m < k * l
-- :=
--   have H3 : n * m ≤ k * m, from mul_le_right (lt_imp_le H1) m,
--   have H4 : k * m < k * l, from mul_lt_left (le_lt_trans (zero_le n) H1) H2,
--   le_lt_trans H3 H4

-- theorem mul_lt_cancel_left {n m k : ℤ} (H : k * n < k * m) : n < m
-- :=
--   have general : ∀ m, k * n < k * m → n < m, from
--     induction_on n
--       (take m : nat,
--         assume H2 : k * 0 < k * m,
--         have H3 : 0 < k * m, from subst H2 (mul_zero_right k),
--         show 0 < m, from mul_pos_imp_pos_right H3)
--       (take l : nat,
--         assume IH : ∀ m, k * l < k * m → l < m,
--         take m : nat,
--         assume H2 : k * succ l < k * m,
--         have H3 : 0 < k * m, from le_lt_trans (zero_le _) H2,
--         have H4 : 0 < m, from mul_pos_imp_pos_right H3,
--         obtain (l2 : ℤ) (Hl2 : m = succ l2), from pos_imp_eq_succ H4,
--         have H5 : k * l + k < k * m, from subst H2 (mul_succ_right k l),
--         have H6 : k * l + k < k * succ l2, from subst H5 Hl2,
--         have H7 : k * l + k < k * l2 + k, from subst H6 (mul_succ_right k l2),
--         have H8 : k * l < k * l2, from add_lt_cancel_right H7,
--         have H9 : l < l2, from IH l2 H8,
--         have H10 : succ l < succ l2, from succ_lt H9,
--         show succ l < m, from subst H10 (symm Hl2)),
--   general m H

-- theorem mul_lt_cancel_right {n m k : ℤ} (H : n * k < m * k) : n < m
-- := mul_lt_cancel_left (subst (subst H (mul_comm n k)) (mul_comm m k))

-- theorem mul_le_cancel_left {n m k : ℤ} (Hk : k > 0) (H : k * n ≤ k * m) : n ≤ m
-- :=
--   have H2 : k * n < k * m + k, from le_lt_trans H (add_pos_right _ Hk),
--   have H3 : k * n < k * succ m, from subst H2 (symm (mul_succ_right k m)),
--   have H4 : n < succ m, from mul_lt_cancel_left H3,
--   show n ≤ m, from lt_succ_imp_le H4

-- theorem mul_le_cancel_right {n m k : ℤ} (Hm : m > 0) (H : n * m ≤ k * m) : n ≤ k
-- := mul_le_cancel_left Hm (subst (subst H (mul_comm n m)) (mul_comm k m))

-- theorem mul_eq_one_left {n m : ℤ} (H : n * m = 1) : n = 1 ∨ n = -1
-- :=
--   have H2 : n * m > 0, from subst (succ_pos 0) (symm H),
--   have H3 : n > 0, from mul_pos_imp_pos_left H2,
--   have H4 : m > 0, from mul_pos_imp_pos_right H2,
--   or_elim (le_or_lt n 1)
--     (assume H5 : n ≤ 1,
--       show n = 1, from le_antisym H5 H3)
--     (assume H5 : n > 1,
--       have H6 : n * m ≥ 2 * 1, from mul_le H5 H4,
--       have H7 : 1 ≥ 2, from subst (subst H6 H) (mul_one_right 2),
--       absurd_elim _ (self_lt_succ 1) (le_imp_not_lt H7))

-- theorem mul_eq_one_right {n m : ℤ} (H : n * m = 1) : m = 1 ∨ m = -1
-- := mul_eq_one_left (subst H (mul_comm n m))

add_rewrite mul_zero_left mul_zero_right
add_rewrite mul_comm mul_assoc

-- ## le
definition le (a b : ℤ) : Bool := ∃n : ℕ, a + n = b
infix  50 <= : le
infix  50 ≤  : le

-- definition le : ℤ → ℤ → Bool := rec_binary quotient (fun a b, xx a + yy b ≤ yy a + xx b)
-- theorem le_comp (u v : ℕ ## ℕ) : (psub u ≤ psub v) ↔ (xx u + yy v ≤ yy u + xx v)
-- :=
--   comp_binary_refl quotient rel_refl
--   (take u u' v v' : ℕ ## ℕ,
--     assume Hu : rel u u',
--     assume Hv : rel v v',

--   u v

-- theorem le_intro {a b : ℤ} {n : ℕ} (H : a + to_int n = b) : a ≤ b
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

theorem le_to_int (n m : ℕ) : (n ≤ m) ↔ (to_int n ≤ to_int m)
:=
  iff_intro
    (assume H : n ≤ m,
      obtain (k : ℕ) (Hk : n + k = m), from nat::le_elim H,
      have H2 : to_int n + to_int k = to_int m, from subst (add_to_int n k) Hk,
      le_intro H2)
    (assume H : to_int n ≤ to_int m,
      obtain (k : ℕ) (Hk : to_int n + to_int k = to_int m), from le_elim H,
      have H2 : n + k = m, from to_int_inj (trans (symm (add_to_int n k)) Hk),
      nat::le_intro H2)

theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = c), from le_elim H2,
  have H3 : a + (n + m) = c, from
    calc
      a + (n + m) = a + (to_int n + m) : {symm (add_to_int n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = c : Hm,
  le_intro H3

--set_option pp::coercion true

theorem le_antisym {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = a), from le_elim H2,
  have H3 : a + (n + m) = a + 0, from
    calc
      a + (n + m) = a + (to_int n + m) : {symm (add_to_int n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = a : Hm
        ... = a + 0 : symm (add_zero_right a),
  have H4 : to_int (n + m) = to_int 0, from add_cancel_left H3,
  have H5 : n + m = 0, from to_int_inj H4,
  have H6 : n = 0, from nat::add_eq_zero_left H5,
  show a = b, from
    calc
      a = a + to_int 0 : symm (add_zero_right a)
        ... = a + n : {symm H6}
        ... = b : Hn


-- ### interaction with add

theorem le_add_to_int_right (a : ℤ) (n : ℕ) : a ≤ a + n
:= le_intro (refl (a + n))

theorem le_add_to_int_left (a : ℤ) (n : ℕ) : a ≤ n + a
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

theorem add_le_cancel_left {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b
:=
  obtain (n : ℕ) (Hn : c + a + n = c + b), from le_elim H,
  have H2 : c + (a + n) = c + b, from
    calc
      c + (a + n) = c + a + n : symm (add_assoc c a n)
        ... = c + b : Hn,
  have H3 : a + n = b, from add_cancel_left H2,
  le_intro H3

theorem add_le_cancel_right {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b
:= add_le_cancel_left (subst (subst H (add_comm a c)) (add_comm b c))

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d
:=
  obtain (n : ℕ) (Hn : c + n = a), from le_elim H2,
  have H3 : c + (n + b) ≤ c + d, from subst (subst H1 (symm Hn)) (add_assoc c n b),
  have H4 : n + b ≤ d, from add_le_cancel_left H3,
  show b ≤ d, from le_trans (le_add_to_int_left b n) H4

theorem le_add_to_int_right_trans {a b : ℤ} (H : a ≤ b) (n : ℕ) : a ≤ b + n
:= le_trans H (le_add_to_int_right b n)

theorem le_split {a b : ℤ} (H : a ≤ b) : a + 1 ≤ b ∨ a = b
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

-- theorem test3 {a b n k : ℤ} (H1 : n = k + 1) (H2 : b = a + n) : a + (k + 1) = b
-- :=
--   calc
--     a + (k + 1) = a + n : by simp
--       ... = b : by simp

-- theorem test2 {a b n k : ℤ} (H1 : n = k + 1) (H2 : a + n = b) : a + (k + 1) = b
-- :=
--   calc
--     a + (k + 1) = a + n : by simp
--       ... = b : by simp

-- theorem test {a b : ℤ} {n k : ℕ} (H1 : n = succ k) (H2 : a + n = b) : a + succ k = b
-- :=
--   calc
--     a + succ k = a + n : by simp
--       ... = b : by simp

-- ### interaction with neg and sub

theorem le_neg {a b : ℤ} (H : a ≤ b) : -b ≤ -a
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
  have H2 : b - n = a, from symm (add_imp_sub_right Hn),
  have H3 : -b + n = -a, from
    calc
      -b + n = -b + -(-n) : {symm (neg_neg n)}
        ... = -(b - n) : symm (neg_add_distr b (-n))
        ... = -a : {H2},
  le_intro H3

theorem le_neg_inv {a b : ℤ} (H : -a ≤ -b) : b ≤ a
:= subst (subst (le_neg H) (neg_neg a)) (neg_neg b)

-- theorem le_nzneg (n m : ℕ) : (n ≤ m) ↔ (nzneg m ≤ nzneg n)
-- :=
--   calc
--     (n ≤ m) = (to_int n ≤ to_int m) : le_to_int n m
--       ... = (-to_int m ≤ -to_int n) : iff_intro (take H, le_neg H) (take H, le_neg_inv H)
--       ... = (nzneg m ≤ -to_int n) : {neg_to_int m}
--       ... = (nzneg m ≤ nzneg n) : {neg_to_int n}

theorem le_sub_to_int (a : ℤ) (n : ℕ) : a - n ≤ a
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



-- -- ### interaction with mul

-- theorem mul_le_left {n m : ℤ} (H : n ≤ m) (k : ℤ) : k * n ≤ k * m
-- :=
--   obtain (l : ℤ) (Hl : n + l = m), from (le_elim H),
--   induction_on k
--     (have H2 : 0 * n = 0 * m,
--       from calc
--         0 * n = 0 : mul_zero_left n
--           ... = 0 * m : symm (mul_zero_left m),
--       show 0 * n ≤ 0 * m, from subst (le_refl (0 * n)) H2)
--     (take (l : ℤ),
--       assume IH : l * n ≤ l * m,
--       have H2 : l * n + n ≤ l * m + m, from add_le IH H,
--       have H3 : succ l * n ≤ l * m + m, from subst H2 (symm (mul_succ_left l n)),
--       show succ l * n ≤ succ l * m, from subst H3 (symm (mul_succ_left l m)))

-- theorem mul_le_right {n m : ℤ} (H : n ≤ m) (k : ℤ) : n * k ≤ m * k
-- := subst (subst (mul_le_left H k) (mul_comm k n)) (mul_comm k m)

-- theorem mul_le {n m k l : ℤ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l
-- := le_trans (mul_le_right H1 m) (mul_le_left H2 k)


-- Less than
-- ---------

definition lt (a b : ℤ) := a + 1 ≤ b
infix 50 <  : lt

theorem lt_intro {a b : ℤ} {n : ℕ} (H : a + 1 + n = b) : a < b
:= le_intro H

theorem lt_elim {a b : ℤ} (H : a < b) : ∃ n : ℕ, a + 1 + n = b
:= le_elim H

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n
:= lt_intro (show a + 1 + n = a + succ n, by simp)

-- -- ### basic facts

-- theorem lt_imp_ne {a b : ℤ} (H : a < b) : a ≠ b
-- := _ --and_elim_right (succ_le_imp_le_and_ne H)

-- theorem lt_irrefl (a : ℤ) : ¬ a < a
-- := not_intro (assume H : n < n, absurd (refl n) (lt_imp_ne H))

-- theorem succ_pos (n : ℤ) : 0 < succ n
-- := succ_le (zero_le n)

-- theorem not_lt_zero (n : ℤ) : ¬ n < 0
-- := not_succ_zero_le n

-- theorem lt_imp_eq_succ {n m : ℤ} (H : n < m) : exists k, m = succ k
-- :=
--   discriminate
--     (take (Hm : m = 0), absurd_elim _ (subst H Hm) (not_lt_zero n))
--     (take (l : ℤ) (Hm : m = succ l), exists_intro l Hm)

-- -- ### interaction with le

-- theorem lt_imp_le_succ {n m : ℤ} (H : n < m) : succ n ≤ m
-- := H

-- theorem le_succ_imp_lt {n m : ℤ} (H : succ n ≤ m) : n < m
-- := H

-- theorem self_lt_succ (n : ℤ) : n < succ n
-- := le_refl (succ n)

-- theorem lt_imp_le {n m : ℤ} (H : n < m) : n ≤ m
-- := and_elim_left (succ_le_imp_le_and_ne H)

-- theorem le_imp_lt_or_eq {n m : ℤ} (H : n ≤ m) : n < m ∨ n = m
-- := le_imp_succ_le_or_eq H

-- theorem le_ne_imp_lt {n m : ℤ} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m
-- := le_ne_imp_succ_le H1 H2

-- theorem le_imp_lt_succ {n m : ℤ} (H : n ≤ m) : n < succ m
-- := succ_le H

-- theorem lt_succ_imp_le {n m : ℤ} (H : n < succ m) : n ≤ m
-- := succ_le_cancel H

-- -- ### transitivity, antisymmmetry

-- theorem lt_le_trans {n m k : ℤ} (H1 : n < m) (H2 : m ≤ k) : n < k
-- := le_trans H1 H2

-- theorem le_lt_trans {n m k : ℤ} (H1 : n ≤ m) (H2 : m < k) : n < k
-- := le_trans (succ_le H1) H2

-- theorem lt_trans {n m k : ℤ} (H1 : n < m) (H2 : m < k) : n < k
-- := lt_le_trans H1 (lt_imp_le H2)

-- theorem le_imp_not_lt {n m : ℤ} (H : n ≤ m) : ¬ m < n
-- := not_intro (take H2 : m < n, absurd (le_lt_trans H H2) (lt_irrefl n))

-- theorem lt_imp_not_le {n m : ℤ} (H : n < m) : ¬ m ≤ n
-- := not_intro (take H2 : m ≤ n, absurd (lt_le_trans H H2) (lt_irrefl n))

-- theorem lt_antisym {n m : ℤ} (H : n < m) : ¬ m < n
-- := le_imp_not_lt (lt_imp_le H)

-- -- ### interaction with addition

-- theorem add_lt_left {n m : ℤ} (H : n < m) (k : ℤ) : k + n < k + m
-- := substp (fun x, x ≤ k + m) (add_le_left H k) (add_succ_right k n)

-- theorem add_lt_right {n m : ℤ} (H : n < m) (k : ℤ) : n + k < m + k
-- := subst (subst (add_lt_left H k) (add_comm k n)) (add_comm k m)

-- theorem add_le_lt {n m k l : ℤ} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l
-- := le_lt_trans (add_le_right H1 m) (add_lt_left H2 k)

-- theorem add_lt_le {n m k l : ℤ} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l
-- := lt_le_trans (add_lt_right H1 m) (add_le_left H2 k)

-- theorem add_lt {n m k l : ℤ} (H1 : n < k) (H2 : m < l) : n + m < k + l
-- := add_lt_le H1 (lt_imp_le H2)

-- theorem add_lt_cancel_left {n m k : ℤ} (H : k + n < k + m) : n < m
-- := add_le_cancel_left (subst H (symm (add_succ_right k n)))

-- theorem add_lt_cancel_right {n m k : ℤ} (H : n + k < m + k) : n < m
-- := add_lt_cancel_left (subst (subst H (add_comm n k)) (add_comm m k))

-- -- ### interaction with successor (see also the interaction with le)

-- theorem succ_lt {n m : ℤ} (H : n < m) : succ n < succ m
-- := subst (subst (add_lt_right H 1) (add_one n)) (add_one m)

-- theorem succ_lt_cancel {n m : ℤ} (H : succ n < succ m) :  n < m
-- := add_lt_cancel_right (subst (subst H (symm (add_one n))) (symm (add_one m)))

-- theorem lt_imp_lt_succ {n m : ℤ} (H : n < m) : n < succ m
--  := lt_trans H (self_lt_succ m)

-- -- ### totality of lt and le

-- theorem le_or_lt (n m : ℤ) : n ≤ m ∨ m < n
-- :=
--   induction_on n
--     (or_intro_left _ (zero_le m))
--     (take (k : ℤ),
--       assume IH : k ≤ m ∨ m < k,
--       or_elim IH
--         (assume H : k ≤ m,
--           obtain (l : ℤ) (Hl : k + l = m), from le_elim H,
--           discriminate
--             (assume H2 : l = 0,
--               have H3 : m = k,
--                 from calc
--                   m = k + l : symm Hl
--                     ... = k + 0 : {H2}
--                     ... = k : add_zero_right k,
--               have H4 : m < succ k, from subst (self_lt_succ m) H3,
--               or_intro_right _ H4)
--             (take l2 : nat,
--               assume H2 : l = succ l2,
--               have H3 : succ k + l2 = m,
--                 from calc
--                   succ k + l2 = k + succ l2 : add_move_succ k l2
--                     ... = k + l : {symm H2}
--                     ... = m : Hl,
--               or_intro_left _ (le_intro H3)))
--         (assume H : m < k, or_intro_right _ (lt_imp_lt_succ H)))

-- theorem trichotomy_alt (n m : ℤ) : (n < m ∨ n = m) ∨ m < n
-- := or_imp_or (le_or_lt n m) (assume H : n ≤ m, le_imp_lt_or_eq H) (assume H : m < n, H)

-- theorem trichotomy (n m : ℤ) : n < m ∨ n = m ∨ m < n
-- := iff_elim_left (or_assoc _ _ _) (trichotomy_alt n m)

-- theorem le_total (n m : ℤ) : n ≤ m ∨ m ≤ n
-- := or_imp_or (le_or_lt n m) (assume H : n ≤ m, H) (assume H : m < n, lt_imp_le H)

-- theorem not_lt_imp_le {n m : ℤ} (H : ¬ n < m) : m ≤ n
-- := resolve_left (le_or_lt m n) H

-- theorem not_le_imp_lt {n m : ℤ} (H : ¬ n ≤ m) : m < n
-- := resolve_right (le_or_lt n m) H

-- -- Note: interaction with multiplication under "positivity"

-- -- ### misc

-- theorem strong_induction_on {P : nat → Bool} (n : ℤ) (H : ∀n, (∀m, m < n → P m) → P n) : P n
-- :=
--   have H1 : ∀n, ∀m, m < n → P m, from
--     take n,
--     induction_on n
--       (show ∀m, m < 0 → P m, from take m H, absurd_elim _ H (not_lt_zero _))
--       (take n',
--         assume IH : ∀m, m < n' → P m,
--         have H2: P n', from H n' IH,
--         show ∀m, m < succ n' → P m, from
--           take m,
--           assume H3 : m < succ n',
--           or_elim (le_imp_lt_or_eq (lt_succ_imp_le H3))
--             (assume H4: m < n', IH _ H4)
--             (assume H4: m = n', subst H2 (symm H4))),
--   H1 _ _ (self_lt_succ n)

-- theorem case_strong_induction_on {P : nat → Bool} (a : nat) (H0 : P 0)
--     (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a
-- :=
--   strong_induction_on a (
--     take n,
--     show (∀m, m < n → P m) → P n, from
--       case n
--          (assume H : (∀m, m < 0 → P m), show P 0, from H0)
--          (take n,
--            assume H : (∀m, m < succ n → P m),
--            show P (succ n), from
--              Hind n (take m, assume H1 : m ≤ n, H _ (le_imp_lt_succ H1))))

-- theorem add_eq_self {n m : ℤ} (H : n + m = n) : m = 0
-- :=
--   discriminate
--     (assume Hm : m = 0, Hm)
--     (take k : nat,
--       assume Hm : m = succ k,
--       have H2 : succ n + k = n,
--         from calc
--           succ n + k = n + succ k : add_move_succ n k
--             ... = n + m : {symm Hm}
--             ... = n : H,
--       have H3 : n < n, from lt_intro H2,
--       have H4 : n ≠ n, from lt_imp_ne H3,
--       absurd_elim _ (refl n) H4)

-- -- Greater than, greater than or equal
-- -- -----------------------------------

-- definition ge (n m : ℤ) := m ≤ n
-- infix 50 >= : ge
-- infix 50 ≥  : ge

-- definition gt (n m : ℤ) := m < n
-- infix 50 >  : gt

-- --- prove some theorems, like ge_imp_le le_imp_ge lt_imp_gt gt_imp_lt?

-- -- Positivity
-- -- ---------
-- --
-- -- Writing "t > 0" is the preferred way to assert that a natural number is positive.

-- -- ### basic

-- -- See also succ_pos.

-- theorem case_zero_pos {P : ℤ → Bool} (y : ℤ) (H0 : P 0) (H1 : ∀y, y > 0 → P y) : P y
-- := case y H0 (take y', H1 _ (succ_pos _))

-- theorem zero_or_pos (n : ℤ) : n = 0 ∨ n > 0
-- := or_imp_or (or_flip (le_imp_lt_or_eq (zero_le n))) (take H : 0 = n, symm H) (take H : n > 0, H)

-- theorem succ_imp_pos {n m : ℤ} (H : n = succ m) : n > 0
-- := subst (succ_pos m) (symm H)

-- theorem ne_zero_pos {n : ℤ} (H : n ≠ 0) : n > 0
-- := or_elim (zero_or_pos n) (take H2 : n = 0, absurd_elim _ H2 H) (take H2 : n > 0, H2)

-- theorem pos_imp_eq_succ {n : ℤ} (H : n > 0) : exists l, n = succ l
-- := lt_imp_eq_succ H

-- theorem add_pos_right (n : ℤ) {k : ℤ} (H : k > 0) : n + k > n
-- :=
--   obtain (l : ℤ) (Hl : k = succ l), from pos_imp_eq_succ H,
--   subst (lt_add_succ n l) (symm Hl)

-- theorem add_pos_left (n : ℤ) {k : ℤ} (H : k > 0) : k + n > n
-- := subst (add_pos_right n H) (add_comm n k)





set_opaque neg true
set_opaque add true
set_opaque mul true
set_opaque le true
set_opaque lt true
set_opaque rep true
--transparent: sub

end -- namespace int
