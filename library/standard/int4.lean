
----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import nat
import quotient
import macros tactic

-------------------------------------------------- axioms int

namespace int
using nat
using quot
using subtype
unary_nat

---------- rel

definition rel (a b : ℕ ## ℕ) : Bool := xx a + yy b = yy a + xx b

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
     xx a + yy c + yy b = xx a + yy b + yy c : add_comm_right _ _ _
      ... = yy a + xx b + yy c : {H1}
      ... = yy a + (xx b + yy c) : add_assoc _ _ _
      ... = yy a + (yy b + xx c) : {H2}
      ... = yy a + (xx c + yy b) : {add_comm _ _}
      ... = yy a + xx c + yy b : symm (add_assoc _ _ _),
  show xx a + yy c = yy a + xx c, from add_left_inj H3

theorem rel_equiv : equivalence rel
:= and_intro rel_refl (and_intro @rel_symm @rel_trans)

theorem rel_flip {a b : ℕ ## ℕ} (H : rel a b) : rel (flip a) (flip b)
:=
  calc
    xx (flip a) + yy (flip b) = yy a + yy (flip b) : {flip_xx a}
      ... = yy a + xx b : {flip_yy b}
      ... = xx a + yy b : symm H
      ... = xx a + xx (flip b) : {symm (flip_xx b)}
      ... = yy (flip a) + xx (flip b) : {symm (flip_yy a)}

theorem rel_add {a a' b b' : ℕ ## ℕ} (Ha : rel a a') (Hb : rel b b')
    : rel (map_pair2 add a b) (map_pair2 add a' b')
:=
  calc
    xx (map_pair2 add a b) + yy (map_pair2 add a' b') = xx a + xx b + (yy a' + yy b')
            : subst (subst (refl _) (map_pair2_xx add a b)) (map_pair2_yy add a' b')
      ... = xx a + yy a' + (xx b + yy b') : add_switch _ _ _ _
      ... = yy a + xx a' + (xx b + yy b') : {Ha}
      ... = yy a + xx a' + (yy b + xx b') : {Hb}
      ... = yy a + yy b + (xx a' + xx b') : add_switch _ _ _ _
      ... = yy (map_pair2 add a b) + xx (map_pair2 add a' b')
            : subst (subst (refl _) (symm (map_pair2_yy add a b))) (symm (map_pair2_xx add a' b'))

---------- proj

definition proj (a : ℕ ## ℕ) : ℕ ## ℕ
:= if xx a ≥ yy a then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a)

theorem proj_ge {a : ℕ ## ℕ} (H : xx a ≥ yy a) : proj a = tpair (xx a - yy a) 0
:=
  calc
    proj a = if true then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a) : {eqt_intro H}
      ... = tpair (xx a - yy a) 0 : if_true (tpair (xx a - yy a) 0) (tpair 0 (yy a - xx a))

theorem proj_lt {a : ℕ ## ℕ} (H : xx a < yy a) : proj a = tpair 0 (yy a - xx a)
:=
  have H2 : ¬ xx a ≥ yy a, from lt_le_antisym H,
  calc
    proj a = if false then tpair (xx a - yy a) 0 else tpair 0 (yy a - xx a) : {eqf_intro H2}
      ... = tpair 0 (yy a - xx a) : if_false (tpair (xx a - yy a) 0) (tpair 0 (yy a - xx a))

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
          ... = yy a + (xx a - yy a) : symm (add_sub_right H)
          ... = yy a + xx (proj a) : {symm (proj_ge_xx H)})
    (assume H : xx a ≤ yy a,
      calc
        xx a + yy (proj a) = xx a + (yy a - xx a) : {proj_le_yy H}
          ... = yy a : add_sub_right H
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

---------- int

definition int := image proj
alias ℤ : int

definition prod_sub : ℕ ## ℕ → ℤ := fun_image proj
definition rep : ℤ → ℕ ## ℕ := subtype::rep

--theorem int_inhabited : inhabited int
--:= image_inhabited2 proj (tpair 0 0)

theorem quotient : @is_quotient (ℕ ## ℕ) ℤ rel prod_sub rep
:= representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

definition nzpos (n : ℕ) : ℤ := prod_sub (tpair n 0)
definition nzneg (n : ℕ) : ℤ := prod_sub (tpair 0 n)
coercion nzpos

theorem zero_pos_eq_neg : nzpos 0 = nzneg 0
:= refl _

theorem cases (a : int) : (exists n : nat, a = n) ∨ (exists n : nat, a = nzneg n)
:=
  have Hv : proj (rep a) = rep a, from @idempotent_image_fix _ proj proj_idempotent a,
  or_imp_or (or_flip (proj_zero_or (rep a)))
    (assume H : yy (proj (rep a)) = 0,
      have H2 : yy (rep a) = 0, from substp (fun x, yy x = 0) H Hv,
      exists_intro (xx (rep a))
        (calc
          a = prod_sub (rep a) : symm (idempotent_image_rep proj_idempotent a)
            ... = prod_sub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = prod_sub (tpair (xx (rep a)) 0) : {H2}
            ... = nzpos (xx (rep a)) : refl _))
    (assume H : xx (proj (rep a)) = 0,
      have H2 : xx (rep a) = 0, from subst H (idempotent_image_fix proj_idempotent a),
      exists_intro (yy (rep a))
        (calc
          a = prod_sub (rep a) : symm (idempotent_image_rep proj_idempotent a)
            ... = prod_sub (tpair (xx (rep a)) (yy (rep a))) : {symm (tpair_tproj_eq (rep a))}
            ... = prod_sub (tpair 0 (yy (rep a))) : {H2}
            ... = nzneg (yy (rep a)) : refl _))

theorem nzpos_eq_nzneg {n m : nat} (H : nzpos n = nzneg m) : n = 0 ∧ m = 0
:=
  have H2 : rel (tpair n 0) (tpair 0 m), from R_intro_refl quotient rel_refl H,
  have H3 : n + m = 0, from
    calc
      n + m = xx (tpair n 0) + yy (tpair 0 m) : by simp
        ... = yy (tpair n 0) + xx (tpair 0 m) : H2
        ... = 0 + 0 : by simp
        ... = 0 : add_zero_right 0,
  add_eq_zero H3

--absolute value (rename to abs? or is that confusing with quot::abs?)
definition modulus : ℤ → ℕ := rec_constant quotient (fun v, sub_abs (xx v) (yy v))

theorem modulus_comp (v : ℕ ## ℕ) : modulus (prod_sub v) = sub_abs (xx v) (yy v)
:=
  comp_constant quotient
    (take v w : ℕ ## ℕ,
      assume H : rel v w,
      show sub_abs (xx v) (yy v) = sub_abs (xx w) (yy w), from sub_abs_eq H)
    (rel_refl v)


theorem modulus_nzpos (n:nat) : modulus (nzpos n) = n
:=
  calc
    modulus (nzpos n) = sub_abs (xx (tpair n 0)) (yy (tpair n 0)) : modulus_comp _
      ... = sub_abs n 0 : by simp
      ... = n : sub_abs_zero_right n

theorem modulus_nzneg (n:nat) : modulus (nzneg n) = n
:=
  calc
    modulus (nzneg n) = sub_abs (xx (tpair 0 n)) (yy (tpair 0 n)) : modulus_comp _
      ... = sub_abs 0 n : by simp
      ... = n : sub_abs_zero_left n

theorem nzpos_inj {n m:nat} (H : nzpos n = nzpos m) : n = m
:=
  calc
    n = modulus (nzpos n) : symm (modulus_nzpos n)
  ... = modulus (nzpos m) : {H}
  ... = m : modulus_nzpos m

theorem nzneg_inj {n m:nat} (H : nzneg n = nzneg m) : n = m
:=
  calc
    n = modulus (nzneg n) : symm (modulus_nzneg n)
  ... = modulus (nzneg m) : {H}
  ... = m : modulus_nzneg m

set_opaque int true
set_opaque prod_sub true
set_opaque proj true
set_opaque modulus true

-------------------------------------------------- arithmetic

definition neg : ℤ → ℤ := quotient_map quotient flip
notation 70 - _ : neg

theorem neg_comp (a : ℕ ## ℕ) : -prod_sub a = prod_sub (flip a)
:= comp_quotient_map quotient @rel_flip (rel_refl a)


definition add : ℤ → ℤ → ℤ := quotient_map_binary quotient (map_pair2 nat::add)
infixl 65 +  : add

theorem add_comp (a b : ℕ ## ℕ) : prod_sub a + prod_sub b = prod_sub (map_pair2 nat::add a b)
:= comp_quotient_map_binary_refl rel_refl quotient @rel_add a b

theorem abs_rep_int (a : ℤ) : prod_sub (rep a) = a
:= abs_rep quotient a

add_rewrite abs_rep_int neg_comp add_comp

theorem neg_nzpos (n : ℕ) : -n = nzneg n
:=
  calc
    -nzpos n = prod_sub (flip (tpair n 0)) : neg_comp (tpair n 0)
      ... = prod_sub (tpair 0 n) : {flip_pair n 0}

theorem neg_nzneg (n : ℕ) : -nzneg n = n
:=
  calc
    -nzneg n = prod_sub (flip (tpair 0 n)) : neg_comp (tpair 0 n)
      ... = prod_sub (tpair n 0) : {flip_pair 0 n}

theorem neg_zero : -nzpos 0 = 0
:= trans (neg_nzpos 0) (symm zero_pos_eq_neg)

theorem neg_neg (a : ℤ) : -(-a) = a
:=
  calc
    -(-a) = -(-prod_sub (rep a)) : by simp
      ... = -prod_sub (flip (rep a)) : {neg_comp (rep a)}
      ... = prod_sub (flip (flip (rep a))) : {neg_comp (flip (rep a))}
      ... = prod_sub (rep a) : {flip_flip (rep a)}
      ... = a : by simp


theorem neg_inj {a b : ℤ} (H : -a = -b) : a = b
:=
  calc
    a = -(-a) : symm (neg_neg a)
      ... = -(-b) : {H}
      ... = b : neg_neg b

theorem add_comm (a b : ℤ) : a + b = b + a
:=
  calc
    a + b = prod_sub (rep a) + prod_sub (rep b) : by simp
      ... = prod_sub (map_pair2 nat::add (rep a) (rep b)) : {add_comp (rep a) (rep b)}
      ... = prod_sub (map_pair2 nat::add (rep b) (rep a))
              : {map_pair2_comm nat::add_comm (rep a) (rep b)}
      ... = prod_sub (rep b) + prod_sub (rep a) : {symm (add_comp (rep b) (rep a))}
      ... = b + a : by simp

theorem add_assoc (a b c : ℤ) : a + b + c = a + (b + c)
:=
  calc
    a + b + c = prod_sub (rep a) + prod_sub (rep b) + prod_sub (rep c) : by simp
      ... = prod_sub (map_pair2 nat::add (rep a) (rep b)) + prod_sub (rep c)
              : {add_comp (rep a) (rep b)}
      ... = prod_sub (map_pair2 nat::add (map_pair2 nat::add (rep a) (rep b)) (rep c))
              : {add_comp _ (rep c)}
      ... = prod_sub (map_pair2 nat::add (rep a) (map_pair2 nat::add (rep b) (rep c)))
              : {map_pair2_assoc nat::add_assoc (rep a) (rep b) (rep c)}
      ... = prod_sub (rep a) + prod_sub (map_pair2 nat::add (rep b) (rep c))
              : symm (add_comp (rep a) _)
      ... = prod_sub (rep a) + (prod_sub (rep b) + prod_sub (rep c))
              : {symm (add_comp (rep b) (rep c))}
      ... = a + (b + c) : by simp

theorem add_comm_left (a b c : ℤ) : a + (b + c) = b + (a + c)
:= left_comm add_comm add_assoc a b c

theorem add_comm_right (a b c : ℤ) : a + b + c = a + c + b
:= right_comm add_comm add_assoc a b c

theorem add_zero_right (a : ℤ) : a + 0 = a
:=
  calc
    a + 0 = prod_sub (rep a) + prod_sub (tpair 0 0) : {symm (abs_rep_int a)}
      ... = prod_sub (map_pair2 nat::add (rep a) (tpair 0 0)) : {add_comp (rep a) (tpair 0 0)}
      ... = prod_sub (rep a) : {map_pair2_id_right nat::add_zero_right (rep a)}
      ... = a : by simp

theorem add_zero_left (a : ℤ) : 0 + a = a
:= subst (add_zero_right a) (add_comm a 0)

theorem add_nzpos (n m : ℕ) : nzpos n + nzpos m = n + m -- this is nzpos (n + m)
:=
  calc
    nzpos n + nzpos m = prod_sub (tpair n 0) + prod_sub (tpair m 0) : refl _
      ... = prod_sub (map_pair2 nat::add (tpair n 0) (tpair m 0))
              : {add_comp (tpair n 0) (tpair m 0)}
      ... = prod_sub (tpair (n + m) (0 + 0)) : {map_pair2_pair nat::add n 0 m 0}
      ... = prod_sub (tpair (n + m) 0) : {nat::add_zero_right 0}
      ... = n + m : refl (n + m)

theorem add_nzneg (n m : ℕ) : nzneg n + nzneg m = nzneg (n + m)
:=
  calc
    nzneg n + nzneg m = prod_sub (tpair 0 n) + prod_sub (tpair 0 m) : refl _
      ... = prod_sub (map_pair2 nat::add (tpair 0 n) (tpair 0 m))
              : {add_comp (tpair 0 n) (tpair 0 m)}
      ... = prod_sub (tpair (0 + 0) (n + m)) : {map_pair2_pair nat::add 0 n 0 m}
      ... = prod_sub (tpair 0 (n + m)) : {nat::add_zero_right 0}
      ... = nzneg (n + m) : refl (nzneg (n + m))

theorem add_inverse_right (a : ℤ) : a + -a = 0
:=
  have H1 : ∀v : ℕ ## ℕ, rel (map_pair2 nat::add v (flip v)) (tpair 0 0), from
    take v : ℕ ## ℕ,
    calc
      xx (map_pair2 nat::add v (flip v)) + yy (tpair 0 0) = xx v + yy v : by simp
        ... = yy v + xx v : nat::add_comm (xx v) (yy v)
        ... = yy (map_pair2 nat::add v (flip v)) + xx (tpair 0 0) : by simp,
  have H2 : ∀v : ℕ ## ℕ, prod_sub v + -prod_sub v = 0, from
    take v : ℕ ## ℕ,
    calc
      prod_sub v + -prod_sub v = prod_sub (map_pair2 nat::add v (flip v)) : by simp
        ... = 0 : eq_abs quotient (H1 v),
  calc
    a + -a = prod_sub (rep a) + -prod_sub (rep a) : by simp
      ... = 0 : H2 (rep a)

theorem add_inverse_left (a : ℤ) : -a + a = 0
:= subst (add_inverse_right a) (add_comm a (-a))

theorem add_neg_distr (a b : ℤ) : -(a + b) = -a + -b
:=
  have H : ∀v w : ℕ ## ℕ, -(prod_sub v + prod_sub w) = -prod_sub v + -prod_sub w, from
    take v w : ℕ ## ℕ,
    calc
      -(prod_sub v + prod_sub w) = prod_sub (flip (map_pair2 nat::add v w)) : by simp
        ... = prod_sub (map_pair2 nat::add (flip v) (flip w)) : {map_pair2_flip nat::add v w}
        ... = -prod_sub v + -prod_sub w : by simp,
  calc
    -(a + b) = -(prod_sub (rep a) + prod_sub (rep b)) : by simp
      ... = -prod_sub (rep a) + -prod_sub (rep b) : H (rep a) (rep b)
      ... = -a + -b : by simp

---------- inversion theorems for add
theorem add_inj_left {a b c : ℤ} (H : a + b = a + c) : b = c
:=
  have lemma : ∀(u v w : ℕ ## ℕ)
      (K : rel (map_pair2 nat::add u v) (map_pair2 nat::add u w)), rel v w, from
    take (u v w : ℕ ## ℕ), assume K,
    have Hlem : xx u + yy u + (xx v + yy w) = xx u + yy u + (yy v + xx w), from
      calc
        xx u + yy u + (xx v + yy w) = xx u + xx v + (yy u + yy w) : add_switch _ _ _ _
          ... = xx (map_pair2 nat::add u v) + (yy u + yy w)
                  : {symm (map_pair2_xx nat::add u v)}
          ... = xx (map_pair2 nat::add u v) + yy (map_pair2 nat::add u w)
                  : {symm (map_pair2_yy nat::add u w)}
          ... = yy (map_pair2 nat::add u v) + xx (map_pair2 nat::add u w) : K
          ... = yy u + yy v + xx (map_pair2 nat::add u w) : {map_pair2_yy nat::add u v}
          ... = yy u + yy v + (xx u + xx w) : {map_pair2_xx nat::add u w}
          ... = yy u + xx u + (yy v + xx w) : add_switch _ _ _ _
          ... = xx u + yy u + (yy v + xx w) : {nat::add_comm (yy u) (xx u)},
    show rel v w, from nat::add_right_inj Hlem,
  have H2 : prod_sub (map_pair2 nat::add (rep a) (rep b))
          = prod_sub (map_pair2 nat::add (rep a) (rep c)), from
    calc
      prod_sub (map_pair2 nat::add (rep a) (rep b)) = prod_sub (rep a) + prod_sub (rep b)
                : symm (add_comp (rep a) (rep b))
        ... = a + b : by simp
        ... = a + c : H
        ... = prod_sub (rep a) + prod_sub (rep c) : by simp
        ... = prod_sub (map_pair2 nat::add (rep a) (rep c)) : add_comp (rep a) (rep c),
  have H3 : rel (rep b) (rep c),
    from lemma (rep a) (rep b) (rep c) (R_intro_refl quotient rel_refl H2),
  show b = c, from rep_eq quotient H3

theorem add_inj_right {a b c : ℤ} (H : a + b = c + b) : a = c
:= add_inj_left (subst (subst H (add_comm a b)) (add_comm c b))

theorem add_eq_zero_right {a b : ℤ} (H : a + b = 0) : b = -a
:=
  have H2 : a + b = a + -a, from subst H (symm (add_inverse_right a)),
  show b = -a, from add_inj_left H2

theorem add_eq_zero_left {a b : ℤ} (H : a + b = 0) : a = -b
:=
  calc
    a = -(-a) : symm (neg_neg a)
      ... = -b : {symm (add_eq_zero_right H)}

---------- sub
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

theorem sub_zero_right (a : ℤ) : a - nzpos 0 = a
:= substp (fun x, a + x = a) (add_zero_right a) (symm neg_zero)
--this doesn't work without explicit P

theorem sub_zero_left (a : ℤ) : 0 - a = -a
:= add_zero_left (-a)

theorem neg_sub  (a b : ℤ) : -(a - b) = -a + b
:=
  calc
    -(a - b) = -a + -(-b) : add_neg_distr a (-b)
      ... = -a + b : {neg_neg b}

theorem sub_flip (a b : ℤ) : -(a - b) = b - a
:=
  calc
    -(a - b) = -a + b : neg_sub a b
      ... = b - a : add_comm (-a) b

--should the following three theorems be reversed?
theorem sub_add_assoc (a b c : ℤ) : a - (b + c) = a - b - c
:=
  calc
    a - (b + c) = a + (-b + -c) : {add_neg_distr b c}
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
:= subst (add_sub_inverse a b) (add_comm_right a b (-b))

theorem sub_inj_left {a b c : ℤ} (H : a - b = a - c) : b = c
:= neg_inj (add_inj_left H)

theorem sub_inj_right {a b c : ℤ} (H : a - b = c - b) : a = c
:= add_inj_right H

theorem sub_eq_zero {a b : ℤ} (H : a - b = 0) : a = b
:= trans (add_eq_zero_left H) (neg_neg b)

--should some of the equalities below be reversed?
theorem add_imp_sub_right {a b c : ℤ} (H : a + b = c) : a = c - b
:=
  have H2 : a + b = c - b + b, from trans H (symm (sub_add_inverse c b)),
  add_inj_right H2

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


definition le (a b : ℤ) : Bool := ∃n : ℕ, a + n = b
infix  50 <= : le
infix  50 ≤  : le

-- definition le : ℤ → ℤ → Bool := rec_binary quotient (fun a b, xx a + yy b ≤ yy a + xx b)
-- theorem le_comp (u v : ℕ ## ℕ) : (prod_sub u ≤ prod_sub v) ↔ (xx u + yy v ≤ yy u + xx v)
-- :=
--   comp_binary_refl quotient rel_refl
--   (take u u' v v' : ℕ ## ℕ,
--     assume Hu : rel u u',
--     assume Hv : rel v v',

--   u v

-- theorem le_intro {a b : ℤ} {n : ℕ} (H : a + nzpos n = b) : a ≤ b
-- :=
--   have lemma : ∀u v, rel (map_pair2 nat::add u (tpair n 0)) v → xx u + yy v + n = yy u + xx v, from
--     take u v,
--     assume H : rel (map_pair2 nat::add u (tpair n 0)) v,
--     calc
--       xx u + yy v + n = xx u + n + yy v : nat::add_comm_right (xx u) (yy v) n
--         ... = xx (map_pair2 nat::add u (tpair n 0)) + yy v : by simp
--         ... = yy (map_pair2 nat::add u (tpair n 0)) + xx v : H
--         ... = yy u + 0 + xx v : by simp
--         ... = yy u + xx v : {nat::add_zero_right (yy u)},
--   have H2 :

theorem le_intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b
:= exists_intro n H

theorem le_elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b
:= H

set_opaque le true

---------- partial order (totality is part of lt)

theorem le_refl (a : ℤ) : a ≤ a
:= le_intro (add_zero_right a)

theorem le_nzpos (n m : ℕ) : (n ≤ m) ↔ (nzpos n ≤ nzpos m)
:=
  iff_intro
    (assume H : n ≤ m,
      obtain (k : ℕ) (Hk : n + k = m), from nat::le_elim H,
      have H2 : nzpos n + nzpos k = nzpos m, from subst (add_nzpos n k) Hk,
      le_intro H2)
    (assume H : nzpos n ≤ nzpos m,
      obtain (k : ℕ) (Hk : nzpos n + nzpos k = nzpos m), from le_elim H,
      have H2 : n + k = m, from nzpos_inj (trans (symm (add_nzpos n k)) Hk),
      nat::le_intro H2)

theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = c), from le_elim H2,
  have H3 : a + (n + m) = c, from
    calc
      a + (n + m) = a + (nzpos n + m) : {symm (add_nzpos n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = c : Hm,
  le_intro H3

set_option pp::coercion true

theorem le_antisym {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:=
  obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
  obtain (m : ℕ) (Hm : b + m = a), from le_elim H2,
  have H3 : a + (n + m) = a + 0, from
    calc
      a + (n + m) = a + (nzpos n + m) : {symm (add_nzpos n m)}
        ... = a + n + m : symm (add_assoc a n m)
        ... = b + m : {Hn}
        ... = a : Hm
        ... = a + 0 : symm (add_zero_right a),
  have H4 : nzpos (n + m) = nzpos 0, from add_inj_left H3,
  have H5 : n + m = 0, from nzpos_inj H4,
  have H6 : n = 0, from nat::add_eq_zero_left H5,
  show a = b, from
    calc
      a = a + nzpos 0 : symm (add_zero_right a)
        ... = a + n : {symm H6}
        ... = b : Hn


---------- interaction with add

theorem le_add_nzpos_right (a : ℤ) (n : ℕ) : a ≤ a + n
:= le_intro (refl (a + n))

theorem le_add_nzpos_left (a : ℤ) (n : ℕ) : a ≤ n + a
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

theorem add_le_left_inv {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b
:=
  obtain (n : ℕ) (Hn : c + a + n = c + b), from le_elim H,
  have H2 : c + (a + n) = c + b, from
    calc
      c + (a + n) = c + a + n : symm (add_assoc c a n)
        ... = c + b : Hn,
  have H3 : a + n = b, from add_inj_left H2,
  le_intro H3

theorem add_le_right_inv {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b
:= add_le_left_inv (subst (subst H (add_comm a c)) (add_comm b c))

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d
:=
  obtain (n : ℕ) (Hn : c + n = a), from le_elim H2,
  have H3 : c + (n + b) ≤ c + d, from subst (subst H1 (symm Hn)) (add_assoc c n b),
  have H4 : n + b ≤ d, from add_le_left_inv H3,
  show b ≤ d, from le_trans (le_add_nzpos_left b n) H4

-- ---------- interaction with succ and pred

-- theorem succ_le {n m : ℤ} (H : n ≤ m) : succ n ≤ succ m
-- := subst (subst (add_le_right H 1) (add_one n)) (add_one m)

-- theorem succ_le_inv {n m : ℤ} (H : succ n ≤ succ m) :  n ≤ m
-- := add_le_right_inv (subst (subst H (symm (add_one n))) (symm (add_one m)))

-- theorem le_self_succ (n : ℤ) : n ≤ succ n
-- := le_intro (add_one n)

-- theorem succ_le_right {n m : ℤ} (H : n ≤ m) : n ≤ succ m
-- := le_trans H (le_self_succ m)

-- theorem succ_le_left_or {n m : ℤ} (H : n ≤ m) : succ n ≤ m ∨ n = m
-- :=
--   obtain (k : ℤ) (Hk : n + k = m), from (le_elim H),
--   ℤ_discrimiℤe
--     (assume H3 : k = 0,
--       have Heq : n = m,
--         from calc
--           n = n + 0 : symm (add_zero_right n)
--             ... = n + k : {symm H3}
--             ... = m : Hk,
--       or_intro_right _ Heq)
--     (take l:ℤ,
--       assume H3 : k = succ l,
--       have Hlt : succ n ≤ m, from
--         (le_intro
--           (calc
--             succ n + l = n + succ l : add_move_succ n l
--               ... = n + k : {symm H3}
--               ... = m : Hk)),
--       or_intro_left _ Hlt)

-- theorem succ_le_left {n m : ℤ} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m
-- := resolve_left (succ_le_left_or H1) H2

-- theorem succ_le_right_inv {n m : ℤ} (H : n ≤ succ m) : n ≤ m ∨ n = succ m
-- :=
--   or_imp_or (succ_le_left_or H)
--     (take H2 : succ n ≤ succ m, show n ≤ m, from succ_le_inv H2)
--     (take H2 : n = succ m, H2)

-- theorem succ_le_left_inv {n m : ℤ} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m
-- :=
--   obtain (k : ℤ) (H2 : succ n + k = m), from (le_elim H),
--   and_intro
--     (have H3 : n + succ k = m,
--       from calc
--         n + succ k = succ n + k : symm (add_move_succ n k)
--           ... = m : H2,
--       show n ≤ m, from le_intro H3)
--     (not_intro
--       (assume H3 : n = m,
--         have H4 : succ n ≤ n, from subst H (symm H3),
--         have H5 : succ n = n, from le_antisym H4 (le_self_succ n),
--         show false, from absurd H5 (succ_ne_self n)))

-- theorem le_pred_self (n : ℤ) : pred n ≤ n
-- :=
--   ℤ_case n
--     (subst (le_refl 0) (symm pred_zero))
--     (take k : ℤ, subst (le_self_succ k) (symm (pred_succ k)))

-- theorem pred_le {n m : ℤ} (H : n ≤ m) : pred n ≤ pred m
-- :=
--   ℤ_discrimiℤe
--     (take Hn : n = 0,
--       have H2 : pred n = 0,
--         from calc
--           pred n = pred 0 : {Hn}
--              ... = 0 : pred_zero,
--       subst (le_zero (pred m)) (symm H2))
--     (take k : ℤ,
--       assume Hn : n = succ k,
--       obtain (l : ℤ) (Hl : n + l = m), from le_elim H,
--       have H2 : pred n + l = pred m,
--         from calc
--           pred n + l = pred (succ k) + l : {Hn}
--             ... = k + l : {pred_succ k}
--             ... = pred (succ (k + l)) : symm (pred_succ (k + l))
--             ... = pred (succ k + l) : {symm (add_succ_left k l)}
--             ... = pred (n + l) : {symm Hn}
--             ... = pred m : {Hl},
--       le_intro H2)


-- theorem pred_le_left_inv {n m : ℤ} (H : pred n ≤ m) : n ≤ m ∨ n = succ m
-- :=
--   ℤ_discrimiℤe
--     (take Hn : n = 0,
--       or_intro_left _ (subst (le_zero m) (symm Hn)))
--     (take k : ℤ,
--       assume Hn : n = succ k,
--       have H2 : pred n = k,
--         from calc
--           pred n = pred (succ k) : {Hn}
--              ... = k : pred_succ k,
--       have H3 : k ≤ m, from subst H H2,
--       have H4 : succ k ≤ m ∨ k = m, from succ_le_left_or H3,
--       show n ≤ m ∨ n = succ m, from
--         or_imp_or H4
--           (take H5 : succ k ≤ m, show n ≤ m, from subst H5 (symm Hn))
--           (take H5 : k = m, show n = succ m, from subst Hn H5))

-- ---------- interaction with mul

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

end -- namespace int
