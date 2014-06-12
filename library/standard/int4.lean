
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

--theorem int_inhabited : inhabited int
--:= subtype_inhabited (proj (tpair 0 0)) (exists_intro (tpair 0 0) (refl _))

definition prod_sub : ℕ ## ℕ → ℤ := fun_image proj
definition rep : ℤ → ℕ ## ℕ := subtype::rep

--theorem int_inhabited : inhabited int
--:= image_inhabited2 proj (tpair 0 0)

theorem quotient : @is_quotient _ int rel prod_sub rep
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

set_opaque int true
set_opaque prod_sub true
set_opaque proj true

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


definition le : ℤ → ℤ → Bool := rec_binary quotient (fun a b, xx a + yy b ≤ yy a + xx b)



--- everything below still needs to be implemented

-- definition abs (z : int) : nat := rec (fun n : nat, n) (fun n : nat, succ n) z

-- theorem nzpos_ne_nzneg (n m : nat) : nzpos n ≠ nzneg m
-- :=

-- theorem abs_pos (n:nat) : abs (pos n) = n
-- := rec_pos _ _ _
-- theorem abs_neg (n:nat) : abs (neg n) = succ n
-- := rec_neg _ _ _

-- theorem pos_inj {n m:nat} (H : pos n = pos m) : n = m
-- :=
--   calc
--     n = abs (pos n) : {symm (abs_pos n)}
--   ... = abs (pos m) : {H}
--   ... = m : {abs_pos m}

-- theorem neg_inj {n m:nat} (H : neg n = neg m) : n = m
-- :=
--   calc
--     n = pred (succ n) : symm (pred_succ n)
--   ... = pred (abs (neg n)) : {symm (abs_neg n)}
--   ... = pred (abs (neg m)) : {H}
--   ... = pred (succ m) : {abs_neg m}
--   ... = m : pred_succ m

-- -------------------------------------------------- add sub

-- -- the function λnm, n - succ m : nat → nat → int
-- definition nz_sub (n m : nat) : int := if (n > m) then pred (n - m) else neg (m - n)

-- theorem nz_sub_ge {n m : nat} (H : n > m) : nz_sub n m = pred (n - m)
-- :=
--   calc
--     nz_sub n m = if true then pred (n - m) else neg (m - n) : {eqt_intro H}
--       ... = pred (n - m) : if_true _ _

-- theorem nz_sub_lt {n m : nat} (H : n ≤ m) : nz_sub n m = neg (m - n)
-- :=
--   calc
--     nz_sub n m = if false then pos (pred (n - m)) else neg (m - n) : {eqf_intro (le_lt_antisym H)}
--       ... = neg (m - n) : if_false _ _

-- theorem add_pos_neg (n m : nat) : pos n + neg m = nz_sub n m
-- := trans (rec_neg _ _ m) (rec_pos _ _ n)

-- theorem add_neg_pos (n m : nat) : neg n + pos m = nz_sub m n
-- := trans (rec_pos _ _ m) (rec_neg _ _ n)

end -- namespace int
