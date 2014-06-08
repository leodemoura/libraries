
----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import nat
import macros
import subtype

-- for kernel?
theorem eq_hcongr2 {A B : (Type U)} {a b : A} (f : A → B) (H : a = b) : f a == f b
:= subst (congr2 f H) (symm (heq_eq (f a) (f b)))

theorem and_inhabited_left {a : Bool} (b : Bool) (H : a) : a ∧ b ↔ b
:=
  have H2 : a = true, from eqt_intro H,
  subst (and_true_left b) (symm H2)

-- relations

definition reflexive {A : Type} (R : A → A → Bool) : Bool := ∀a, R a a
definition transitive {A : Type} (R : A → A → Bool) : Bool := ∀a b c, R a b → R b c → R a c
definition symmetric {A : Type} (R : A → A → Bool) : Bool := ∀a b, R a b → R b a
definition equivalence {A : Type} (R : A → A → Bool) : Bool
:= reflexive R ∧ symmetric R ∧ transitive R
definition PER {A : Type} (R : A → A → Bool) : Bool := symmetric R ∧ transitive R

definition equiv_imp_PER {A : Type} {R : A → A → Bool} (H : equivalence R) : PER R
:= and_intro (and_elim_left (and_elim_right H)) (and_elim_right (and_elim_right H))


-- pairs

alias xx : tproj1
alias yy : tproj2

definition flip {A B : Type} (a : A ## B) : B ## A := tpair (yy a) (xx a)

theorem flip_pair {A B : Type} (a : A) (b : B) : flip (tpair a b) = tpair b a
:=
  calc
    flip (tpair a b) = tpair b (xx (tpair a b)) : {tproj2_tpair _ _}
      ... = tpair b a : {tproj1_tpair _ _}

theorem flip_xx {A B : Type} (a : A ## B) : xx (flip a) = yy a
:= tproj1_tpair (yy a) (xx a)

theorem flip_yy {A B : Type} (a : A ## B) : yy (flip a) = xx a
:= tproj2_tpair (yy a) (xx a)

theorem flip_flip {A B : Type} (a : A ## B) : flip (flip a) = a
:=
  calc
    flip (flip a) = tpair (xx a) (yy a) : flip_pair (yy a) (xx a)
      ... = a : tpair_tproj_eq a

theorem P_flip {A B : Type} {P : A → B → Bool} {a : A ## B} (H : P (xx a) (yy a))
    : P (yy (flip a)) (xx (flip a))
:= subst (subst H (symm (flip_xx a))) (symm (flip_yy a))

theorem flip_inj {A B : Type} {a b : A ## B} (H : flip a = flip b) : a = b
:=
  have H2 : flip (flip a) = flip (flip b), from congr2 flip H,
  show a = b, from subst (subst H2 (flip_flip a)) (flip_flip b)

set_opaque flip true

-------------------------------------------------- quotients

namespace quot
using subtype

---------- definition and basics

definition is_quotient {A B : Type} (R : A → A → Bool) (abs : A → B) (rep : B → A) : Bool
:=
  (∀b, abs (rep b) = b) ∧
  (∀b, R (rep b) (rep b)) ∧
  (∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s))

theorem quotient_intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : ∀b, abs (rep b) = b) (H2 : ∀b, R (rep b) (rep b))
    (H3 : ∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)) : is_quotient R abs rep
:= and_intro H1 (and_intro H2 H3)

theorem quotient_intro_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
    (H3 : ∀r s, R r s ↔ abs r = abs s) : is_quotient R abs rep
:=
  quotient_intro
    H2
    (take b, H1 (rep b))
    (take r s,
      have H4 : R r s ↔ R s s ∧ abs r = abs s,
        from subst (H3 r s) (symm (and_inhabited_left _ (H1 s))),
      subst H4 (symm (and_inhabited_left _ (H1 r))))

theorem quotient_abs_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (b : B) :  abs (rep b) = b
:= and_elim_left Q b

theorem quotient_refl_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (b : B) : R (rep b) (rep b)
:= and_elim_left (and_elim_right Q) b

theorem quotient_R_iff {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (r s : A) : R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)
:= and_elim_right (and_elim_right Q) r s

theorem quotient_refl_left {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R r r
:= and_elim_left (iff_elim_left (quotient_R_iff Q r s) H)

theorem quotient_refl_right {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R s s
:= and_elim_left (and_elim_right (iff_elim_left (quotient_R_iff Q r s) H))

theorem quotient_eq_abs {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : abs r = abs s
:= and_elim_right (and_elim_right (iff_elim_left (quotient_R_iff Q r s) H))

theorem quotient_R_intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H1 : R r r) (H2 : R s s) (H3 : abs r = abs s) : R r s
:= iff_elim_right (quotient_R_iff Q r s) (and_intro H1 (and_intro H2 H3))

theorem quotient_R_intro_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (H1 : reflexive R) {r s : A} (H2 : abs r = abs s) : R r s
:= iff_elim_right (quotient_R_iff Q r s) (and_intro (H1 r) (and_intro (H1 s) H2))

---------- recursion

definition quotient_rec {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
--    (H : forall (r s : A) (H' : R r s),
--        cast (eq_hcongr2 C (quotient_eq_abs Q H')) (f r) = f s)
    (b : B) : C b
:= cast (eq_hcongr2 C (quotient_abs_rep Q b)) (f (rep b))

theorem quotient_comp {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a))
    (H1 : forall (r s : A) (H' : R r s),
        cast (eq_hcongr2 C (quotient_eq_abs Q H')) (f r) = f s)
    {a : A} (H2 : R a a) : quotient_rec Q f (abs a) = f a
:=
  have H3 : abs a = abs (rep (abs a)), from symm (quotient_abs_rep Q (abs a)),
  have H4 : R a (rep (abs a)),
    from quotient_R_intro Q H2 (quotient_refl_rep Q (abs a)) H3,
  calc
    quotient_rec Q f (abs a) = cast _ (f (rep (abs a))) : refl _
      ... = cast _ (cast _ (f a)) : {symm (H1 _ _ H4)}
      ... = cast _ (f a) : cast_trans _ _ _
      ... = f a : cast_eq _ _

definition quotient_rec2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} (f : A → C)
--    (H : forall (r s : A) (H' : R r s), f r = f s)
    (b : B) : C
:= f (rep b)

theorem quotient_comp2 {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} (f : A → C)
    (H1 : forall (r s : A) (H' : R r s), f r = f s)
    {a : A} (H2 : R a a) : quotient_rec2 Q f (abs a) = f a
:=
  have H3 : abs a = abs (rep (abs a)), from symm (quotient_abs_rep Q (abs a)),
  have H4 : R a (rep (abs a)),
    from quotient_R_intro Q H2 (quotient_refl_rep Q (abs a)) H3,
  -- congr2 f (symm (H1 _ _ H4)) -- this gives strange error
  calc
    quotient_rec2 Q f (abs a) = f (rep (abs a)) : refl _
      ... = f a : {symm (H1 _ _ H4)}

---------- image

definition image {A B : Type} (f : A → B) := subtype B (fun b, ∃a, f a = b)

theorem image_inhabited {A B : Type} (f : A → B) (H : inhabited A) : inhabited (image f)
:= inhabited_elim H (take a : A, subtype_inhabited (f a) (exists_intro a (refl (f a))))

theorem image_inhabited2 {A B : Type} (f : A → B) (a : A) : inhabited (image f)
:= image_inhabited f (inhabited_intro a)

definition fun_image {A B : Type} (f : A → B) (a : A) : image f
:= abst (f a) (image_inhabited2 f a)

theorem fun_image_def {A B : Type} (f : A → B) (a : A)
    : fun_image f a = abst (f a) (image_inhabited2 f a)
:= refl _

theorem rep_fun_image {A B : Type} (f : A → B) (a : A) : rep (fun_image f a) = f a
:= rep_abst (image_inhabited2 f a) (f a) (exists_intro a (refl (f a)))

theorem image_rep {A B : Type} (f : A → B) (b : image f) : ∃a, f a = rep b
:= P_rep b

theorem fun_image_eq {A B : Type} (f : A → B) (a b : A)
    : (f a = f b) ↔ (fun_image f a = fun_image f b)
:=
  iff_intro
    (assume H : f a = f b,
      have H2 : image_inhabited2 f a = image_inhabited2 f b, from proof_irrel _ _,
      congr (congr2 abst H) H2)
    (assume H : fun_image f a = fun_image f b,
      subst (subst (congr2 rep H) (rep_fun_image f a)) (rep_fun_image f b))

---------- construct quotient from representative map

theorem representative_map_idempotent {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
    : f (f a) = f a
:= symm (and_elim_right (and_elim_right (iff_elim_left (H2 a (f a)) (H1 a))))

theorem representative_map_refl_rep {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
    : R (f a) (f a)
:=  subst (H1 (f a)) (representative_map_idempotent R H1 H2 a)

-- this theorem fails if it's not given explicitly that "image f" is the "B"
theorem representative_map_to_quotient {A : Type} {R : A → A → Bool} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b)
    : @is_quotient A (image f) R (fun_image f) rep
:= let abs := fun_image f in
  @quotient_intro A (image f) R abs rep
   (take b : image f,
      show abs (rep b) = b, from
       obtain (a : A) (Ha : f a = rep b), from image_rep f b,
      calc
        abs (rep b) = abs (f a) : {symm Ha}
          ... = abst (f a) (image_inhabited2 f (f a)) :
                          {@representative_map_idempotent A R f H1 H2 a}
          ... = abst (rep b) (image_inhabited2 f (f a)) : {Ha}
          ... = b : abst_rep (image_inhabited2 f (f a)) b)
   (take b : image f,
     show R (rep b) (rep b), from
     obtain (a : A) (Ha : f a = rep b), from image_rep f b,
     subst (@representative_map_refl_rep A R f H1 H2 a) Ha)
    (take a b, subst (H2 a b) (fun_image_eq f a b))

theorem representative_map_equiv_inj {A : Type} {R : A → A → Bool}
    (equiv : equivalence R) {f : A → A} (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b)
    {a b : A} (H3 : f a = f b) : R a b
:=
  have symmR : symmetric R, from and_elim_left (and_elim_right equiv),
  have transR : transitive R, from and_elim_right (and_elim_right equiv),
  show R a b, from
    have H2 : R a (f b), from subst (H1 a) H3,
    have H3 : R (f b) b, from symmR _ _ (H1 b),
    transR _ _ _ H2 H3

theorem representative_map_to_quotient_equiv {A : Type} {R : A → A → Bool}
    (equiv : equivalence R) {f : A → A} (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b)
    : @is_quotient A (image f) R (fun_image f) rep
:=
  representative_map_to_quotient
    H1
    (take a b,
      have reflR : reflexive R, from and_elim_left equiv,
      have H3 : f a = f b → R a b, from representative_map_equiv_inj equiv H1 H2,
      have H4 : R a b ↔ f a = f b, from iff_intro (H2 a b) H3,
      have H5 : R a b ↔ R b b ∧ f a = f b,
        from subst H4 (symm (and_inhabited_left _ (reflR b))),
      subst H5 (symm (and_inhabited_left _ (reflR a))))

---------- abstract quotient

definition prelim_quotient_map {A : Type} (R : A → A → Bool) (a : A)
:= ε (inhabited_intro a) (fun b, R a b)

--only needed R reflexive (or weaker: R a a)
theorem prelim_quotient_map_rel {A : Type} {R : A → A → Bool} (H : equivalence R) (a : A)
    : R a (prelim_quotient_map R a)
:=
  have reflR : reflexive R, from and_elim_left H,
  eps_ax (inhabited_intro a) a (reflR a)

-- only needed: R PER
theorem prelim_quotient_map_congr {A : Type} {R : A → A → Bool} (H1 : equivalence R) {a b : A}
    (H2 : R a b) : prelim_quotient_map R a = prelim_quotient_map R b
:=
  have symm : symmetric R, from and_elim_left (and_elim_right H1),
  have trans : transitive R, from and_elim_right (and_elim_right H1),
  have H3 : ∀c, R a c ↔ R b c, from
    take c,
      iff_intro
        (assume H4 : R a c, trans b a c (symm a b H2) H4)
        (assume H4 : R b c, trans a b c H2 H4),
  have H4 : (fun c, R a c) = (fun c, R b c), from funext H3,
  congr (congr2 ε (proof_irrel (inhabited_intro a) (inhabited_intro b))) H4

definition quotient {A : Type} (R : A → A → Bool) : Type := image (prelim_quotient_map R)

definition quotient_map {A : Type} (R : A → A → Bool) : A → quotient R
:= fun_image (prelim_quotient_map R)

definition quotient_rep {A : Type} (R : A → A → Bool) : quotient R → A := rep

theorem quotient_is_quotient  {A : Type} (R : A → A → Bool) (H1 : equivalence R)
    : is_quotient R (quotient_map R) (quotient_rep R)
:=
  representative_map_to_quotient_equiv
    H1
    (prelim_quotient_map_rel H1)
    (@prelim_quotient_map_congr _ _ H1)

set_opaque quotient_rec true
set_opaque is_quotient true

end -- namespace quot

-------------------------------------------------- axioms int


namespace int
using nat
using quot
using subtype
unary_nat

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

definition int := image proj
alias ℤ : int

--theorem int_inhabited : inhabited int
--:= image_inhabited2 proj (tpair 0 0)

theorem quotient : @is_quotient _ int rel (fun_image proj) rep -- note: rep is subtype::rep
:=
  representative_map_to_quotient_equiv rel_equiv proj_rel @proj_congr

definition pos (n : ℕ) : ℤ := (fun_image proj) (tpair n 0)
coercion pos
definition neg (n : ℕ) : ℤ := (fun_image proj) (tpair 0 n)

--- everything below still needs to be changed

-- axiom rec {P : ℤ → Type} (f : ∀n : nat, P (pos n)) (g : ∀n : nat, P (neg n)) (z : ℤ) : P z
-- axiom rec_pos {P : ℤ → Type} (f : ∀n : nat, P (pos n))
--     (g : ∀n : nat, P (neg n)) (n : nat) :  rec f g (pos n) = f n
-- axiom rec_neg {P : ℤ → Type} (f : ∀n : nat, P (pos n))
--     (g : ∀n : nat, P (neg n)) (n : nat) :  rec f g (neg n) = g n


-- -------------------------------------------------- basics

-- theorem induction {P : ℤ → Bool} (z : ℤ) (Hp : ∀n : nat, P (pos n))
--     (Hn : ∀n : nat, P (neg n)) : P z
-- := rec Hp Hn z

-- theorem pos_ne_neg (n m : nat) : pos n ≠ neg m
-- :=
--   not_intro
--     (take H : pos n = neg m,
--       have H2 : true = false, from
--         (let f : int → Bool := (rec (fun a,true) (fun b, false))
--           in calc
--             true = f (pos n) : symm (rec_pos _ _ _)
--              ... = f (neg m) : {H}
-- 	           ... = false : rec_neg _ _ _),
--       absurd H2 true_ne_false)

-- theorem cases (z : int) : (exists n, z = pos n) ∨ (exists n, z = neg n)
-- :=
--   induction z
--     (take n, or_intro_left _ (exists_intro n (refl _)))
--     (take n, or_intro_right _ (exists_intro n (refl _)))

-- theorem discriminate {B : Bool} {z : int} (Hp : ∀n, z = pos n → B)
--     (Hn : ∀n, z = neg n → B) : B
-- :=
--   or_elim (cases z)
--     (take H, obtain (n : nat) (Hz : z = pos n), from H, Hp n Hz)
--     (take H, obtain (n : nat) (Hz : z = neg n), from H, Hn n Hz)

-- definition abs (z : int) : nat := rec (fun n : nat, n) (fun n : nat, succ n) z

-- theorem abs_pos (n:nat) : abs (pos n) = n
-- := rec_pos _ _ _
-- theorem abs_neg (n:nat) : abs (neg n) = succ n
-- := rec_neg _ _ _

-- set_opaque abs true

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

-- definition add (z w : int) : int :=
--   rec
--     (take m : nat, rec
--       (take n : nat, pos (n + m))
--       (take n : nat, nz_sub m n) z)
--     (take m : nat, rec
--       (take n : nat, nz_sub n m)
--       (take n : nat, neg (succ (n + m))) z) w

-- infixl 65 + : int::add

-- theorem add_pos_pos (n m : nat) : pos n + pos m = pos (n + m)
-- := trans (rec_pos _ _ m) (rec_pos _ _ n)

-- theorem add_pos_neg (n m : nat) : pos n + neg m = nz_sub n m
-- := trans (rec_neg _ _ m) (rec_pos _ _ n)

-- theorem add_neg_pos (n m : nat) : neg n + pos m = nz_sub m n
-- := trans (rec_pos _ _ m) (rec_neg _ _ n)

-- theorem add_neg_neg (n m : nat) : neg n + neg m = neg (succ (n + m))
-- := trans (rec_neg _ _ m) (rec_neg _ _ n)

-- theorem add_comm (a b : int) : a + b = b + a
-- :=
--   induction a
--     (take n, induction b
--       (take m,  calc
--          pos n + pos m = pos (n + m) : add_pos_pos n m
--            ... = pos (m + n) : {add_comm n m}
--            ... = pos m + pos n : symm (add_pos_pos m n))
--       (take m, trans (add_pos_neg n m) (symm (add_neg_pos m n))))
--     (take n, induction b
--       (take m, trans (add_neg_pos n m) (symm (add_pos_neg m n)))
--       (take m, calc
--          neg n + neg m = neg (succ (n + m)) : add_neg_neg n m
--            ... = neg (succ (m + n)) : {add_comm n m}
--            ... = neg m + neg n : symm (add_neg_neg m n)))

-- -- theorem add_assoc (a b c : int) : a + b + c = a + (b + c)
-- -- := _

end -- namespace int
