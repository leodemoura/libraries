----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import macros tactic subtype

-- for kernel?

theorem eq_hcongr2 {A B : (Type U)} {a b : A} (f : A → B) (H : a = b) : f a == f b
:= subst (congr2 f H) (symm (heq_eq (f a) (f b)))

theorem and_inhabited_left {a : Bool} (b : Bool) (H : a) : a ∧ b ↔ b
:=
  have H2 : a = true, from eqt_intro H,
  subst (and_true_left b) (symm H2)


-- ## Relations

definition reflexive {A : Type} (R : A → A → Bool) : Bool := ∀a, R a a
definition symmetric {A : Type} (R : A → A → Bool) : Bool := ∀a b, R a b → R b a
definition transitive {A : Type} (R : A → A → Bool) : Bool := ∀a b c, R a b → R b c → R a c
definition PER {A : Type} (R : A → A → Bool) : Bool := symmetric R ∧ transitive R
definition equivalence {A : Type} (R : A → A → Bool) : Bool
:= reflexive R ∧ PER R

theorem equivalence_intro {A : Type} {R : A → A → Bool} (H1 : reflexive R) (H2 : symmetric R)
    (H3 : transitive R) : equivalence R
:= and_intro H1 (and_intro H2 H3)

theorem equiv_imp_PER {A : Type} {R : A → A → Bool} (H : equivalence R) : PER R
:= and_elim_right H


-- ## More on pairs

alias xx : tproj1
alias yy : tproj2

-- ### flip

definition flip {A B : Type} (a : A ## B) : B ## A := tpair (yy a) (xx a)

theorem flip_def {A B : Type} (a : A ## B) : flip a = tpair (yy a) (xx a)
:= refl (flip a)

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

-- ### coordinatewise unary maps

definition map_pair {A B : Type} (f : A → B) (a : A ## A) : B ## B
:= tpair (f (xx a)) (f (yy a))

theorem map_pair_def {A B : Type} (f : A → B) (a : A ## A)
    : map_pair f a = tpair (f (xx a)) (f (yy a))
:= refl _

theorem map_pair_pair {A B : Type} (f : A → B) (a a' : A)
    : map_pair f (tpair a a') = tpair (f a) (f a')
:= subst (subst (refl _) (tproj2_tpair a a')) (tproj1_tpair a a')

theorem map_pair_xx {A B : Type} (f : A → B) (a : A ## A) : xx (map_pair f a) = f (tproj1 a)
:= tproj1_tpair _ _

theorem map_pair_yy {A B : Type} (f : A → B) (a : A ## A) : yy (map_pair f a) = f (tproj2 a)
:= tproj2_tpair _ _

-- ### coordinatewise binary maps

definition map_pair2 {A B C : Type} (f : A → B → C) (a : A ## A) (b : B ## B) : C ## C
:= tpair (f (xx a) (tproj1 b)) (f (yy a) (tproj2 b))

theorem map_pair2_def {A B C : Type} (f : A → B → C) (a : A ## A) (b : B ## B)
    : map_pair2 f a b = tpair (f (xx a) (tproj1 b)) (f (yy a) (tproj2 b))
:= refl _

theorem map_pair2_pair {A B C : Type} (f : A → B → C) (a a' : A) (b b' : B)
    : map_pair2 f (tpair a a') (tpair b b') = tpair (f a b) (f a' b')
:=
  calc
    map_pair2 f (tpair a a') (tpair b b')
          = tpair (f (xx (tpair a a')) b) (f (yy (tpair a a')) (tproj2 (tpair b b')))
              : {tproj1_tpair b b'}
      ... = tpair (f (xx (tpair a a')) b) (f (yy (tpair a a')) b') : {tproj2_tpair b b'}
      ... = tpair (f (xx (tpair a a')) b) (f a' b') : {tproj2_tpair a a'}
      ... = tpair (f a b) (f a' b') : {tproj1_tpair a a'}

theorem map_pair2_xx {A B C : Type} (f : A → B → C) (a : A ## A) (b : B ## B)
    : xx (map_pair2 f a b) = f (tproj1 a) (tproj1 b)
:= tproj1_tpair _ _

theorem map_pair2_yy {A B C : Type} (f : A → B → C) (a : A ## A) (b : B ## B)
    : yy (map_pair2 f a b) = f (tproj2 a) (tproj2 b)
:= tproj2_tpair _ _

theorem map_pair2_flip {A B C : Type} (f : A → B → C) (a : A ## A) (b : B ## B)
    : flip (map_pair2 f a b) = map_pair2 f (flip a) (flip b)
:=
  have Hx : xx (flip (map_pair2 f a b)) =  xx (map_pair2 f (flip a) (flip b)), from
    calc
      xx (flip (map_pair2 f a b)) = yy (map_pair2 f a b) : flip_xx _
        ... = f (tproj2 a) (tproj2 b) : map_pair2_yy f a b
        ... = f (tproj1 (flip a)) (tproj2 b) : {symm (flip_xx a)}
        ... = f (tproj1 (flip a)) (tproj1 (flip b)) : {symm (flip_xx b)}
        ... = xx (map_pair2 f (flip a) (flip b)) : symm (map_pair2_xx f _ _),
  have Hy : yy (flip (map_pair2 f a b)) =  yy (map_pair2 f (flip a) (flip b)), from
    calc
      yy (flip (map_pair2 f a b)) = xx (map_pair2 f a b) : flip_yy _
        ... = f (tproj1 a) (tproj1 b) : map_pair2_xx f a b
        ... = f (tproj2 (flip a)) (tproj1 b) : {symm (flip_yy a)}
        ... = f (tproj2 (flip a)) (tproj2 (flip b)) : {symm (flip_yy b)}
        ... = yy (map_pair2 f (flip a) (flip b)) : symm (map_pair2_yy f _ _),
  tpairext Hx Hy

add_rewrite flip_xx flip_yy flip_pair
add_rewrite map_pair_xx map_pair_yy map_pair_pair
add_rewrite map_pair2_xx map_pair2_yy map_pair2_pair

theorem map_pair2_comm {A B : Type} {f : A → A → B} (Hcomm : ∀a b : A, f a b = f b a)
    (v w : A ## A) : map_pair2 f v w = map_pair2 f w v
:=
  have Hx : xx (map_pair2 f v w) = xx (map_pair2 f w v), from
    calc
      xx (map_pair2 f v w) = f (tproj1 v) (tproj1 w) : map_pair2_xx f v w
        ... = f (tproj1 w) (tproj1 v) : Hcomm _ _
        ... = xx (map_pair2 f w v) : symm (map_pair2_xx f w v),
  have Hy : yy (map_pair2 f v w) = yy (map_pair2 f w v), from
    calc
      yy (map_pair2 f v w) = f (tproj2 v) (tproj2 w) : map_pair2_yy f v w
        ... = f (tproj2 w) (tproj2 v) : Hcomm _ _
        ... = yy (map_pair2 f w v) : symm (map_pair2_yy f w v),
  tpairext Hx Hy

theorem map_pair2_assoc {A : Type} {f : A → A → A}
    (Hassoc : ∀a b c : A, f (f a b) c = f a (f b c)) (u v w : A ## A)
    : map_pair2 f (map_pair2 f u v) w = map_pair2 f u (map_pair2 f v w)
:=
  have Hx : xx (map_pair2 f (map_pair2 f u v) w) =
            xx (map_pair2 f u (map_pair2 f v w)), from
    calc
       xx (map_pair2 f (map_pair2 f u v) w)
            = f (xx (map_pair2 f u v)) (xx w) : map_pair2_xx f _ _
        ... = f (f (xx u) (xx v)) (xx w) : {map_pair2_xx f _ _}
        ... = f (xx u) (f (xx v) (xx w)) : Hassoc (xx u) (xx v) (xx w)
        ... = f (xx u) (xx (map_pair2 f v w)) : {symm (map_pair2_xx f _ _)}
        ... = xx (map_pair2 f u (map_pair2 f v w)) : symm (map_pair2_xx f _ _),
  have Hy : yy (map_pair2 f (map_pair2 f u v) w) =
            yy (map_pair2 f u (map_pair2 f v w)), from
    calc
       yy (map_pair2 f (map_pair2 f u v) w)
            = f (yy (map_pair2 f u v)) (yy w) : map_pair2_yy f _ _
        ... = f (f (yy u) (yy v)) (yy w) : {map_pair2_yy f _ _}
        ... = f (yy u) (f (yy v) (yy w)) : Hassoc (yy u) (yy v) (yy w)
        ... = f (yy u) (yy (map_pair2 f v w)) : {symm (map_pair2_yy f _ _)}
        ... = yy (map_pair2 f u (map_pair2 f v w)) : symm (map_pair2_yy f _ _),
  tpairext Hx Hy

theorem map_pair2_id_right {A B : Type} {f : A → B → A} {e : B} (Hid : ∀a : A, f a e = a)
    (v : A ## A) : map_pair2 f v (tpair e e) = v
:=
  have Hx : xx (map_pair2 f v (tpair e e)) = xx v, from
     calc
      xx (map_pair2 f v (tpair e e)) = f (tproj1 v) (tproj1 (tpair e e)) : by simp
        ... = f (tproj1 v) e : by simp
        ... = tproj1 v : Hid (tproj1 v),
  have Hy : yy (map_pair2 f v (tpair e e)) = yy v, from
     calc
      yy (map_pair2 f v (tpair e e)) = f (tproj2 v) (tproj2 (tpair e e)) : by simp
        ... = f (tproj2 v) e : by simp
        ... = tproj2 v : Hid (tproj2 v),
  tpairext Hx Hy

theorem map_pair2_id_left {A B : Type} {f : B → A → A} {e : B} (Hid : ∀a : A, f e a = a)
    (v : A ## A) : map_pair2 f (tpair e e) v = v
:=
  have Hx : xx (map_pair2 f (tpair e e) v) = xx v, from
     calc
      xx (map_pair2 f (tpair e e) v) = f (tproj1 (tpair e e)) (tproj1 v) : by simp
        ... = f e (tproj1 v) : by simp
        ... = tproj1 v : Hid (tproj1 v),
  have Hy : yy (map_pair2 f (tpair e e) v) = yy v, from
     calc
      yy (map_pair2 f (tpair e e) v) = f (tproj2 (tpair e e)) (tproj2 v) : by simp
        ... = f e (tproj2 v) : by simp
        ... = tproj2 v : Hid (tproj2 v),
  tpairext Hx Hy


set_opaque flip true
set_opaque map_pair true
set_opaque map_pair2 true

-- Theory quot
-- ===========

namespace quot
using subtype

-- definition and basics
-- ---------------------

definition is_quotient {A B : Type} (R : A → A → Bool) (abs : A → B) (rep : B → A) : Bool
:=
  (∀b, abs (rep b) = b) ∧
  (∀b, R (rep b) (rep b)) ∧
  (∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s))

theorem intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : ∀b, abs (rep b) = b) (H2 : ∀b, R (rep b) (rep b))
    (H3 : ∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)) : is_quotient R abs rep
:= and_intro H1 (and_intro H2 H3)

theorem intro_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
    (H3 : ∀r s, R r s ↔ abs r = abs s) : is_quotient R abs rep
:=
  intro
    H2
    (take b, H1 (rep b))
    (take r s,
      have H4 : R r s ↔ R s s ∧ abs r = abs s,
        from subst (H3 r s) (symm (and_inhabited_left _ (H1 s))),
      subst H4 (symm (and_inhabited_left _ (H1 r))))

theorem abs_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (b : B) :  abs (rep b) = b
:= and_elim_left Q b

theorem refl_rep {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (b : B) : R (rep b) (rep b)
:= and_elim_left (and_elim_right Q) b

theorem R_iff {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (r s : A) : R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)
:= and_elim_right (and_elim_right Q) r s

theorem refl_left {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R r r
:= and_elim_left (iff_elim_left (R_iff Q r s) H)

theorem refl_right {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R s s
:= and_elim_left (and_elim_right (iff_elim_left (R_iff Q r s) H))

theorem eq_abs {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H : R r s) : abs r = abs s
:= and_elim_right (and_elim_right (iff_elim_left (R_iff Q r s) H))

theorem R_intro {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {r s : A} (H1 : R r r) (H2 : R s s) (H3 : abs r = abs s) : R r s
:= iff_elim_right (R_iff Q r s) (and_intro H1 (and_intro H2 H3))

theorem R_intro_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (H1 : reflexive R) {r s : A} (H2 : abs r = abs s) : R r s
:= iff_elim_right (R_iff Q r s) (and_intro (H1 r) (and_intro (H1 s) H2))

theorem rep_eq {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {a b : B} (H : R (rep a) (rep b)) : a = b
:=
  calc
    a = abs (rep a) : symm (abs_rep Q a)
      ... = abs (rep b) : {eq_abs Q H}
      ... = b : abs_rep Q b

theorem R_rep_abs {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {a : A} (H : R a a) : R a (rep (abs a))
:=
  have H3 : abs a = abs (rep (abs a)), from symm (abs_rep Q (abs a)),
  R_intro Q H (refl_rep Q (abs a)) H3

theorem quotient_imp_symm {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) : symmetric R
:=
  take a b : A,
  assume H : R a b,
  have Ha : R a a, from refl_left Q H,
  have Hb : R b b, from refl_right Q H,
  have Hab : abs b = abs a, from symm (eq_abs Q H),
  R_intro Q Hb Ha Hab

theorem quotient_imp_trans {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) : transitive R
:=
  take a b c : A,
  assume Hab : R a b,
  assume Hbc : R b c,
  have Ha : R a a, from refl_left Q Hab,
  have Hc : R c c, from refl_right Q Hbc,
  have Hac : abs a = abs c, from trans (eq_abs Q Hab) (eq_abs Q Hbc),
  R_intro Q Ha Hc Hac

-- recursion
-- ---------

-- (maybe some are superfluous)

definition rec {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a)) (b : B) : C b
:= cast (eq_hcongr2 C (abs_rep Q b)) (f (rep b))

theorem comp {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : B → Type} {f : forall (a : A), C (abs a)}
    (H : forall (r s : A) (H' : R r s),
        cast (eq_hcongr2 C (eq_abs Q H')) (f r) = f s)
    {a : A} (Ha : R a a) : rec Q f (abs a) = f a
:=
  have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
  calc
    rec Q f (abs a) = cast _ (f (rep (abs a))) : refl _
      ... = cast _ (cast _ (f a)) : {symm (H _ _ H2)}
      ... = cast _ (f a) : cast_trans _ _ _
      ... = f a : cast_eq _ _

definition rec_constant {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} (f : A → C) (b : B) : C
:= f (rep b)

theorem comp_constant {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} {f : A → C}
    (H : forall (r s : A) (H' : R r s), f r = f s)
    {a : A} (Ha : R a a) : rec_constant Q f (abs a) = f a
:=
  have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
  -- congr2 f (symm (H1 _ _ H4)) -- this gives strange error
  calc
    rec_constant Q f (abs a) = f (rep (abs a)) : refl _
      ... = f a : {symm (H _ _ H2)}

definition rec_binary {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} (f : A → A → C) (b c : B) : C
:= f (rep b) (rep c)

theorem comp_binary {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {C : Type} {f : A → A → C}
    (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), f a b = f a' b')
    {a b : A} (Ha : R a a) (Hb : R b b) : rec_binary Q f (abs a) (abs b) = f a b
:=
  have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
  have H3 : R b (rep (abs b)), from R_rep_abs Q Hb,
  calc
    rec_binary Q f (abs a) (abs b) = f (rep (abs a))  (rep (abs b)) : refl _
      ... = f a b : {symm (H _ _ _ _ H2 H3)}

theorem comp_binary_refl {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (Hrefl : reflexive R) {C : Type} {f : A → A → C}
    (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), f a b = f a' b')
    (a b : A) : rec_binary Q f (abs a) (abs b) = f a b
:= comp_binary Q H (Hrefl a) (Hrefl b)

definition quotient_map {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (f : A → A) (b : B) : B
:= abs (f (rep b))

theorem comp_quotient_map {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {f : A → A}
    (H : forall (a a' : A) (Ha : R a a'), R (f a) (f a'))
    {a : A} (Ha : R a a) : quotient_map Q f (abs a) = abs (f a)
:=
  have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
  have H3 : R (f a) (f (rep (abs a))), from H _ _ H2,
  have H4 : abs (f a) = abs (f (rep (abs a))), from eq_abs Q H3,
  symm H4

definition quotient_map_binary {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) (f : A → A → A) (b c : B) : B
:= abs (f (rep b) (rep c))

theorem comp_quotient_map_binary {A B : Type} {R : A → A → Bool} {abs : A → B} {rep : B → A}
    (Q : is_quotient R abs rep) {f : A → A → A}
    (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), R (f a b) (f a' b'))
    {a b : A} (Ha : R a a) (Hb : R b b) : quotient_map_binary Q f (abs a) (abs b) = abs (f a b)
:=
  have Ha2 : R a (rep (abs a)), from R_rep_abs Q Ha,
  have Hb2 : R b (rep (abs b)), from R_rep_abs Q Hb,
  have H2 : R (f a b) (f (rep (abs a)) (rep (abs b))), from H _ _ _ _ Ha2 Hb2,
  symm (eq_abs Q H2)

theorem comp_quotient_map_binary_refl {A B : Type} {R : A → A → Bool} (Hrefl : reflexive R)
    {abs : A → B} {rep : B → A} (Q : is_quotient R abs rep) {f : A → A → A}
    (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), R (f a b) (f a' b'))
    (a b : A) : quotient_map_binary Q f (abs a) (abs b) = abs (f a b)
:= comp_quotient_map_binary Q H (Hrefl a) (Hrefl b)

set_opaque rec true
set_opaque rec_constant true
set_opaque rec_binary true
set_opaque quotient_map true
set_opaque quotient_map_binary true

-- image
-- -----

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

theorem image_rep {A B : Type} {f : A → B} (b : image f) : ∃a, f a = rep b
:= P_rep b

theorem fun_image_surj {A B : Type} {f : A → B} (b : image f) : ∃a, fun_image f a = b
:=
  obtain (a : A) (H : f a = rep b), from image_rep b,
  exists_intro a
    (calc
      fun_image f a = abst (rep b) _ : {H}
        ... = b : abst_rep _ b)

theorem image_abst {A B : Type} {f : A → B} (b : image f) : ∃a H, abst (f a) H = b
:=
  obtain (a : A) (H : fun_image f a = b), from fun_image_surj b,
  exists_intro a
    (exists_intro (image_inhabited2 f a) H)

theorem fun_image_eq {A B : Type} (f : A → B) (a b : A)
    : (f a = f b) ↔ (fun_image f a = fun_image f b)
:=
  iff_intro
    (assume H : f a = f b,
      have H2 : image_inhabited2 f a = image_inhabited2 f b, from proof_irrel _ _,
      congr (congr2 abst H) H2)
    (assume H : fun_image f a = fun_image f b,
      subst (subst (congr2 rep H) (rep_fun_image f a)) (rep_fun_image f b))

theorem idempotent_image_rep {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (b : image f)
    : fun_image f (rep b) = b
:=
  obtain (a : A) (Ha : fun_image f a = b), from fun_image_surj b,
  calc
    fun_image f (rep b) = fun_image f (rep (fun_image f a)) : {symm Ha}
      ... = fun_image f (f a) : {rep_fun_image f a}
      ... = fun_image f a : {iff_elim_left (fun_image_eq f (f a) a) (H a)}
      ... = b : Ha

theorem idempotent_image_fix {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (b : image f)
    : f (rep b) = rep b
:=
  obtain (a : A) (Ha : f a = rep b), from image_rep b,
  calc
    f (rep b) = f (f a) : {symm Ha}
      ... = f a : H a
      ... = rep b : Ha

-- construct quotient from representative map
-- ------------------------------------------

--the R's are intentionally explicit, because usually the elaborator cannot figure them out when implicit
theorem representative_map_idempotent {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
    : f (f a) = f a
:= symm (and_elim_right (and_elim_right (iff_elim_left (H2 a (f a)) (H1 a))))

theorem representative_map_idempotent_equiv {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b) (a : A)
    : f (f a) = f a
:= symm (H2 a (f a) (H1 a))

theorem representative_map_refl_rep {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
    : R (f a) (f a)
:= subst (H1 (f a)) (representative_map_idempotent R H1 H2 a)

theorem representative_map_image_fix {A : Type} (R : A → A → Bool) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a a', R a a' ↔ R a a ∧ R a' a' ∧ f a = f a') (b : image f)
    : f (rep b) = rep b
:= idempotent_image_fix (representative_map_idempotent R H1 H2) b

-- this theorem fails if it's not given explicitly that "image f" is the "B"
-- note: rep is subtype::rep
theorem representative_map_to_quotient {A : Type} {R : A → A → Bool} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b)
    : @is_quotient A (image f) R (fun_image f) rep
:= let abs := fun_image f in
  @intro A (image f) R abs rep
   (take b : image f,
      show abs (rep b) = b, from
       obtain (a : A) (Ha : f a = rep b), from image_rep b,
      calc
        abs (rep b) = abs (f a) : {symm Ha}
          ... = abst (f a) (image_inhabited2 f (f a)) :
                          {@representative_map_idempotent A R f H1 H2 a}
          ... = abst (rep b) (image_inhabited2 f (f a)) : {Ha}
          ... = b : abst_rep (image_inhabited2 f (f a)) b)
   (take b : image f,
     show R (rep b) (rep b), from
     obtain (a : A) (Ha : f a = rep b), from image_rep b,
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

-- abstract quotient
-- -----------------

definition prelim_map {A : Type} (R : A → A → Bool) (a : A)
:= ε (inhabited_intro a) (fun b, R a b)

--only needed R reflexive (or weaker: R a a)
theorem prelim_map_rel {A : Type} {R : A → A → Bool} (H : equivalence R) (a : A)
    : R a (prelim_map R a)
:=
  have reflR : reflexive R, from and_elim_left H,
  eps_ax (inhabited_intro a) a (reflR a)

-- only needed: R PER
theorem prelim_map_congr {A : Type} {R : A → A → Bool} (H1 : equivalence R) {a b : A}
    (H2 : R a b) : prelim_map R a = prelim_map R b
:=
  have symmR : symmetric R, from and_elim_left (and_elim_right H1),
  have transR : transitive R, from and_elim_right (and_elim_right H1),
  have H3 : ∀c, R a c ↔ R b c, from
    take c,
      iff_intro
        (assume H4 : R a c, transR b a c (symmR a b H2) H4)
        (assume H4 : R b c, transR a b c H2 H4),
  have H4 : (fun c, R a c) = (fun c, R b c), from funext H3,
  congr (congr2 ε (proof_irrel (inhabited_intro a) (inhabited_intro b))) H4

definition quotient {A : Type} (R : A → A → Bool) : Type := image (prelim_map R)

definition quotient_abs {A : Type} (R : A → A → Bool) : A → quotient R
:= fun_image (prelim_map R)

definition quotient_rep {A : Type} (R : A → A → Bool) : quotient R → A := rep

theorem quotient_is_quotient  {A : Type} (R : A → A → Bool) (H : equivalence R)
    : is_quotient R (quotient_abs R) (quotient_rep R)
:=
  representative_map_to_quotient_equiv
    H
    (prelim_map_rel H)
    (@prelim_map_congr _ _ H)

set_opaque fun_image true
set_opaque rec true
set_opaque is_quotient true
set_opaque prelim_map true

-- transparent: image, image_incl, quotient, quotient_abs, quotient_rep

end -- namespace quot
