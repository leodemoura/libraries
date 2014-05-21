----------------------------------------------------------------------------------------------------
--
-- playing with the axioms
--
----------------------------------------------------------------------------------------------------

import macros

-- the natural axioms for equality, together with refl

axiom subst_new {A : (Type U)} {a b : A} {P : A → Type} (H1 : P a) (H2 : a = b) : P b
axiom subst_new_id {A : (Type U)} {a : A} {P : A → Type} (H1 : P a) (e : a = a) : subst_new H1 e = H1

-- previously an axiom
theorem subst_old {A : (Type U)} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a = b) : P b
:= subst_new H1 H2.

-- casting
definition cast_new {A B : Type} (e : A = B) (a : A) : B
:= subst_new a e

theorem cast_new_id {A : Type} (e : A = A) (a : A) : cast_new e a = a
:= subst_new_id a e

-- previously a variable
definition cast_old {A B : Type} (e : A == B) (a : A) : B
:= cast_new (to_eq e) a

-- previously an axiom
theorem cast_new_heq {A B : Type} (e : A = B) (a : A) : cast_new e a == a 
:= subst_new 
      (show ∀ e : A = A, ∀ a : A, cast_new e a == a, from fun e, fun a, to_heq (@cast_new_id A e a))
      e e a 

-- corresponding axioms for hsubst
-- I am not sure we need them
-- axiom hsubst_new {A B : (Type U+1)} {a : A} {b : B} (P : ∀ T : (Type U+1), T → Type) : 
--    P A a → a == b → P B b

-- axiom hsubst_new_id {A : (Type U+1)} {a : A} (P : ∀ T : (Type U+1), T → Type) (p : P A a)
--    (e : a == a): hsubst_new P p e = p

-- -- previously an axiom
-- theorem hsubst_old {A B : (Type U+1)} {a : A} {b : B} (P : ∀ T : (Type U+1), T → Bool)
--      (p : P A a) (e : a == b) : P B b
-- := hsubst_new P p e

-- why is the theorem hcongr1 in kernal.lean called that? maybe congr1_dep would be better?
-- then this would be hcongr1_dep
axiom hcongr1_new {A : (Type U+1)} {B B' : A → (Type U+1)} {f : ∀ x : A, B x} {f' : ∀ x : A, B' x} 
  (a : A) (e : f == f') : f a == f' a

-- previously an axiom
theorem hcongr_old {A A' : (Type U+1)} {B : A → (Type U+1)} {B' : A' → (Type U+1)} 
  {f : ∀ x : A, B x} {f' : ∀ x : A', B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'
:=
  take eq_f_f' : f == f',
  take eq_a_a' : a == a',
  have aux : ∀ B B' : A → (Type U+1), ∀ f : ∀ x : A, B x, ∀ f' : ∀ x : A, B' x,
      f == f' → f a == f' a, from (fun B B' : A → (Type U+1), fun f f' e, hcongr1_new a e),
  -- it seems the elaborator can't infer the predicate here
  --  (hsubst _ aux eq_a_a') B B' f f' eq_f_f'
  hsubst
    (fun X : (Type U+1), fun x : X, 
      ∀ B : A → (Type U+1), ∀ B' : X → (Type U+1), ∀ f : ∀ x : A, B x, ∀ f' : ∀ x : X, B' x, 
          f == f' → f a == f' x)
    aux eq_a_a' B B' f f' eq_f_f'

theorem hpiext_new {A : Type} {B B' : A → Type} (e : B = B') : (∀ x, B x) = (∀ x, B' x)
:=
  let P := fun X : A → Type, (∀ x, B x) = (∀ x, X x) in
  substp P (refl (∀ x, B x)) e
--  subst (refl _) e -- causes nontermination

theorem hpiext_old {A A' : Type} {B : A → Type} {B' : A' → Type}
      (e : A = A') (H : ∀ x x', x == x' → B x == B' x') : (∀ x, B x) == (∀ x, B' x)
:=
  have aux: ∀ B B' : A → Type, (∀ x x', x == x' → B x == B' x') → (∀ x, B x) == (∀ x, B' x), from (
    take B B' : A → Type,
    take H : (∀ x x', x == x' → B x == B' x'),
    have H2 : ∀x, B x = B' x, from (take x : A, to_eq (H x x (hrefl x))),
    have H3 : B = B', from funext H2,
    to_heq (hpiext_new H3)
  ),
  @subst_new _ _ _ (fun X,
    ∀ B : A → Type, ∀ B' : X → Type, (∀ x x', x == x' → B x == B' x') → (∀ x, B x) == (∀ x, B' x))
    aux e B B' H

theorem app_cast {A : Type} {B B' : A → Type} (f : ∀ x, B x) (e : B = B')
  (a : A) : cast_new (hpiext_new e) f a = cast_new (congr1 e a) (f a)
:= 
  let P := fun X : A → Type, ∀ e' : B = X, 
    cast_new (hpiext_new e') f a = cast_new (congr1 e' a) (f a) in
  have H : P B, from (
    take e', trans (hcongr1 (cast_new_id _ f) a) (symm (cast_new_id _ (f a)))),
  have H2 : P B', from subst H e,
  H2 e

-- should replace the old one
theorem type_eq_new {A B : Type} {a : A} {b : B} (e : a == b) : A = B
:= to_eq (type_eq e)

theorem heq_to_eq2 {A B : Type} {a : A} {b : B} (e : a == b):
  cast_new (type_eq_new e) a = b
:= to_eq (htrans (cast_new_heq (type_eq_new e) a) e)

-- an alternative characterization of ==
-- could be used as a definition
theorem heq_equiv {A B : Type} {a : A} {b : B} :
  (a == b) ↔ ∃ e : A = B, cast_new e a = b
:= 
  iff_intro (
    assume e : a == b,
    exists_intro (type_eq_new e) (heq_to_eq2 e)
  ) (
    assume H : ∃ e : A = B, cast_new e a = b,
    obtain (e : A = B) (H1 : cast_new e a = b), from H,
    htrans (hsymm (cast_new_heq e a)) (to_heq H1)
  )

theorem hrefl_sim {A : Type} {a : A} : ∃ e : A = A, cast_new e a = a
:= 
  exists_intro (refl A) (cast_new_id _ a)

theorem hsubst_sim {A B : Type} {a : A} {b : B} (P : ∀ T : Type, T → Bool)
  (p : P A a) (H : ∃ e : A = B, cast_new e a = b) : P B b
:= 
  obtain (e : A = B) (e1: cast_new e a = b), from H,
  have aux : ∀ e' : A = A, P A a → P A (cast_new e' a), from (
    assume e' : A = A,
    assume H' : P A a,
    have e'' : a = cast_new e' a, from symm (cast_new_id e' a), 
    subst H' e''
  ),
--  let temp := @subst Type A B
--   (fun X : Type, ∀ e' : A = X, P A a → P X (cast_new e' a)) aux e in
  have H2 : ∀ (e' : A = B), P A a → P B (cast_new e' a), from 
    @subst Type A B (fun X : Type, ∀ e' : A = X, P A a → P X (cast_new e' a)) aux e,
  have H3 : P B (cast_new e a), from H2 e p,
  subst H3 e1

axiom pi_ext (A : Type) (B B' : A → Type) : inhabited (∀ x, B x) → (∀ x, B x) = (∀ x, B' x) → B = B' 

axiom sig_ext (A : Type) (B B' : A → Type) : inhabited A → (sig x, B x) = (sig x, B' x) → B = B' 