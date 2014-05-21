----------------------------------------------------------------------------------------------------
--
-- list.lean
--
-- Experimenting with lists.
--
-- authors: Jeremy Avigad, Parikshit Khanna
--
----------------------------------------------------------------------------------------------------

import macros
import tactic 

using Nat

variable list : Type → Type

variable nil {T : Type} : list T

check (@nil Nat)

variable cons {T : Type} (x : T) (l : list T) : list T

check (cons 1 (cons 2 nil))

axiom list_rec {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) 
    (l : list T) : C l

axiom list_rec_comp_nil {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) :
  list_rec c g nil = c

axiom list_rec_comp_cons {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l))
    (x : T) (l : list T):
  list_rec c g (cons x l) = g x l (list_rec c g l)
 
definition concat {T : Type} (s t : list T) : list T
:= list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

theorem nil_concat {T : Type} (t : list T) : concat nil t = t
:= list_rec_comp_nil _ _ 

theorem cons_concat {T : Type} (x : T) (s t : list T) : concat (cons x s) t = cons x (concat s t)
:= list_rec_comp_cons _ _ _ _

theorem concat_nil {T : Type} (t : list T) : concat t nil = t
:=
  list_rec (nil_concat nil) (
    take x : T, 
    take l : list T, 
    assume H : concat l nil = l,
    show concat (cons x l) nil = cons x l, from
    (calc
      concat (cons x l) nil = cons x (concat l nil) : cons_concat x l nil
                        ... = cons x l : {H}
    )
  ) t

definition length {T : Type} : list T → ℕ
:= list_rec 0 (fun x l m, m + 1)

theorem length_nil {T : Type} : length (@nil T) = 0
:= list_rec_comp_nil _ _

theorem length_cons {T : Type} (x : T) (t : list T) : length (cons x t) = length t + 1
:= list_rec_comp_cons _ _ _ _ 

-- theorem length_concat {T : Type} (s t : list T) : length (concat s t) = length s + length t
-- := _

-- definition reverse {T : Type} : list T → list T := _

-- theorem {T : Type} (t : list t) : reverse (reverse t) = t