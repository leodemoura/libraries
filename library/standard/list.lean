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
import nat

using nat

variable list : Type → Type

variable nil {T : Type} : list T

check (@nil nat)

variable cons {T : Type} (x : T) (l : list T) : list T

check (cons (succ zero) (cons (succ (succ zero)) nil))

axiom list_rec {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) :
    forall l : list T,  C l

axiom list_rec_nil {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l)) :
  list_rec c g nil = c

axiom list_rec_cons {T : Type} {C : list T → Type} (c : C nil) 
    (g : forall x : T, forall l : list T, forall c : C l, C (cons x l))
    (x : T) (l : list T):
  list_rec c g (cons x l) = g x l (list_rec c g l)
 
definition concat {T : Type} (s t : list T) : list T
:= list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

infix 50 @ : concat
infix 50 ## : cons

theorem nil_concat {T : Type} (t : list T) : nil @ t = t
:= list_rec_nil _ _ 

theorem cons_concat {T : Type} (x : T) (s t : list T) : concat (cons x s) t = cons x (concat s t)
:= list_rec_cons _ _ _ _

theorem concat_nil {T : Type} (t : list T) : concat t nil = t
:=
  list_rec (nil_concat nil) (
    take x : T, 
    take l : list T, 
    assume H : concat l nil = l,
    show concat (cons x l) nil = cons x l, from
      calc
        concat (cons x l) nil = cons x (concat l nil) : cons_concat x l nil
                        ... = cons x l : {H}
  ) t

theorem concat_assoc {T : Type} (s t u : list T) : concat (concat s t) u = concat s (concat t u)
:=
  list_rec (
    calc
      concat (concat nil t) u = concat t u : { nil_concat _ }
        ... = concat nil (concat t u) : symm (nil_concat _)
  ) (
    take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
    calc
      concat (concat (cons x l) t) u = concat (cons x (concat l t)) u : {cons_concat _ _ _}
         ... = cons x (concat (concat l t) u) : {cons_concat _ _ _ } 
         ... = cons x (concat l (concat t u)) : { H }
         ... = concat (cons x l) (concat t u) : {symm (cons_concat _ _ _)}
  ) s

definition length {T : Type} : list T → ℕ
:= list_rec zero (fun x l m, succ m)

theorem length_nil {T : Type} : length (@nil T) = zero
:= list_rec_nil _ _

theorem length_cons {T : Type} (x : T) (t : list T) : length (cons x t) = succ (length t)
:= list_rec_cons _ _ _ _ 

-- theorem length_concat {T : Type} (s t : list T) : length (concat s t) = length s + length t
--  := list_rec (length t) (fun (x : T) (l : list T) (c : length l), calc(length (concat (l t)))) s

definition reverse {T : Type} : list T → list T := 
  list_rec nil (fun x l r, concat r (cons x nil))

theorem reverse_nil {T : Type} : reverse (@nil T) = nil
:= list_rec_nil _ _

theorem reverse_cons {T : Type} (x : T) (l : list T) : reverse (cons x l) = 
    concat (reverse l) (cons x nil)
:= list_rec_cons _ _ _ _

theorem reverse_concat {T : Type} (s t : list T) : 
    reverse (concat s t) = concat (reverse t) (reverse s)
:=
  list_rec (
    calc
      reverse (concat nil t) = reverse t : { nil_concat _ }
                         ... = concat (reverse t) nil : symm (concat_nil _)
                         ... = concat (reverse t) (reverse nil) : {symm (reverse_nil)}
  ) (
    take x l,
    assume H : reverse (concat l t) = concat (reverse t) (reverse l),
    calc
      reverse (concat (cons x l) t) = reverse (cons x (concat l t)) : {cons_concat _ _ _}
        ... = concat (reverse (concat l t)) (cons x nil) : reverse_cons _ _  
        ... = concat (concat (reverse t) (reverse l)) (cons x nil) : { H }
        ... = concat (reverse t) (concat (reverse l) (cons x nil)) : concat_assoc _ _ _
        ... = concat (reverse t) (reverse (cons x l)) : {symm (reverse_cons _ _)}   
  ) s
  
theorem reverse_reverse {T : Type} (t : list T) : reverse (reverse t) = t
:= 
  list_rec (
    calc
      reverse (reverse (@nil T)) = reverse nil : {reverse_nil}
                        ... = nil : reverse_nil
  ) (
    take x l,
    assume H: reverse (reverse l) = l,
    show reverse (reverse (cons x l)) = cons x l, from 
      calc
        reverse (reverse (cons x l)) = reverse (concat (reverse l) (cons x nil)) 
            : {reverse_cons x l}
          ... = concat (reverse (cons x nil)) (reverse (reverse l)) : {reverse_concat _ _}
          ... = concat (reverse (cons x nil)) l : {H}
          ... = concat (concat (reverse nil) (cons x nil)) l : {reverse_cons _ _}
          ... = concat (concat nil (cons x nil)) l : {reverse_nil}
          ... = concat (cons x nil) l : {nil_concat _}
          ... = cons x (concat nil l) : cons_concat _ _ _
          ... = cons x l : {nil_concat _} 
  ) t


definition head {T : Type} (null : T) : list T → T 
:= list_rec null (fun x l h, x)
