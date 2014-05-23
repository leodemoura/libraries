import kernel
import macros

variable nat : Type

namespace nat
variable zero : nat
variable succ : nat -> nat
axiom nat_rec {P : nat → Type} (x : P zero)  (f : ∀ m : nat, P m → P (succ m)) (m:nat) : P m
axiom nat_rec_zero {P : nat → Type} (x : P zero) (f : ∀ m : nat, P m → P (succ m)) : nat_rec x f zero = x
axiom nat_rec_succ {P : nat → Type} (x : P zero) (f : ∀ m : nat, P m → P (succ m)) (n : nat) : nat_rec x f (succ n) = f n  (nat_rec x f n)

theorem induction_on {P : nat → Bool} (a : nat) (H1 : P zero) (H2 : ∀ (n : nat) (IH : P n), P (succ n)) : P a
:= nat_rec H1 H2 a

theorem zero_neq_succ (n:nat) : zero ≠ succ n
:= iff_elimr neq_to_not_eq (not_intro (take H: zero = succ n,absurd
   (let f : nat -> Bool := (nat_rec true (fun a b,false))
   in calc true = f zero : symm (nat_rec_zero _ _)
      	   ... = f (succ n) : subst (refl _) H
	   ... = false : nat_rec_succ _ _ _) true_ne_false))

--theorem zero_or_succ (n:nat) : n = zero ∨ ∃k, n = succ k
--:= induction_on n (or_introl (refl _) _) (take m IH, or_intror _ (exists_intro m (refl _)))

definition pred (a : nat) := nat_rec zero (fun m x, m) a

theorem pred_zero : pred zero = zero := nat_rec_zero _ _
theorem pred_succ (n:nat) : pred (succ n) = n := nat_rec_succ _ _ _

set_opaque pred true

theorem zero_or_succ (n:nat) : n = zero ∨ n = succ (pred n)
:= induction_on n (or_introl (refl _) _) (take m IH, or_intror _ (congr2 succ (symm (pred_succ _))))

theorem succ_mono {n m:nat} (H : succ n = succ m) : n = m
:= calc n = pred (succ n)    : symm (pred_succ n)
   	... = pred (succ m)  : {H}
	... = m	   	       : pred_succ m

theorem succ_nofixpoint (n:nat) : n ≠ succ n
:= iff_elimr neq_to_not_eq (not_intro (induction_on n
   (take H : zero = succ zero, let neq : zero ≠ succ zero := zero_neq_succ zero in iff_eliml (neq_elim neq) H)
   (take k IH H, IH (succ_mono H))
   ))


definition add (a b : nat) := nat_rec a (fun m x, succ x) b
infixl 65 +  : add

theorem add_zeror (n:nat) : n + zero = n := nat_rec_zero _ _
theorem add_succr (n m:nat) : n + succ m = succ (n + m) := nat_rec_succ _ _ _

set_opaque add true

theorem add_zerol (n:nat) : zero + n = n
:= induction_on n (add_zeror zero) (take m IH, 
   calc zero + succ m = succ (zero + m) : add_succr _ _
   	      ... = succ m   	     	   : { IH }
   )

theorem add_succl (n m:nat) : (succ n) + m = succ (n + m)
:= induction_on m
   (calc succ n + zero = succ n : add_zeror (succ n)
   	       	       ... = succ (n + zero) : {symm (add_zeror n)})
 (take k IH, 
   calc succ n + succ k = succ (succ n + k) : add_succr _ _
   	      ... = succ (succ (n + k)) : {IH}
   	      ... = succ (n + succ k) : {symm (add_succr _ _)}
   )

theorem add_comm (n m:nat) : n + m = m + n
:= induction_on m (trans (add_zeror _) (symm (add_zerol _))) 
   (take k IH, calc n + succ k = succ (n+k) : add_succr _ _
   	      	       	    ... = succ (k+n) : {IH}
			    ... = (succ k) + n : symm (add_succl _ _))

--theorem add_comm_succ (n m:nat) : n + succ m = m + succ n
--:= calc n + succ m = succ (n + m) : add_succr _ _
--  	    	 ... = succ n + m : symm (add_succl _ _)
--		 ... = m + succ n : add_comm _ _

theorem add_assoc (n m k:nat) : (n + m) + k = n + (m + k)
:= induction_on k 
   (calc (n + m) + zero = n + m : add_zeror _
   	      	   ... = n + (m + zero) : {symm (add_zeror m)})
   (take l IH, calc (n + m) + succ l = succ ((n + m) + l) : add_succr _ _
   	      	      	       	 ... = succ (n + (m + l)) : {IH}
				 ... = n + succ (m + l) : symm (add_succr _ _)
				 ... = n + (m + succ l) : {symm (add_succr _ _)})

definition mul (a b : nat) := nat_rec zero (fun m x, x + a) b
infixl 70 *  : mul

theorem mul_zeror (n:nat) : n * zero = zero := nat_rec_zero _ _
theorem mul_succr (n m:nat) : n * succ m = n * m + n := nat_rec_succ _ _ _

set_opaque mul true

theorem mul_zerol (n:nat) : zero * n = zero
:= induction_on n (mul_zeror zero) (take m IH, 
   calc zero * succ m = zero * m + zero : mul_succr _ _
   	      ... = zero * m : add_zeror _
   	      ... = zero : IH
   )

theorem mul_succl (n m:nat) : (succ n) * m = (n * m) + m
:= induction_on m
   (calc succ n * zero = zero			: mul_zeror _
   	       	       ... = n * zero 		: symm (mul_zeror _)
   	       	       ... = n * zero + zero 	: symm (add_zeror _))
 (take k IH, 
   calc succ n * succ k = (succ n * k) + succ n : mul_succr _ _
   	      ... = (n * k) + k + succ n : { IH }
   	      ... = (n * k) + (k + succ n) : add_assoc _ _ _
   	      ... = (n * k) + succ (k + n) : {add_succr _ _}
   	      ... = (n * k) + (succ k + n) : {symm (add_succl _ _)}
   	      ... = (n * k) + (n + succ k) : {add_comm _ _}
--   	      ... = (n * k) + (n + succ k) : {add_comm_succ _ _}
   	      ... = (n * k) + n + succ k : symm (add_assoc _ _ _)
   	      ... = (n * succ k) + succ k : {symm (mul_succr n k)})

theorem mul_comm (n m:nat) : n * m = m * n
:= induction_on m (trans (mul_zeror _) (symm (mul_zerol _))) 
   (take k IH, calc n * succ k = n * k + n : mul_succr _ _
   	      	       	    ... = k * n + n : {IH}
			    ... = (succ k) * n : symm (mul_succl _ _))

theorem mul_add_distrl  (n m k : nat) : (n + m) * k = n * k + m * k
:= induction_on k
   (calc (n + m) * zero = zero : mul_zeror _
   	      	   ... = zero + zero : symm (add_zeror _)
		   ... = n * zero + zero : {symm (mul_zeror _)}
		   ... = n * zero + m * zero : {symm (mul_zeror _)})
   (take l IH, calc (n + m) * succ l = (n + m) * l + (n + m) : mul_succr _ _
   	       	       	      ... = n * l + m * l + (n + m) : {IH}
   	       	       	      ... = n * l + m * l + n + m : symm (add_assoc _ _ _)
   	       	       	      ... = n * l + (m * l + n) + m : {add_assoc _ _ _}
   	       	       	      ... = n * l + (n + m * l) + m : {add_comm _ _}
   	       	       	      ... = n * l + n + m * l + m : {symm (add_assoc _ _ _)}
   	       	       	      ... = n * l + n + (m * l + m) : add_assoc _ _ _
   	       	       	      ... = n * succ l + (m * l + m) : {symm (mul_succr _ _)}
   	       	       	      ... = n * succ l + m * succ l : {symm (mul_succr _ _)})


theorem mul_add_distrr  (n m k : nat) : n * (m + k) = n * m + n * k
:= calc n * (m + k) = (m + k) * n : mul_comm _ _
   	       	 ... = m * n + k * n : mul_add_distrl _ _ _
		 ... = n * m + k * n : {mul_comm _ _}
		 ... = n * m + n * k : {mul_comm _ _}

theorem mul_assoc (n m k:nat) : (n * m) * k = n * (m * k)
:= induction_on k 
   (calc (n * m) * zero = zero : mul_zeror _
   	      	   ... = n * zero : symm (mul_zeror _)
   	      	   ... = n * (m * zero) : {symm (mul_zeror _)})
   (take l IH, calc (n * m) * succ l = (n * m) * l + n * m : mul_succr _ _
   	      	      	       	 ... = n * (m * l) + n * m : {IH}
				 ... = n * (m * l + m) : symm (mul_add_distrr _ _ _)
				 ... = n * (m * succ l) : {symm (mul_succr _ _)})


end --namespace nat