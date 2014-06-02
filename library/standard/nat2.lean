----------------------------------------------------------------------------------------------------
import macros
import nat
import find
import tactic

using nat

unary_nat

-- computes (succ x) divmod (succ y) from x divmod y  
definition divmod_aux' (y : ℕ) (p : ℕ # ℕ) : ℕ # ℕ
:= 
  let q := proj1 p,    --  q = x div (succ y)
    r := proj2 p in    --  r = x mod (succ y)
  if r < y then pair q (succ r) else pair (succ q) (r - y)

-- computes x divmod (succ y)
definition divmod_aux (y : ℕ) : ℕ → ℕ # ℕ 
:=
  nat_rec 
    (pair 0 0)                      -- when x = 0
    (fun x' p, divmod_aux' y p)     -- case x = succ x'

theorem divmod_aux_zero (y : ℕ) : divmod_aux y 0 = pair 0 0
:= nat_rec_zero _ _

theorem divmod_aux_succ (y x : ℕ) : divmod_aux y (succ x) = divmod_aux' y (divmod_aux y x)
:= nat_rec_succ _ _ _

definition divmod (x : ℕ) : ℕ → ℕ # ℕ
:=
  nat_rec
    (pair 0 x)                     -- case y = 0    
    (fun y' h, divmod_aux y' x)    -- case y = succ y'

theorem divmod_zero (x : ℕ) : divmod x 0 = pair 0 x
:= nat_rec_zero _ _

theorem divmod_succ (x y : ℕ) : divmod x (succ y) = divmod_aux y x
:= nat_rec_succ _ _ _

theorem divmod_zero_succ (y : ℕ) : divmod 0 (succ y) = pair 0 0 
:= trans (divmod_succ _ _) (divmod_aux_zero _)

theorem divmod_succ_succ (x y : ℕ) : divmod (succ x) (succ y) = divmod_aux' y (divmod x (succ y))  
:=
  calc
     divmod (succ x) (succ y) = divmod_aux y (succ x) : divmod_succ _ _
     ... = divmod_aux' y (divmod_aux y x) : divmod_aux_succ _ _
     ... = divmod_aux' y (divmod x (succ y)) : {symm (divmod_succ x y)}

definition idivide x y := proj1 (divmod x y)

definition modulo x y := proj2 (divmod x y)

infixl 70 div : idivide    -- copied from Isabelle
infixl 70 mod : modulo 

theorem div_zero (x : ℕ) : x div 0 = 0
:= proj1_congr (divmod_zero x)

theorem mod_zero (x : ℕ) : x mod 0 = x
:= proj2_congr (divmod_zero x)

theorem zero_div (y : ℕ) : 0 div y = 0 
:= nat_case y (div_zero 0) (take y', proj1_congr (divmod_zero_succ _))

theorem zero_mod (y : ℕ) : 0 mod y = 0 
:= nat_case y (mod_zero 0) (take y', proj2_congr (divmod_zero_succ _))

-- copied and adapted from app_if_distribute in kernel
theorem proj1_if_distribute {A A' B : (Type U)} (c : Bool) (a b : A # A') : 
  proj1 (if c then a else b) = if c then proj1 a else proj1 b
:= or_elim (em c)
     (λ Hc : c , calc
          proj1 (if c then a else b) = proj1 (if true then a else b)    : { eqt_intro Hc }
                            ...  = proj1 a                          : proj1_congr (if_true a b)
                            ...  = if true then proj1 a else proj1 b    : symm (if_true (proj1 a) (proj1 b))
                            ...  = if c then proj1 a else proj1 b       : { symm (eqt_intro Hc) })
     (λ Hnc : ¬ c, calc
          proj1 (if c then a else b) = proj1 (if false then a else b)   : { eqf_intro Hnc }
                            ...  = proj1 b                          : proj1_congr (if_false a b)
                            ...  = if false then proj1 a else proj1 b   : symm (if_false (proj1 a) (proj1 b))
                            ...  = if c then proj1 a else proj1 b       : { symm (eqf_intro Hnc) })
theorem proj2_if_distribute {A A' B : (Type U)} (c : Bool) (a b : A # A') : 
  proj2 (if c then a else b) = if c then proj2 a else proj2 b
:= or_elim (em c)
     (λ Hc : c , calc
          proj2 (if c then a else b) = proj2 (if true then a else b)    : { eqt_intro Hc }
                            ...  = proj2 a                          : proj2_congr (if_true a b)
                            ...  = if true then proj2 a else proj2 b    : symm (if_true (proj2 a) (proj2 b))
                            ...  = if c then proj2 a else proj2 b       : { symm (eqt_intro Hc) })
     (λ Hnc : ¬ c, calc
          proj2 (if c then a else b) = proj2 (if false then a else b)   : { eqf_intro Hnc }
                            ...  = proj2 b                          : proj2_congr (if_false a b)
                            ...  = if false then proj2 a else proj2 b   : symm (if_false (proj2 a) (proj2 b))
                            ...  = if c then proj2 a else proj2 b       : { symm (eqf_intro Hnc) })

theorem div_succ_succ (x y : ℕ) : (succ x) div (succ y) = 
    if (x mod (succ y) < y) then x div (succ y) else succ (x div (succ y))
:=
  have H : (succ x) div (succ y) = proj1 (divmod_aux' y (divmod x (succ y))), 
    from proj1_congr (divmod_succ_succ x y),
  let q := x div (succ y),
    r := x mod (succ y) in
  have H1 : divmod_aux' y (divmod x (succ y)) = 
      if r < y then pair q (succ r) else pair (succ q) (r - y), from refl _,
  have H2 : proj1 (if r < y then pair q (succ r) else pair (succ q) (r - y)) =
      if r < y then proj1 (pair q (succ r)) else proj1 (pair (succ q) (r - y)), 
    from @proj1_if_distribute ℕ ℕ (ℕ # ℕ) (r < y) (pair q (succ r)) (pair (succ q) (r - y)),
  trans (trans H (proj1_congr H1)) H2

theorem mod_succ_succ (x y : ℕ) : (succ x) mod (succ y) = 
    if (x mod (succ y) < y) then succ (x mod (succ y)) else x mod (succ y) - y
:=
  have H : (succ x) mod (succ y) = proj2 (divmod_aux' y (divmod x (succ y))), 
    from proj2_congr (divmod_succ_succ x y),
  let q := x div (succ y),
    r := x mod (succ y) in
  have H1 : divmod_aux' y (divmod x (succ y)) = 
      if r < y then pair q (succ r) else pair (succ q) (r - y), from refl _,
  have H2 : proj2 (if r < y then pair q (succ r) else pair (succ q) (r - y)) =
      if r < y then proj2 (pair q (succ r)) else proj2 (pair (succ q) (r - y)), 
    from @proj2_if_distribute ℕ ℕ (ℕ # ℕ) (r < y) (pair q (succ r)) (pair (succ q) (r - y)),
  trans (trans H (proj2_congr H1)) H2
