
Theory nat2
===========

This is a continuation of the development of the natural numbers, with a general way of
defining recursive functions, and definitions of div, mod, and gcd.

```lean
import kernel
import macros
import nat
import find
import tactic

using nat
unary_nat

namespace nat


```

A general recursion principle
=============================

Data:

  dom, codom : Type
  default : codom
  measure : dom → ℕ
  rec_val : dom → (dom → codom) → codom

and a proof

  rec_decreasing : ∀m, m ≥ measure x, rec_val x f = rec_val x (restrict f m)

... which says that the recursive call only depends on f at values with measure less than x,
in the sense that changing other values to the default value doesn't change the result.

The result is a function f = rec_measure, satisfying

  f x = rec_val x f

```lean
definition restrict {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom)

theorem restrict_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom) (H : measure x < m) :
  restrict default measure f m x = f x

theorem restrict_not_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (f : dom → codom) (m : ℕ) (x : dom) (H : ¬ measure x < m) :
  restrict default measure f m x = default

definition rec_measure_aux {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) : ℕ → dom → codom

definition rec_measure {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) (x : dom) : codom

theorem rec_measure_aux_spec {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom)
    (rec_decreasing : ∀g m x, m ≥ measure x →
        rec_val x g = rec_val x (restrict default measure g m))
    (m : ℕ) :
  let f' := rec_measure_aux default measure rec_val in
  let f := rec_measure default measure rec_val in
  f' m = restrict default measure f m

theorem rec_measure_spec {dom codom : Type} {default : codom} {measure : dom → ℕ}
    (rec_val : dom → (dom → codom) → codom)
    (rec_decreasing : ∀g m x, m ≥ measure x →
      rec_val x g = rec_val x (restrict default measure g m))
    (x : dom):
  let f := rec_measure default measure rec_val in
  f x = rec_val x f


```

Div and mod
-----------

### the definition of div

```lean
  -- for fixed y, recursive call for x div y
definition div_aux_rec (y : ℕ) (x : ℕ) (div_aux' : ℕ → ℕ) : ℕ

definition div_aux (y : ℕ) : ℕ → ℕ := rec_measure 0 (fun x, x) (div_aux_rec y)

theorem div_aux_decreasing (y : ℕ) (g : ℕ → ℕ) (m : ℕ) (x : ℕ) (H : m ≥ x) :
    div_aux_rec y x g = div_aux_rec y x (restrict 0 (fun x, x) g m)

theorem div_aux_spec (y : ℕ) (x : ℕ) :
    div_aux y x = if (y = 0 ∨ x < y) then 0 else succ (div_aux y (x - y))

definition idivide (x : ℕ) (y : ℕ) : ℕ := div_aux y x

infixl 70 div : idivide    -- copied from Isabelle

theorem div_zero (x : ℕ) : x div 0 = 0

theorem div_less {x y : ℕ} (H : x < y) : x div y = 0

theorem zero_div (y : ℕ) : 0 div y = 0

theorem div_rec {x y : ℕ} (H1 : y > 0) (H2 : x ≥ y) : x div y = succ ((x - y) div y)

add_rewrite div_zero div_less zero_div

theorem div_add_self (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) div z = succ (x div z)

theorem div_add_mul_self (x y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) div z = x div z + y


```

### The definition of mod

```lean
  -- for fixed y, recursive call for x mod y
definition mod_aux_rec (y : ℕ) (x : ℕ) (mod_aux' : ℕ → ℕ) : ℕ

definition mod_aux (y : ℕ) : ℕ → ℕ := rec_measure 0 (fun x, x) (mod_aux_rec y)

theorem mod_aux_decreasing (y : ℕ) (g : ℕ → ℕ) (m : ℕ) (x : ℕ) (H : m ≥ x) :
    mod_aux_rec y x g = mod_aux_rec y x (restrict 0 (fun x, x) g m)

theorem mod_aux_spec (y : ℕ) (x : ℕ) :
    mod_aux y x = if (y = 0 ∨ x < y) then x else mod_aux y (x - y)

definition modulo (x : ℕ) (y : ℕ) : ℕ := mod_aux y x

infixl 70 mod : modulo

theorem mod_zero (x : ℕ) : x mod 0 = x

theorem mod_less {x y : ℕ} (H : x < y) : x mod y = x

theorem zero_mod (y : ℕ) : 0 mod y = 0

theorem mod_rec {x y : ℕ} (H1 : y > 0) (H2 : x ≥ y) : x mod y = (x - y) mod y

theorem mod_add_self (x : ℕ) {z : ℕ} (H : z > 0) : (x + z) mod z = x mod z

theorem mod_add_mul_self (x y : ℕ) {z : ℕ} (H : z > 0) : (x + y * z) mod z = x mod z

add_rewrite mod_zero mod_less zero_mod

```

### properties of div and mod together

```lean
theorem mod_lt (x : ℕ) {y : ℕ} (H : y > 0) : x mod y < y

theorem div_mod_eq (x y : ℕ) : x = x div y * y + x mod y

theorem mod_le (x y : ℕ) : x mod y ≤ x

theorem remainder_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
    (H3 : q1 * y + r1 = q2 * y + r2) : r1 = r2

theorem quotient_unique {y : ℕ} (H : y > 0) {q1 r1 q2 r2 : ℕ} (H1 : r1 < y) (H2 : r2 < y)
    (H3 : q1 * y + r1 = q2 * y + r2) : q1 = q2

theorem div_mul_mul {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) div (z * y) = x div y

theorem mod_mul_mul {z : ℕ} (x y : ℕ) (zpos : z > 0) : (z * x) mod (z * y) = z * (x mod y)

theorem mod_1 (x : ℕ) : x mod 1 = 0

add_rewrite mod_1

theorem div_1 (x : ℕ) : x div 1 = x

```

Divides
-------

```lean
definition dvd (x y : ℕ) : Bool := y mod x = 0

infix 50 | : dvd

theorem dvd_iff_mod_eq_zero (x y : ℕ) : y | x ↔ x mod y = 0

theorem dvd_imp_div_mul_eq {x y : ℕ} (H : y | x) : x div y * y = x

theorem mul_eq_imp_dvd {z x y : ℕ} (H : z * y = x) :  y | x

theorem dvd_iff_exists_mul (x y : ℕ) : x | y ↔ ∃z, z * x = y


```

Gcd and lcm
-----------

### definition of gcd

```lean
definition gcd_aux_measure (p : ℕ ## ℕ) : ℕ

definition gcd_aux_rec (p : ℕ ## ℕ) (gcd_aux' : ℕ ## ℕ → ℕ) : ℕ

definition gcd_aux : ℕ ## ℕ → ℕ := rec_measure 0 gcd_aux_measure gcd_aux_rec

theorem gcd_aux_decreasing (g : ℕ ## ℕ → ℕ) (m : ℕ) (p : ℕ ## ℕ) (H : m ≥ gcd_aux_measure p) :
    gcd_aux_rec p g = gcd_aux_rec p (restrict 0 gcd_aux_measure g m)

theorem gcd_aux_spec (p : ℕ ## ℕ) : gcd_aux p =
  let x := tproj1 p, y := tproj2 p in
  if y = 0 then x else gcd_aux (tpair y (x mod y))

definition gcd (x y : ℕ) : ℕ := gcd_aux (tpair x y)

theorem gcd_def (x y : ℕ) : gcd x y = if y = 0 then x else gcd y (x mod y)

theorem gcd_zero (x : ℕ) : gcd x 0 = x

add_rewrite gcd_zero

theorem gcd_zero_left (x : ℕ) : gcd 0 x = x
```

