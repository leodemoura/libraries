
Theory nat
==========

The natural numbers, with addition, multiplication, ordering, and subtraction.

Axioms
------

```lean
import kernel
import macros

variable nat : Type
alias ℕ : nat
unary_nat -- enables numerals

namespace nat

variable zero : nat
variable succ : nat -> nat
axiom rec {P : nat → Type} (x : P 0)  (f : ∀m : nat, P m → P (succ m)) (m : ℕ) : P m
axiom rec_zero {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) :
    rec x f 0 = x
axiom rec_succ {P : nat → Type} (x : P 0) (f : ∀m : nat, P m → P (succ m)) (n : ℕ) :
    rec x f (succ n) = f n  (rec x f n)

theorem induction_on {P : nat → Bool} (a : ℕ) (H1 : P 0)
    (H2 : ∀(n : ℕ) (IH : P n), P (succ n)) : P a

```

Successor and predecessor
-------------------------

```lean
theorem succ_ne_zero (n : ℕ) : succ n ≠ 0

definition pred (n : ℕ) := rec 0 (fun m x, m) n

theorem pred_zero : pred 0 = 0

set_opaque pred true

theorem zero_or_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n)

theorem zero_or_exists_succ (n : ℕ) : n = 0 ∨ ∃k, n = succ k

theorem case {P : nat → Bool} (n : ℕ) (H1: P 0) (H2 : ∀m, P (succ m)) : P n

theorem case_zero_pos {P : ℕ → Bool} (y : ℕ) (H0 : P 0) (H1 : ∀y, y > 0 → P y) : P y

theorem discriminate {B : Bool} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m

theorem succ_ne_self (n : ℕ) : succ n ≠ n

theorem decidable_equality (n m : ℕ) : n = m ∨ n ≠ m

theorem two_step_induction_on {P : nat → Bool} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a

theorem sub_induction {P : nat → nat → Bool} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m

add_rewrite succ_ne_zero

```

Addition
--------

```lean
definition add (n m : ℕ) := rec n (fun k x, succ x) m
infixl 65 +  : add

theorem add_zero_right (n : ℕ) : n + 0 = n

set_opaque add true

```

### commutativity and associativity

```lean
theorem add_zero_left (n : ℕ) : 0 + n = n

theorem add_succ_left (n m : ℕ) : (succ n) + m = succ (n + m)

theorem add_comm (n m : ℕ) : n + m = m + n

theorem add_move_succ (n m : ℕ) : succ n + m = n + succ m

theorem add_comm_succ (n m : ℕ) : n + succ m = m + succ n

theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k)

theorem add_left_comm (n m k : ℕ) : n + (m + k) = m + (n + k)

theorem add_right_comm (n m k : ℕ) : n + m + k = n + k + m

theorem add_switch (n m k l : ℕ) : n + m + (k + l) = n + k + (m + l)

```

### cancelation

```lean
theorem add_cancel_left {n m k : ℕ} : n + m = n + k → m = k

theorem add_cancel_right {n m k : ℕ} (H : n + m = k + m) : n = k

theorem add_eq_zero_left {n m : ℕ} : n + m = 0 → n = 0

theorem add_eq_zero_right {n m : ℕ} (H : n + m = 0) : m = 0

theorem add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0

```

See also add_eq_self below.

### misc

```lean
theorem add_one (n : ℕ) : n + 1 = succ n

theorem add_one_left (n : ℕ) : 1 + n = succ n

theorem induction_plus_one {P : nat → Bool} (a : ℕ) (H1 : P 0)
    (H2 : ∀ (n : ℕ) (IH : P n), P (n + 1)) : P a

add_rewrite add_zero_left add_zero_right
add_rewrite add_succ_left add_succ_right
add_rewrite add_comm add_assoc add_left_comm

```

Multiplication
--------------

```lean
definition mul (n m : ℕ) := rec 0 (fun m x, x + n) m
infixl 70 *  : mul

theorem mul_zero_right (n : ℕ) : n * 0 = 0

set_opaque mul true

```

### commutativity, distributivity, associativity, identity

```lean
theorem mul_zero_left (n : ℕ) : 0 * n = 0

theorem mul_succ_left (n m : ℕ) : (succ n) * m = (n * m) + m

theorem mul_comm (n m : ℕ) : n * m = m * n

theorem mul_distr_right (n m k : ℕ) : (n + m) * k = n * k + m * k

theorem mul_distr_left (n m k : ℕ) : n * (m + k) = n * m + n * k

theorem mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k)

theorem mul_left_comm (n m k : ℕ) : n * (m * k) = m * (n * k)

theorem mul_right_comm (n m k : ℕ) : n * m * k = n * k * m

theorem mul_one_right (n : ℕ) : n * 1 = n

theorem mul_one_left (n : ℕ) : 1 * n = n

theorem mul_eq_zero {n m : ℕ} (H : n * m = 0) : n = 0 ∨ m = 0

add_rewrite mul_zero_left mul_zero_right
add_rewrite mul_succ_left mul_succ_right
add_rewrite mul_comm mul_assoc mul_left_comm

```

Less than or equal
------------------

```lean
definition le (n m : ℕ) : Bool := exists k : nat, n + k = m
infix  50 <= : le
infix  50 ≤  : le

theorem le_intro {n m k : ℕ} (H : n + k = m) : n ≤ m

theorem le_elim {n m : ℕ} (H : n ≤ m) : ∃ k, n + k = m

set_opaque le true

```

### partial order (totality is part of less than)

```lean
theorem le_refl (n : ℕ) : n ≤ n

theorem zero_le (n : ℕ) : 0 ≤ n

theorem le_zero {n : ℕ} (H : n ≤ 0) : n = 0

theorem not_succ_zero_le (n : ℕ) : ¬ succ n ≤ 0

theorem le_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k

theorem le_antisym {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m

```

### interaction with addition

```lean
theorem le_add_right (n m : ℕ) : n ≤ n + m

theorem le_add_left (n m : ℕ) : n ≤ m + n

theorem add_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m

theorem add_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n + k ≤ m + k

theorem add_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n + m ≤ k + l

theorem add_le_cancel_left {n m k : ℕ} (H : k + n ≤ k + m) : n ≤ m

theorem add_le_cancel_right {n m k : ℕ} (H : n + k ≤ m + k) : n ≤ m

theorem add_le_inv {n m k l : ℕ} (H1 : n + m ≤ k + l) (H2 : k ≤ n) : m ≤ l

add_rewrite le_add_right le_add_left

```

### interaction with successor and predecessor

```lean
theorem succ_le {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m

theorem succ_le_cancel {n m : ℕ} (H : succ n ≤ succ m) :  n ≤ m

theorem self_le_succ (n : ℕ) : n ≤ succ n

theorem le_imp_le_succ {n m : ℕ} (H : n ≤ m) : n ≤ succ m

theorem le_imp_succ_le_or_eq {n m : ℕ} (H : n ≤ m) : succ n ≤ m ∨ n = m

theorem le_ne_imp_succ_le {n m : ℕ} (H1 : n ≤ m) (H2 : n ≠ m) : succ n ≤ m

theorem le_succ_imp_le_or_eq {n m : ℕ} (H : n ≤ succ m) : n ≤ m ∨ n = succ m

theorem succ_le_imp_le_and_ne {n m : ℕ} (H : succ n ≤ m) : n ≤ m ∧ n ≠ m

theorem pred_le_self (n : ℕ) : pred n ≤ n

theorem pred_le {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m

theorem pred_le_imp_le_or_eq {n m : ℕ} (H : pred n ≤ m) : n ≤ m ∨ n = succ m

```

### interaction with multiplication

```lean
theorem mul_le_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k * n ≤ k * m

theorem mul_le_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n * k ≤ m * k

theorem mul_le {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l


```

Less than
---------

```lean
definition lt (n m : ℕ) := succ n ≤ m
infix 50 <  : lt

theorem lt_intro {n m k : ℕ} (H : succ n + k = m) : n < m

theorem lt_elim {n m : ℕ} (H : n < m) : ∃ k, succ n + k = m

theorem lt_add_succ (n m : ℕ) : n < n + succ m

```

### basic facts

```lean
theorem lt_imp_ne {n m : ℕ} (H : n < m) : n ≠ m

theorem lt_irrefl (n : ℕ) : ¬ n < n

theorem succ_pos (n : ℕ) : 0 < succ n

theorem not_lt_zero (n : ℕ) : ¬ n < 0

theorem lt_imp_eq_succ {n m : ℕ} (H : n < m) : exists k, m = succ k

```

### interaction with le

```lean
theorem lt_imp_le_succ {n m : ℕ} (H : n < m) : succ n ≤ m

theorem le_succ_imp_lt {n m : ℕ} (H : succ n ≤ m) : n < m

theorem self_lt_succ (n : ℕ) : n < succ n

theorem lt_imp_le {n m : ℕ} (H : n < m) : n ≤ m

theorem le_imp_lt_or_eq {n m : ℕ} (H : n ≤ m) : n < m ∨ n = m

theorem le_ne_imp_lt {n m : ℕ} (H1 : n ≤ m)  (H2 : n ≠ m) : n < m

theorem le_imp_lt_succ {n m : ℕ} (H : n ≤ m) : n < succ m

theorem lt_succ_imp_le {n m : ℕ} (H : n < succ m) : n ≤ m

```

### transitivity, antisymmmetry

```lean
theorem lt_le_trans {n m k : ℕ} (H1 : n < m) (H2 : m ≤ k) : n < k

theorem le_lt_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m < k) : n < k

theorem lt_trans {n m k : ℕ} (H1 : n < m) (H2 : m < k) : n < k

theorem le_imp_not_lt {n m : ℕ} (H : n ≤ m) : ¬ m < n

theorem lt_imp_not_le {n m : ℕ} (H : n < m) : ¬ m ≤ n

theorem lt_antisym {n m : ℕ} (H : n < m) : ¬ m < n

```

### interaction with addition

```lean
theorem add_lt_left {n m : ℕ} (H : n < m) (k : ℕ) : k + n < k + m

theorem add_lt_right {n m : ℕ} (H : n < m) (k : ℕ) : n + k < m + k

theorem add_le_lt {n m k l : ℕ} (H1 : n ≤ k) (H2 : m < l) : n + m < k + l

theorem add_lt_le {n m k l : ℕ} (H1 : n < k) (H2 : m ≤ l) : n + m < k + l

theorem add_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n + m < k + l

theorem add_lt_cancel_left {n m k : ℕ} (H : k + n < k + m) : n < m

theorem add_lt_cancel_right {n m k : ℕ} (H : n + k < m + k) : n < m

```

### interaction with successor (see also the interaction with le)

```lean
theorem succ_lt {n m : ℕ} (H : n < m) : succ n < succ m

theorem succ_lt_cancel {n m : ℕ} (H : succ n < succ m) :  n < m

theorem lt_imp_lt_succ {n m : ℕ} (H : n < m) : n < succ m
 := lt_trans H (self_lt_succ m)

```

### totality of lt and le

```lean
theorem le_or_lt (n m : ℕ) : n ≤ m ∨ m < n

theorem trichotomy_alt (n m : ℕ) : (n < m ∨ n = m) ∨ m < n

theorem trichotomy (n m : ℕ) : n < m ∨ n = m ∨ m < n

theorem le_total (n m : ℕ) : n ≤ m ∨ m ≤ n

theorem not_lt_imp_le {n m : ℕ} (H : ¬ n < m) : m ≤ n

theorem not_le_imp_lt {n m : ℕ} (H : ¬ n ≤ m) : m < n

```

Note: interaction with multiplication under "positivity"

### misc

```lean
theorem strong_induction_on {P : nat → Bool} (n : ℕ) (H : ∀n, (∀m, m < n → P m) → P n) : P n

theorem case_strong_induction_on {P : nat → Bool} (a : nat) (H0 : P 0)
    (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a

theorem add_eq_self {n m : ℕ} (H : n + m = n) : m = 0

```

Greater than, greater than or equal
-----------------------------------

```lean
definition ge (n m : ℕ) := m ≤ n
infix 50 >= : ge
infix 50 ≥  : ge

definition gt (n m : ℕ) := m < n
infix 50 >  : gt


```

Positivity
---------

Writing "t > 0" is the preferred way to assert that a natural number is positive.

### basic

See also succ_pos.

```lean
theorem zero_or_pos (n : ℕ) : n = 0 ∨ n > 0

theorem succ_imp_pos {n m : ℕ} (H : n = succ m) : n > 0

theorem ne_zero_pos {n : ℕ} (H : n ≠ 0) : n > 0

theorem pos_imp_eq_succ {n : ℕ} (H : n > 0) : exists l, n = succ l

theorem add_pos_right (n : ℕ) {k : ℕ} (H : k > 0) : n + k > n

theorem add_pos_left (n : ℕ) {k : ℕ} (H : k > 0) : k + n > n

```

### multiplication

```lean
theorem mul_pos {n m : ℕ} (Hn : n > 0) (Hm : m > 0) : n * m > 0

theorem mul_pos_imp_pos_left {n m : ℕ} (H : n * m > 0) : n > 0

theorem mul_pos_imp_pos_right {n m : ℕ} (H : n * m > 0) : m > 0

theorem mul_cancel_left {n m k : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k

theorem mul_cancel_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k

```

See also mul_eq_one below.

### interaction of mul with le and lt

```lean
theorem mul_lt_left {n m k : ℕ} (Hk : k > 0) (H : n < m) : k * n < k * m

theorem mul_lt_right {n m k : ℕ} (Hk : k > 0) (H : n < m)  : n * k < m * k

theorem mul_le_lt {n m k l : ℕ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) : n * m < k * l

theorem mul_lt_le {n m k l : ℕ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) : n * m < k * l

theorem mul_lt {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n * m < k * l

theorem mul_lt_cancel_left {n m k : ℕ} (H : k * n < k * m) : n < m

theorem mul_lt_cancel_right {n m k : ℕ} (H : n * k < m * k) : n < m

theorem mul_le_cancel_left {n m k : ℕ} (Hk : k > 0) (H : k * n ≤ k * m) : n ≤ m

theorem mul_le_cancel_right {n m k : ℕ} (Hm : m > 0) (H : n * m ≤ k * m) : n ≤ k

theorem mul_eq_one_left {n m : ℕ} (H : n * m = 1) : n = 1

theorem mul_eq_one_right {n m : ℕ} (H : n * m = 1) : m = 1


set_opaque lt true

```

### sub

```lean
definition sub (n m : ℕ) : nat := rec n (fun m x, pred x) m
infixl 65 - : sub

theorem sub_zero_right (n : ℕ) : n - 0 = n

set_opaque sub true

theorem sub_zero_left (n : ℕ) : 0 - n = 0

theorem sub_succ_succ (n m : ℕ) : succ n - succ m = n - m

theorem sub_self (n : ℕ) : n - n = 0

theorem sub_add_add_right (n m k : ℕ) : (n + k) - (m + k) = n - m

theorem sub_add_add_left (n m k : ℕ) : (k + n) - (k + m) = n - m

theorem sub_add_left (n m : ℕ) : n + m - m = n

theorem sub_add_left2 (n m : ℕ) : n + m - n = m

theorem sub_sub (n m k : ℕ) : n - m - k = n - (m + k)

theorem succ_sub_sub (n m k : ℕ) : succ n - m - succ k = n - m - k

theorem sub_add_right_eq_zero (n m : ℕ) : n - (n + m) = 0

theorem sub_comm (m n k : ℕ) : m - n - k = m - k - n

theorem sub_one (n : ℕ) : n - 1 = pred n

theorem succ_sub_one (n : ℕ) : succ n - 1 = n

add_rewrite sub_add_left

```

### interaction with multiplication

```lean
theorem mul_pred_left (n m : ℕ) : pred n * m = n * m - m

theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n

theorem mul_sub_distr_right (n m k : ℕ) : (n - m) * k = n * k - m * k

theorem mul_sub_distr_left (n m k : ℕ) : n * (m - k) = n * m - n * k

```

### interaction with inequalities

```lean
theorem succ_sub {n m : ℕ} : n ≤ m → succ m - n  = succ (m - n)

theorem add_sub_right {n m : ℕ} : n ≤ m → n + (m - n) = m

theorem add_sub_left {n m : ℕ} (H : n ≤ m) : m - n + n = m

theorem le_imp_sub_eq_zero {n m : ℕ} (H : n ≤ m) : n - m = 0

theorem sub_split {P : nat → Bool} {n m : ℕ} (H1 : n ≤ m → P 0) (H2 : ∀k, n = m + k -> P k)
    : P (n - m)

theorem sub_le_self (n m : ℕ) : n - m ≤ n

theorem le_elim_sub (n m : ℕ) (H : n ≤ m) : exists k, m - k = n

theorem add_sub_assoc {n m k : ℕ} : k ≤ m → n + m - k = n + (m - k)

theorem sub_eq_zero_imp_le {n m : ℕ} : n - m = 0 → n ≤ m

theorem sub_sub_split {P : nat → nat → Bool} {n m : ℕ} (H1 : ∀k, n = m + k -> P k 0)
    (H2 : ∀k, m = n + k → P 0 k) : P (n - m) (m - n)

theorem sub_intro {n m k : ℕ} (H : n + m = k) : k - n = m

theorem sub_lt {x y : ℕ} (xpos : x > 0) (ypos : y > 0) : x - y < x

```

Max, min, iteration, and absolute difference
--------------------------------------------


### absolute difference

This section is still incomplete, it is just sufficient to define the absolute value of an integer.

```lean
definition asub (n m : ℕ) := (n - m) + (m - n)

theorem asub_comm (n m : ℕ) : asub n m = asub m n

theorem asub_le {n m : ℕ} (H : n ≤ m) : asub n m = m - n

theorem asub_ge {n m : ℕ} (H : n ≥ m) : asub n m = n - m

theorem asub_zero_right (n : ℕ) : asub n 0 = n

theorem asub_zero_left (n : ℕ) : asub 0 n = n

theorem asub_intro {n m k : ℕ} (H : n + m = k) : asub k n = m

theorem asub_add_right (n m k : ℕ) : asub (n + k) (m + k) = asub n m

theorem asub_ge_add_right {n m : ℕ} (H : n ≥ m) : asub n m + m = n

theorem asub_add_left (n m k : ℕ) : asub (k + n) (k + m) = asub n m

theorem asub_eq {n m k l : ℕ} (H : n + m = k + l) : asub n k = asub l m

end --namespace nat
```

