Proof Style Guidelines
======================

General remarks
---------------

The file header should contain copyright information, a list of all the authors
who have worked on the file, and a description of the contents.

Use 100 columns.

When using unicode, do not use an extra space after exists, forall, or fun:
```lean
    theorem example : ∀X : Type, ∀x : X, ∃y, (λu, u) x = y 
```
Use spaces around ":" and ":=".


Structuring proofs
------------------

Use the macros take, assume, have, and show. These need to be imported:
```lean
    import macros.lua
```

With these macros the code
```lean
    theorem example2 : ∀x : ℕ, 0 < x → 0 < x + x 
    :=
      take x, 
      assume H : 0 < x, 
      have H1 : 0 + 0 < x + x, from add_lt H H,
      have H2 : 0 + 0 = 0, from add_zero_left  _,
      show 0 < x + x, from subst H1 H2    
```
is syntactic sugar for
```lean
    theorem example2: ∀x : ℕ, 0 < x → 0 < x + x 
    :=
      fun x, 
      fun H : 0 < x,
      let H1 : 0 + 0 < x + x := add_lt H H in
      let H2 : 0 + 0 = 0 := add_zero_left 0 in
      let H_show : 0 < x + x := subst H1 H2 in
      H_show
```
(This example assumes that you have imported nat.) The second proof of example2 
succeeds even if the type annotatations in the "let"
statements are ommitted. But using "have" and "show" to structure proofs generally
makes the proofs easier to read and maintain.

When universally quantified variables and hypotheses are introduced right away,
it is better to name them as parameters to the theorem:
```lean
    theorem example2 (x : ℕ) (H : 0 < x) : 0 < x + x 
    := 
      have H1 : 0 + 0 < x + x, from add_lt H H,
      have H2 : 0 + 0 = 0, from add_zero_left  _,
      show 0 < x + x, from subst H1 H2    
```

       
Indentation and line breaks
---------------------------

Use two spaces to indent. Use an extra indent when a long line forces a break, 
as in the statement of the theorem here:

```lean
    theorem two_step_induction_on {P : nat → Bool} (a : nat) (H1 : P 0) (H2 : P (succ 0))
        (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a
    :=
      [...]

```

After the statement of a theorem, put the ":=" on its own line, and start the 
proof two spaces indented.
```lean
    theorem zero_or_succ (n : nat) : n = zero ∨ n = succ (pred n)
    :=
      induction_on n
        (or_intro_left _ (refl zero))
        (take m IH, or_intro_right _
          (show succ m = succ (pred (succ m)), from congr2 succ (symm (pred_succ m))))
```      
One-line proofs can be put on the same line as ":=".
```lean
    theorem nat_case {P : nat → Bool} (n : nat) (H1: P 0) (H2 : ∀m, P (succ m)) : P n
    := induction_on n H1 (take m IH, H2 m)
```
A short definition can be written on a single line:
```lean
    definition square (x : nat) := x * x
```
For longer definitions, use conventions like those for theorems.

A "have" / "from" pair can be put on the same line.
```lean
    have H2 : n ≠ succ k, from subst (ne_symm (succ_ne_zero k)) (symm H),
    [...]
```
For clarify, you can also put it on the next line, if the justification is long.
```lean
    have H2 : n ≠ succ k, 
      from subst (ne_symm (succ_ne_zero k)) (symm H),
    [...]
```
If the justification takes more than a single line, keep the "from" on the same
line as the "have", and then begin the justification indented on the next line.
```lean
    have n ≠ succ k, from
      not_intro
        (take H4 : n = succ k,
          have H5 : succ l = succ k, from trans (symm H) H4,
          have H6 : l = k, from succ_inj H5,
          absurd H6 H2)))),
    [...]
```

When a proof rule takes multiple arguments, it is sometimes clearer, and often 
necessary, to put some of the arguments on subsequent lines. In that case, 
indent each argument.
```lean
    theorem nat_discriminate {B : Bool} {n : nat} (H1: n = 0 → B) 
        (H2 : ∀m, n = succ m → B) : B
    :=
      or_elim (zero_or_succ n)
        (take H3 : n = zero, H1 H3)
        (take H3 : n = succ (pred n), H2 (pred n) H3)

```

When the arguments themselves are long enough to require line breaks, use
an additional indent for every line after the first, as in the following 
example:
```lean
    theorem add_right_inj {n m k : nat} : n + m = n + k → m = k
    :=
      induction_on n
        (take H : 0 + m = 0 + k,
          calc
            m = 0 + m : symm (add_zero_left m)
              ... = 0 + k : H
              ... = k : add_zero_left k)
        (take (n : nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
          have H2 : succ (n + m) = succ (n + k), from
            calc
              succ (n + m) = succ n + m : symm (add_succ_left n m)
                ... = succ n + k : H
                ... = succ (n + k) : add_succ_left n k,
          have H3 : n + m = n + k, from succ_inj H2,
          IH H3)
```

Note that handling of "calc". The first line of the 
calculation is indented two spaces, and each subsequent line is indented an
additional two spaces.
