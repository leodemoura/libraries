Library To Do List
==================

*logic*

- rewrite kernel with impredicative encodings of logical connectives

- separate out classical part and put them in a separate file (as in Coq)


*equality*

- has to wait for Lean 0.2.

- define equality and hequality

- separate out classical, proof irrelevant part


*nat*

- harvest stuff from Nat.lean, num.lean, primes.lean

- make names uniform and principled!


*lists*

- (will depend on nat, for example, for theorems like length (concat s t) = ...)


*overloading and generic classes*

- Cody is working on type hints to handle type classes

- overload +, *, <, <=, etc.

- develop axiomatic classes for ordering, groups, semigroups, etc.

- make nat instances of these

- eventually, develop generic treatment of iterated operators, like sums and products


*other numeric classes

- int, rat, real, complex*


*HoTT library*

- set up basic HTS, with Id and Path types, and Fib predicate

- port basic HoTT library

- experiment with HIT's