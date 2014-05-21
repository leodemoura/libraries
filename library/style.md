[Some of the things below include specific choices of names, etc., so they are not really "style guidelines." They are just here for discussion now. We can delete them from the guidelines once they are in the library.]


Naming objects and theorems
===========================

Generally use lowercase with underscores.

Brevity is a virtue, but it is more important to have the expressions easy to read, understand, and remember. 

Be consistent with terms and abbreviations.

When ordering the arguments, remember that functions and theorems will often be partially applied; think about common usages. 

Use uppercase for structures and classes, like Group and Abelian_Group. [Should we use lower case for the constructors, as in "group T m i o ..." and "abelian_group ..."?] 



*General*

A_eq_B for equations, like "abs_nonneg_eq"

A_iff_B for equivalences, like "less_iff_not_le"

A_imp_B for implications, like "less_imp_le"  [or use "implies"?]

Use lower case for important types, like nat, int, real


*Logic*

"forall" "exists" "and" "or" "not" "implies" "iff"

"intro" "elim"

For example: "and_intro" "and_elim1" "and_elim2" [or "left" "right"?]


*Equality*

"refl" "symm" "trans"

"subst"

[Think about the order here; I prefer "subst e P" as in Isabelle, rather than "subst P e" as in Coq.]


*Order*

"less" "le"

"trans" "trans_le_less" "trans_less_le"


*General operations*

"add" "mult" [or "mul"?] "less" "le" "div" "sub" "neg" "dvd" "pow"

"commute" "assoc" "distrib" 

["distrib_right" for "a * (b + c) = ..." and "left" for the other?]

"succ" "zero" "one" (instead of "0" "1")

"add_mono" "add_left_mono" "add_right_mono" "add_strict_left_mono" "add_less_le" "add_le_less" etc.



Proof Style
===========

100 columns

4 column indent

[We should set guidelines for when to indent, how to break long lines, etc.]

[Question: do we want to have synonyms "Theorem." "Lemma." "Proposition." "Corollary." as in a math textbook?]

[Similarly, we can have "Axiom" "Variable" "Constant" And plurals, "Axioms", etc.]

[Of course, we should talk about the proof language as well as style. I like the current choices of "take" "assume" "have" "show" "obtain" etc. but we should think about everything carefully now.]

[What information should go into file headers?]


