Documentation Style Guidelines
==============================

Proof documents are generated from .lean files automatically, in the following
way:

* Lines beginning with "---" are omitted. 

* Blocks between lines beginning with "--(" and "--)" are omitted.

* Otherwise, lines beginning with "--" are rendered as markdown (the two dashes,
and a single space if it exists, are dropped).

* Lines of code between comments are rendered as markdown code blocks.

* Definitions starting with a ":=" at the beginning of a line are omitted, until
the next blank line.

To facilitate nice proof documents, use "---", "--(", and "--)" to indicate things 
that should be omitted, such as the copyright notice or "to do" items.

After the copyright notice, start the file with a header like this:
```
-- Theory nat
-- ==========
--
-- The natural numbers, with addition, multiplication, ordering, and subtraction.
```

Begin sections with a second-level header:
```
-- Addition
-- --------
```
Capitalize only the first word.

Begin subsections with a third-level header:
```
-- ### commutativity and associativity
```
Use lower case.

If you want to add comments to code without breaking up the code block, simply
start the comment two spaces in:
```
  -- for fixed y, recursive call for x div y
definition div_aux_rec (y : ℕ) (x : ℕ) (div_aux' : ℕ → ℕ) : ℕ
```

