-- import GameServer
import Game.Levels.FTAWorld.L07_FTA

World "FTAWorld"
Level 8
Title "List products are fixed under permutation"

Introduction "
# **Level 8**
We now that `P ∼ Q` as a hypothesis. Given that permutations are inductively defined, we might want to attempt **structural induction** on the hypothesis `h`. 👉 Specifically, try
```
induction h
```
This ought to produce four goals...
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
As stated:
```
theorem prod_perm_eq_self
  (P Q : List Z)
  (h : P ~ Q) :
  P.prod = Q.prod
```
If two lists of integers are permutations of each other, then they have the same product.
-/
TheoremDoc prod_perm_eq_self as "FTA : prod_perm_eq_self"

/-- If two lists of integers are permutations of each other, then they have the same product.-/
Statement prod_perm_eq_self
  (P Q : List Z)
  (h : P ~ Q) :
  P.prod = Q.prod := by
  induction h
  Hint "The first is simple; we're assumping `P` and `Q` are empty lists (this is the **nil** constructor for `Perm`)."
  rfl
  Hint "Now we're reckoning the **cons** constructor."
  simp[List.prod,a_ih]
  Hint "And now the **swap** constructor."
  simp[List.prod]
  rw[← mul_assoc,← mul_assoc,mul_comm y]
  Hint "Finally, the **trans** constructor."
  rw[a_ih,a_ih_1]

Conclusion "
"
