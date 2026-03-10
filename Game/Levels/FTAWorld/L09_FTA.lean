-- import GameServer
import Game.Levels.FTAWorld.L08_FTA

World "FTAWorld"
Level 9
Title "Tails of non-permutative lists "

Introduction "
# **Level 9**
This exercise is short, but a little tricky.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
The permutation relation is symmetric on lists. Here's what it looks like in Lean (where `α` is a generic Type):
```
Perm.symm (h : l₁ ~ l₂) : l₂ ~ l₁
```
-/
DefinitionDoc List.Perm.symm as "Perm.symm"

/--
As stated:
```
tails_not_perm {u : Type}
  (p : u)
  (P Q Pt Qt : List u)
  (np : ¬ P ~ Q)
  (hPt : P ~ (p :: Pt))
  (hQt : Q ~ (p :: Qt)) :
  ¬ Pt ~ Qt
```
If two lists are not permutations of each other but they share the same head, then their tails are not permutations of each other.
-/
TheoremDoc not_perm_tails as "FTA : not_perm_tails"

/-- If two lists of integers are permutations of each other, then they have the same product.-/
Statement not_perm_tails {u : Type}
  (p : u)
  (P Q Pt Qt : List u)
  (np : ¬ P ~ Q)
  (hPt : P ~ (p :: Pt))
  (hQt : Q ~ (p :: Qt)) :
  ¬ Pt ~ Qt := by
  by_contra F
  obtain F' := Perm.cons p F
  Hint "Almost there. It might be helpful to know that the permutation relation is symmetric and that Lean knows this. 🔍 Check out the entry for `Perm.symm` in the **Definitions** tab."
  exact np (Perm.trans hPt (Perm.trans F' (Perm.symm hQt)))

Conclusion "
"

NewDefinition List.Perm.symm
