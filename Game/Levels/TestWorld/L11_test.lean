-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L10_test

World "RingWorld"
Level 11
Title "More Negatives of Products"

Introduction "
# **Level 11**
Don't work too hard ... if you're economical, you can get this done using no more than three tactic calls (🔍 Check out the entry for `mul_comm` in the **Definitions** tab).
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
neg_mul_left : ∀ a b : Z, - (a * b) = -a * b
```
Negatives can distribute to the left-member of a product. In particular, $∀ a , b ∈ ℤ$, we have $-(ab) = (-a)b$.
-/
TheoremDoc neg_mul_left as "Rng : neg_mul_left"

/--
Multiplication is commutative. In particular, $∀ a,b ∈ ℤ, ab = ba$. Here's how it looks in Lean
```
mul_comm : ∀ a b : Z, a * b = b * a
```
-/
DefinitionDoc mul_comm as "mul_comm"

/-- The product of the negative of an integer and another integer is also equal to the negative product of those integers. -/
Statement neg_mul_left : ∀ a b : Z, - (a * b) = -a * b := by
  intro a b
  rw[mul_comm,mul_comm (-a)]
  exact neg_mul_right b a

Conclusion "
"
NewTheorem neg_mul_left
NewDefinition mul_comm
