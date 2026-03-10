-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L09_test

World "RingWorld"
Level 10
Title "Negatives of Products"

Introduction "
# **Level 10**
There are a couple different ways to go about this one.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
neg_mul_right : ∀ a b : Z, - (a * b) = a * (-b)
```
Negatives can distribute to the right-member of a product. In particular, for all $a,b ∈ ℤ$, we have $-(ab) = a(-b)$.
-/
TheoremDoc neg_mul_right as "Rng : neg_mul_right"

/-- The product of an integer and the negative of another integer is equal to the negative product of those integers.-/
Statement neg_mul_right : ∀ a b : Z, - (a * b) = a * (-b) := by
  intro a b
  symm
  apply neg_unique
  rw[← mul_add,add_neg_self,mul_zero]

Conclusion "
"
NewTheorem neg_mul_right
