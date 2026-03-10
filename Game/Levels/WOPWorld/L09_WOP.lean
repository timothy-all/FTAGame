-- import GameServer
import Game.Levels.WOPWorld.L08_WOP

World "WOPWorld"
Level 9
Title "Magnifying by multiplication"

Introduction "
# **Level 9**
This lemma is just setup for the main boss at the end of the world.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As state:
```
mul_step_up : ∀ a b x : Z, 0 < b →
  ∃ y : Z, a + -(b * x) < a + -(b * y)
```
For all $a b, x ∈ ℤ$, if $b$ is positive, then there exists $y ∈ ℤ$ such that $ a - bx < a - by $.
-/
TheoremDoc mul_step_up as "WOP : mul_step_up"

/-- For all $a,b, x ∈ ℤ$, if $b$ is positive, then there exists $y ∈ ℤ$ such that $ a - bx < a - by $.-/
Statement mul_step_up : ∀ a b x : Z, 0 < b → ∃ y : Z, a + -(b * x) < a + -(b * y) := by
  intro a b x hb
  use (x + -1)
  apply add_le_lt
  simp[le_def]
  rw[mul_add,← neg_mul_right,← neg_add,add_comm]
  simp
  rw[lt_def,add_assoc]
  simp[mem_Zplus,hb]


Conclusion "
We'll generalize this lemma in the next level.
"
