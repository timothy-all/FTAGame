-- import GameServer
import Game.Levels.absWorld.L02_abs

World "absWorld"
Level 3
Title "Absolute values are non-negative"

Introduction "
# **Level 3**
Let's show that absolute values are non-negative.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
abs_pos : ∀ a : Z, 0 ≤ abs a
```
For all $a ∈ ℤ$, we have $0 ≤ |a|$.
-/
TheoremDoc abs_nonneg as "Abs : abs_nonneg"


/-- For every integer $a$, $|a|$ is nonnegative.-/
Statement abs_nonneg : ∀ a : Z, 0 ≤ abs a := by
  intro a
  by_cases ha : a < 0
  right
  simp[abs,ha]
  simpa[lt_def] using ha
  simp[abs,ha]
  simpa using ha

Conclusion "
"
