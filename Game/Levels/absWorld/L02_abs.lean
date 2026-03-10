-- import GameServer
import Game.Levels.absWorld.L01_abs

World "absWorld"
Level 2
Title "Integers are divisible by their absolute values"

Introduction "
# **Level 2**
This level is a natural companion to the previous level and ought to give us more practice with the `abs` definition.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
dvd_abs : ∀ a : Z, a ∣ abs a
```
For all $a ∈ ℤ$, $|a|$ divides $a$.
-/
TheoremDoc abs_dvd as "Abs : abs_dvd"


/-- For every integer $a$, $|a|$ divides $a$.-/
Statement abs_dvd : ∀ a : Z, abs a ∣ a := by
  intro a
  by_cases ha : a < 0
  simp[abs,ha]
  use -1
  rw[← neg_mul_left,← neg_mul_right]
  simp
  simp[abs,ha]
  exact dvd_refl a

Conclusion "
"
