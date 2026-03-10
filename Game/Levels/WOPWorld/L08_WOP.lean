-- import GameServer
import Game.Levels.WOPWorld.L07_WOP

World "WOPWorld"
Level 8
Title "Divides implies less-than-or-equal-to"

Introduction "
# **Level 8**
Boss fight! This one is important.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
dvd_le : ∀ a b : Z, a ∣ b → 0 < b → a ≤ b
```
For all integers $a,b$, if $a ∣ b$ and $b$ is positive, then $a ≤ b$.
-/
TheoremDoc dvd_le as "WOP : dvd_le"


/-- For all integers $a,b$, if $a ∣ b$ and $b$ is positive, then $a ≤ b$.-/
Statement dvd_le : ∀ a b : Z, a ∣ b → 0 < b → a ≤ b := by
  intro a b hab hb
  by_cases ha : a < 0
  right
  exact lt_trans a 0 b ha hb
  simp at ha
  rcases ha with rfl | apos
  simp[le_def,hb]
  by_contra! F
  rcases hab with ⟨d, rfl⟩
  apply nibzo d
  exact pos_mul_pos_left a d hb apos
  exact left_mul_cancel_lt a d apos F

Conclusion "
🔧 This theorem will be particularly important in **Prime World**.
"
