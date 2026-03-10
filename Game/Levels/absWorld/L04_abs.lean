-- import GameServer
import Game.Levels.absWorld.L03_abs

World "absWorld"
Level 4
Title "Positive absolute values"

Introduction "
# **Level 4**
This will be useful to know going forward.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
abs_pos : ∀ a : Z, a ≠ 0 → 0 < abs a
```
For all $a ∈ ℤ$, if $a$ is nonzero, then $0 < |a|$.
-/
TheoremDoc abs_pos as "Abs : abs_pos"


/-- For all $a ∈ ℤ$, if $a$ is nonzero, then $0 < |a|$.-/
Statement abs_pos : ∀ a : Z, a ≠ 0 → 0 < abs a := by
  intro a ha
  by_cases h : a < 0
  simp[abs,h]
  rw[lt_def] at h ⊢
  simp at ⊢ h
  exact h
  simp[abs,h]
  simp at h
  rcases h with F | T
  symm at F
  contradiction
  exact T


Conclusion "
"
