-- import GameServer
import Game.Levels.DivisionWorld.L05_division

World "DivisionWorld"
Level 6
Title "The actual division algorithm"

Introduction "
# **Level 6**
This is the same statement as in the previous exercise, but we weaken the hypotheses. Instead of `hb : 0 < b` we merely have `hb : b ≠ 0`. **Hint:** no need to reinvent the wheel here.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
div_alg
  (a b : Z)
  (hb : b ≠ 0) :
  ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < abs b
```
For all $a, b ∈ ℤ$, if $b$ is nonzero, then there exists $q,r ∈ ℤ$ such that $a = bq + r$ and $0 ≤ r < |b|$.
-/
TheoremDoc div_alg as "Div : div_alg"

/-- For all $a, b ∈ ℤ$, if $b ≠ 0$, then there exists $q,r ∈ ℤ$ such that $a = bq + r$ and $0 ≤ r < |b|$.-/
Statement div_alg (a b : Z) (hb : b ≠ 0) : ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < abs b := by
  by_cases h : b < 0
  simp[abs,h]
  rw[lt_def,zero_add,mem_Zplus] at h
  obtain ⟨q,r,⟨eq,⟨le,lt⟩⟩⟩ := div_alg_pos a (-b) h
  use -q; use r
  refine ⟨?_,le,lt⟩
  rw[← neg_mul_right,neg_mul_left,eq]
  simp[abs,h]
  simp at h
  rcases h with rfl | T
  contradiction
  exact div_alg_pos a b T

Conclusion "
🙌 You've beaten Division World!
"
