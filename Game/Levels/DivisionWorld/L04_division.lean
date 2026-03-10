-- import GameServer
import Game.Levels.DivisionWorld.L03_division

World "DivisionWorld"
Level 4
Title "The baby division algorithm"

Introduction "
# **Level 4**
A warm-up for the final showdown.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
div_alg_dvd (a b: Z) :
  0 < b → b ∣ a →
  ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < b
```
For all integers $a,b$, if $0 < b$ and $b ∣ a$, then there exists $q,r ∈ ℤ$ such that $a = bq + r$ and $0 ≤ r < b$.
-/
TheoremDoc div_alg_dvd as "Div : div_alg_dvd"

Statement div_alg_dvd (a b: Z) : 0 < b → b ∣ a → ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < b := by
  intro hb hab
  rcases hab with ⟨ q, hq⟩
  use q
  use 0
  constructor
  rw[add_zero]
  exact hq
  constructor
  left
  rfl
  exact hb


Conclusion "
"
