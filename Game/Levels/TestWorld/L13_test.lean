-- import GameServer
import Game.Levels.TestWorld.L12_test

World "RingWorld"
Level 13
Title "Divides is reflexive"

Introduction "
# **Level 13**
Let's get more practice with the `use` tactic.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
one_dvd : ∀ a : Z, 1 ∣ a
```
For all $a ∈ ℤ$, $1$ divides $a$.
-/
TheoremDoc one_dvd as "Rng : one_dvd"

/-- For all $a ∈ ℤ$, $1$ divides $a$.-/
Statement one_dvd : ∀ a : Z, 1 ∣ a := by
  intro a
  Hint "### 💡 Pro-tip
  We do **not** need to `rw[dvd_def]`. Lean knows that `1 ∣ a` is an existential. We need only suppy a witness."
  use a
  rw[mul_comm,mul_one]

Conclusion "
Next up: we'll show that *divides* is transitive.
"
