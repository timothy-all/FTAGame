-- import GameServer
import Game.Levels.DivisionWorld


World "GCDWorld"
Level 1
Title "Common divisors are bounded"

Introduction "
# **Level 1**
This exercise will be crucial for the next boss fight.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
bdd_divisors
  (a b : Z)
  ( hab : ¬ (a = 0 ∧ b = 0) ) :
  ∃ u : Z, ∀ x : Z, x ∈ {d : Z | d ∣ a ∧ d ∣ b} → x ≤ u
```
Let $a,b ∈ ℤ$. If $d ∈ ℤ$ such that $d ∣ a $ and $d ∣ b$, we call $d$ a **common divisor** of $a$ and $b$. If at least one of $a$ or $b$ is non-zero, then the set of common divisors of $a$ and $b$ is bounded above.
-/
TheoremDoc bdd_divisors as "GCD : bdd_divisors"

/-- As long as one of $a$ or $b$ is non-zero, then the set of common divisors of $a$ and $b$ is bounded above.-/
Statement bdd_divisors (a b : Z) ( hab : ¬ (a = 0 ∧ b = 0) ) : ∃ u : Z, ∀ x : Z, x ∈ {d : Z | d ∣ a ∧ d ∣ b} → x ≤ u := by
  by_cases h : a = 0
  simp at hab
  obtain hb := hab h
  use abs b
  intro x hx
  exact dvd_le x (abs b) (dvd_trans x b (abs b) hx.right (dvd_abs b)) (abs_pos b hb)
  use abs a
  intro x hx
  exact dvd_le x (abs a) (dvd_trans x a (abs a) hx.left (dvd_abs a)) (abs_pos a h)

Conclusion "
Next up: an important boss.
"
