-- import GameServer
import Game.Levels.OrderWorld.L09_order

World "OrderWorld"
Level 10
Title "Multiplying inequalities by positives"

Introduction "
# **Level 10**
Nothing super new here, just a useful theorem to explicitly have going forward. Have some rest at this site of grace.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
mul_on_left_lt : ∀ a b c : Z,
  0 < a → b < c → a * b < a * c
```
For all $a,b,c ∈ ℤ$, if $a$ is positive and $b < c$, then $ab < ac$
-/
TheoremDoc mul_on_left_lt as "Ord : mul_on_left_lt"

/-- For all $a,b,c ∈ ℤ$, if $a$ is positive and $b < c$, then $ab < ac$.-/
Statement mul_on_left_lt : ∀ a b c : Z, 0 < a → b < c → a * b < a * c := by
  intro a b c h1 h2
  rw[lt_def] at h1 h2 ⊢
  rw [neg_mul_right, ← mul_add]
  simp at h1
  exact mul_closure a (c + -b) h1 h2

Conclusion "
Easy peasy, lemon squeezy.
"
