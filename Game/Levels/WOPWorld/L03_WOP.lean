-- import GameServer
import Game.Levels.WOPWorld.L02_WOP

World "WOPWorld"
Level 3
Title "Minimums and maximums"

Introduction "
# **Level 3**
This level relates minimums to maximums of *flipped* sets.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
min_flip_max
  (S : Set Z)
  (u m: Z)
  (hmin : ∀ x :Z, x ∈ {y : Z | ∃ s ∈ S, y = u + -s} → m ≤ x) :
    ∀ x : Z, x ∈ S → x ≤ u + -m
```
Let $S$ be a non-empty set of integers, and let $u ∈ ℤ$. Suppose $m$ is a minimum of the set $\{ y ∈ ℤ ∣ ∃ s ∈ S, y = u + -s \}$. Then $u + -m$ is maximum of $S$.
-/
TheoremDoc min_flip_max as "WOP : min_flip_max"

/-- Let $S$ be a non-empty set of integers, and let $u ∈ ℤ$. Suppose $m$ is a minimum of the set $\{ y ∈ ℤ ∣ ∃ s ∈ S, y = u + -s \}$. Then $u + -m$ is maximum of $S$.-/
Statement min_flip_max
  (S : Set Z)
  (u m : Z)
  (hmin : ∀ x : Z, x ∈ {y : Z | ∃ s ∈ S, y = u + -s} → m ≤ x) :
    ∀ x : Z, x ∈ S → x ≤ u + -m := by
  intro x hxS
  Hint "👉 You might try a proof by contradiction."
  by_contra! F
  obtain hux := mem_flip_set S u x hxS
  obtain m_le := hmin (u + -x) hux
  obtain m_gt := add_neg_lt_swap u m x F
  exact lt_self m (le_lt_trans m (u + -x) m m_le m_gt)


Conclusion "
"
