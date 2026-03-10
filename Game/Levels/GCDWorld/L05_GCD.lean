-- import GameServer
import Game.Levels.GCDWorld.L04_GCD

World "GCDWorld"
Level 5
Title "The set Bez is non-empty : Part 1"

Introduction "
# **Level 2**
Before we go on a wild goose chase, it would be good to know that `Bez` is non-empty.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
Bezout_ne (a b : Z)
  (ha : a ≠ 0) :
  Bez a b ≠∅
```
For all $a,b ∈ ℤ$ , if at least one of $a$ or $b$ is nonzero,then the set

$$ \{d ∈ ℤ : 0 < d ∧ ∃ m,n ∈ ℤ, ma + nb = d\} $$

is nonempty.
-/
TheoremDoc Bezout_ne_left as "GCD : Bezout_ne_left"

/-- For all $a,b ∈ ℤ$, if $a ≠ 0$, then the set of all positive linear combinations of $a$ and $b$ is nonempty.-/
Statement Bezout_ne_left (a b : Z)
  (ha : a ≠ 0 ) :
  Bez a b ≠∅ := by
  use abs a
  constructor
  exact abs_pos a ha
  obtain hd := dvd_abs a
  rcases hd with ⟨ x, hx⟩
  symm at hx
  use x ; use 0
  simp[hx]

Conclusion "
But what if `b ≠ 0`... is `Bez a b` non-empty then?
"
