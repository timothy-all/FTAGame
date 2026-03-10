-- import GameServer
import Game.Levels.GCDWorld.L05_GCD

World "GCDWorld"
Level 6
Title "The set Bez is non-empty : Part 2"

Introduction "
# **Level 6**
Don't work too hard here.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
Bezout_ne (a b : Z)
  (hab : ¬ (a = 0 ∧ b = 0)) :
  {d : Z | 0 < d ∧ ∃ m n : Z, m * a + n * b = d} ≠∅
```
For all $a,b ∈ ℤ$ , if at least one of $a$ or $b$ is nonzero,then the set

$$ \{d ∈ ℤ : 0 < d ∧ ∃ m,n ∈ ℤ, ma + nb = d\} $$

is nonempty.
-/
TheoremDoc Bezout_ne as "GCD : Bezout_ne"

/-- For all $a,b ∈ ℤ$, if $a ≠ 0$, then the set of all positive linear combinations of $a$ and $b$ is nonempty.-/
Statement Bezout_ne (a b : Z)
  (h : ¬ (a = 0 ∧ b = 0) ) :
  Bez a b ≠∅ := by
  simp at h
  by_cases ha : a = 0
  obtain hb := h ha
  obtain ⟨d,hd⟩ := Bezout_ne_left b a hb
  use d
  exact (Bez_symm a b).right d hd
  exact Bezout_ne_left a b ha

Conclusion "
"
