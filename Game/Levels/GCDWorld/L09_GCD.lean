-- import GameServer
import Game.Levels.GCDWorld.L08_GCD

World "GCDWorld"
Level 9
Title "The minimum of Bez : Part 2"

Introduction "
# **Level 9**
Once again, don't work too hard here.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
Bezout_min_dvd (a b m: Z)
  (hmB : m ∈ Bez a b)
  (hmin: ∀ s ∈ Bez a b, m ≤ s) :
  m ∣ a ∧ m ∣ b
```
For all $a, b ∈ ℤ$, if $m$ is a minimal positive linear combination of $a$ and $b$, then $m$ divides $a$ and $m$ divides $b$.
-/
TheoremDoc Bezout_min_dvd as "GCD : Bezout_min_dvd"

/-- For all $a, b ∈ ℤ$, if $m$ is a minimal positive linear combination of $a$ and $b$, then $m$ divides $a$ and $m$ divides $b$.-/
Statement Bezout_min_dvd (a b m: Z)
  (hmB : m ∈ Bez a b)
  (hmin: ∀ s ∈ Bez a b, m ≤ s) :
  m ∣ a ∧ m ∣ b := by
  constructor
  exact Bezout_min_dvd_left a b m hmB hmin
  obtain hmB' : m ∈ Bez b a := (Bez_symm a b).left m hmB
  obtain hmin' : ∀ s ∈ Bez b a, m ≤ s
  intro s hs
  obtain hs' := (Bez_symm a b).right s hs
  exact hmin s hs'
  exact Bezout_min_dvd_left b a m hmB' hmin'


Conclusion "
"
