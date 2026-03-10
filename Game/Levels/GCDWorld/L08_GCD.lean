-- import GameServer
import Game.Levels.GCDWorld.L07_GCD

World "GCDWorld"
Level 8
Title "The minimum of Bez : Part 1"

Introduction "
# **Level 8**
This is a crucial step towards proving Bezout's Theorem.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
Bezout_min_dvd (a b m: Z)
  (hmB : m ∈ Bez a b)
  (hmin: ∀ s ∈ Bez a b, m ≤ s) :
  m ∣ a
```
For all $a,b ∈ ℤ$, if $m$ is a minimal positive linear combination of $a$ and $b$, then $m$ divides $a$.
-/
TheoremDoc Bezout_min_dvd_left as "GCD : Bezout_min_dvd_left"

/-- For all $a,b ∈ ℤ$, if $m$ is a minimal positive linear combination of $a$ and $b$, then $m$ divides $a$.-/
Statement Bezout_min_dvd_left (a b m: Z)
  (hmB : m ∈ Bez a b)
  (hmin: ∀ s ∈ Bez a b, m ≤ s) :
  m ∣ a := by
  by_cases hm : m = 0
  obtain F := hmB.left
  rw[hm] at F
  simp at F
  obtain ⟨q,r,⟨eq,nonneg,lt⟩⟩ := div_alg a m hm
  rcases nonneg with T | F
  use q
  rw[← T,add_zero] at eq
  exact eq
  obtain hrB : r ∈ Bez a b := div_alg_mem_Bez a b m q r hmB eq F
  obtain m_abs := abs_eq m hmB.left
  rw[← m_abs] at lt
  obtain F' := lt_self m (le_lt_trans m r m (hmin r hrB) lt)
  contradiction


Conclusion "
Does the minimum of `Bez a b` divide `b` too?
"
