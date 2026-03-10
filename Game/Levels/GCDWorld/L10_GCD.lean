-- import GameServer
import Game.Levels.GCDWorld.L09_GCD

World "GCDWorld"
Level 10
Title "Bezout's Theorem"

Introduction "
# **Level 10**
**Boss Fight!** We prove Bezout's theorem in this level.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
Bezout
  (a b : Z) :
  ∃ x y : Z, a * x + b * y = (gcd a b).g
```
For all $a, b ∈ ℤ$, there $\gcd(a,b)$ is a linear combination of $a$ and $b$.
-/
TheoremDoc Bezout as "GCD : Bezout"

/-- For all $a, b ∈ ℤ$, there $\gcd(a,b)$ is a linear combination of $a$ and $b$.-/
Statement Bezout (a b : Z) : ∃ x y : Z, a * x + b * y = (gcd a b).g := by
  by_cases h : a = 0 ∧ b = 0
  use 0; use 0;
  simp[h,gcd]
  by_wop (Bez a b) with m hmB hmin
  obtain md := Bezout_min_dvd a b m hmB hmin
  obtain le := (gcd a b).le h m md.left md.right
  obtain ⟨u,v,eq⟩ := hmB.right
  obtain gdm := dvd_linear a b u v (gcd a b).g (gcd a b).left (gcd a b).right
  rw[eq] at gdm
  obtain glem := dvd_le (gcd a b).g m gdm hmB.left
  rcases le with T | F
  use u; use v
  rw[← T]
  exact eq
  obtain F := lt_self (gcd a b).g (le_lt_trans (gcd a b).g m (gcd a b).g glem F)
  contradiction
  intro d hd
  rw[mem_Zplus]
  exact hd.left
  exact Bezout_ne a b h

Conclusion "
🙌 You've beaten Bezout World! ***Congrats!***
"
