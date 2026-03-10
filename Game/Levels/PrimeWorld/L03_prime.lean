-- import GameServer
import Game.Levels.PrimeWorld.L02_prime

World "PrimeWorld"
Level 3
Title "No prime divides one"

Introduction "
# **Level 3**
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
prime_dvd_one : ∀ p : Z,
  Prime p → p ∣ 1 → False
```
No prime divides one.
-/
TheoremDoc prime_dvd_one as "Prm : prime_dvd_one"

/-- No prime divides one.-/
Statement prime_dvd_one : ∀ p : Z, Prime p → p ∣ 1 → False:= by
  intro p hp hd
  obtain F := dvd_le p 1 hd one_pos
  exact lt_self p (le_lt_trans p 1 p F hp.left)

Conclusion "
"
