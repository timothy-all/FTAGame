-- import GameServer
import Game.Levels.GCDWorld
import Game.Levels.PrimeWorld


World "FTAWorld"
Level 1
Title "Greatest common divisors are positive"

Introduction "
# **Level 1**
This level combines what we know from **GCD World** and **Prime World**.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
gcd_prime_one : ∀ a p : Z, Prime p → ¬ p ∣ a → (gcd a p).g = 1
```
For all $a, p ∈ ℤ$, if $p$ is prime and $p$ does not divide $a$, then $\gcd(a,p) = 1$.
-/
TheoremDoc gcd_prime_one as "FTA : gcd_prime_one"

/-- For all $a, p ∈ ℤ$, if $p$ is prime and $p$ does not divide $a$, then $\gcd(a,p) = 1$.-/
Statement gcd_prime_one : ∀ a p : Z, Prime p → ¬ p ∣ a → (gcd a p).g = 1 := by
  intro a p hp npda
  obtain gpos := gcd_pos a p (prime_ne_zero p hp)
  obtain T | F := hp.right (gcd a p).g gpos (gcd a p).right
  exact T
  obtain pda := (gcd a p).left
  rw[F] at pda
  contradiction

Conclusion "
"
