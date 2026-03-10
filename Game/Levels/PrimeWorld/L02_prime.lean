-- import GameServer
import Game.Levels.PrimeWorld.L01_prime

World "PrimeWorld"
Level 2
Title "Primes are positive"

Introduction "
# **Level 2**
This one isn't so hard either, but it's good to have in the inventory.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
prime_pos : ∀ p : Z, Prime p → 0 < p
```
For all $p ∈ ℤ$, if $p$ is prime, then $0 < p$.
-/
TheoremDoc prime_pos as "Prm : prime_pos"

/-- Primes are positive.-/
Statement prime_pos : ∀ p : Z, Prime p → 0 < p:= by
  intro p hp
  obtain one_pos : (0 : Z) < 1 := one_pos
  exact lt_trans 0 1 p one_pos hp.left

Conclusion "
"
