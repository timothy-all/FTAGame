-- import GameServer
import Game.Levels.PrimeWorld.L07_prime

World "PrimeWorld"
Level 8
Title "Primes are magnifiers"

Introduction "
# **Level 8**
This level is straightforward and will give us a break from lists.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
pos_mul_prime : ∀ p n : Z,
  0 < n → Prime p → n < p * n
```
For all $p,n ∈ ℤ$, if $n$ is positive and $p$ is prime, then $n < pn$.
-/
TheoremDoc pos_mul_prime as "Prm : pos_mul_prime"

/-- For all $p,n ∈ ℤ$, if $n$ is positive and $p$ is prime, then $n < pn$.-/
Statement pos_mul_prime : ∀ p n : Z, 0 < n → Prime p → n < p * n := by
  intro p q hq hp
  obtain h := mul_on_left_lt q 1 p hq hp.left
  rw[mul_one,mul_comm] at h
  exact h

Conclusion "
"
