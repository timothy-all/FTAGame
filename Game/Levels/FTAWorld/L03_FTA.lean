-- import GameServer
import Game.Levels.FTAWorld.L02_FTA

World "FTAWorld"
Level 3
Title "Now this is what it's like when primes divide"

Introduction "
# **Level 3**
The only way that primes divide eachother is if they are equal.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
prime_dvd_prime : ∀ p q : Z, Prime p → Prime q → p ∣ q → p = q
```
If $p,q ∈ ℤ$ are primes such that $p ∣ q$, then $p = q$.
-/
TheoremDoc prime_dvd_prime as "FTA : prime_dvd_prime"


/-- If $p,q ∈ ℤ$ are primes such that $p ∣ q$, then $p = q$.-/
Statement prime_dvd_prime : ∀ p q : Z, Prime p → Prime q → p ∣ q → p = q := by
  intro p q hp hq hd
  obtain h := hq.right p (prime_pos p hp) hd
  rcases h with F | T
  obtain h := hp.left
  rw[F] at h
  simp at h
  exact T


Conclusion "
"
