-- import GameServer
import Game.Levels.PrimeWorld.L08_prime

World "PrimeWorld"
Level 9
Title "Cofactors of primes for composites are proper"

Introduction "
# **Level 9**
This level is harder, but doesn't involve lists either.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
factor_of_prime_dvd
  (m p : Z)
  (lt : 1 < m)
  (hm : ¬ Prime m)
  (hp : Prime p)
  (hmp :  p ∣ m) :
    ∃ n : Z, m = p * n ∧ 1 < n ∧ n < m
```
For all $m,p ∈ ℤ$, if $1 < m$, $m$ is not prime, $p$ is prime, and $p ∣ m$, then there exists an integer $q$ such that $m = pq$ and $1 < q$ and $q < p$. In other words, if $m$ isn't prime and $p$ is a prime factor, then the other factor is proper.
-/
TheoremDoc factor_of_prime_dvd as "Prm : factor_of_prime_dvd"

/-- For all $m,p ∈ ℤ$, if $1 < m$ and $p$ is prime factor of $m$, say $pq = m$, then $q$ is a proper factor of $m$ (greater than $1$ but less than $m$).-/
Statement factor_of_prime_dvd (m p : Z) (lt : 1 < m) (hm : ¬ Prime m) (hp : Prime p) (hmp :  p ∣ m) : ∃ n : Z, m = p * n ∧ 1 < n ∧ n < m := by
  rcases hmp with ⟨n, hn⟩
  use n
  Hint "It's helpful to obtain the hypothesis that `0 < n` **before** separating the conjunction in the goal."
  obtain mpos := lt_trans 0 1 m one_pos lt
  rw[hn] at mpos
  obtain npos := pos_mul_pos_left p n mpos (prime_pos p hp)
  refine ⟨hn,?_,?_⟩
  by_contra! F
  rcases F with F1 | F2
  rw[F1,mul_one] at hn
  rw[hn] at hm
  contradiction
  exact nibzo n npos F2
  rw[hn]
  exact pos_mul_prime p n npos hp

Conclusion "
"
