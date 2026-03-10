-- import GameServer
import Game.Levels.GCDWorld.L05_GCD


World "GCDWorld"
Level 6
Title "Greatest common divisors are positive"

Introduction "
# Level 6

"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
gcd_prime_one : ∀ a p : Z, Prime p → ¬ p ∣ a → (gcd a p).g = 1
```
For all $a, p ∈ ℤ$, if $p$ is prime and $p$ does not divide $a$, then $\gcd(a,p) = 1$.
-/
TheoremDoc gcd_prime_one as "gcd_prime_one"

/-- For all $a, p ∈ ℤ$, if $p$ is prime and $p$ does not divide $a$, then $\gcd(a,p) = 1$.-/
Statement test (a b : Z) (hb : b ≠ 0) : (gcd a b).g = (gcd b (divalg a b hb).r).g := by
  by_cases h : ¬ (a = 0 ∧ (divalg a b hb).r = 0)
  obtain h1 := dvd_rem a b (gcd a b).g hb (gcd a b).left (gcd a b).right
  obtain h2 := (gcd a b).right
  obtain h3 := (gcd a (divalg a b hb).r).max h (gcd a b).g (gcd a b).left h1
  sorry
  sorry

Conclusion "
"
