-- import GameServer
import Game.Levels.FTAWorld.L01_FTA

World "FTAWorld"
Level 2
Title "Primes dividing products"

Introduction "
# **Level 2**
***Mini boss fight!*** The result of this level is sometimes referred to as the **Fundamental Lemma**.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
prime_dvd_mul (a b p : Z) : Prime p → p ∣ a * b → (p ∣ a ∨ p ∣ b)
```
For all $a,b,p ∈ ℤ$, if $p$ is prime and $p ∣ ab$, then $p ∣ a$ or $p ∣ b$.
-/
TheoremDoc prime_dvd_mul as "FTA : prime_dvd_mul"

/-- For all $a,b,p ∈ ℤ$, if $p$ is prime and $p ∣ ab$, then $p ∣ a$ or $p ∣ b$.-/
Statement prime_dvd_mul (a b p : Z) : Prime p → p ∣ a * b → (p ∣ a ∨ p ∣ b) := by
  intro hp hd
  by_cases ha : p ∣ a
  left
  exact ha
  right
  obtain hg := gcd_prime_one a p hp ha
  obtain ⟨x,y,eq⟩ := Bezout a p
  rw[hg] at eq
  obtain eqb := mul_on_left (a * x + p * y) 1 b eq
  simp[mul_add] at eqb
  rw[← mul_assoc,← mul_assoc,mul_comm b,mul_comm b,mul_assoc p] at eqb
  obtain p_dvd := dvd_linear (a * b) p x (b * y) p hd (dvd_refl p)
  rw[eqb] at p_dvd
  exact p_dvd

Conclusion "
"
