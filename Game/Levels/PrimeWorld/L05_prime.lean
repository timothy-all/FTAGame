-- import GameServer
import Game.Levels.PrimeWorld.L04_prime

World "PrimeWorld"
Level 5
Title "Divisble by a prime"

Introduction "
# **Level 5**
***Boss fight!*** This is a crucial step towards FTA!
"

variable {Z : Type} [RRZ : RossRing Z]



/--
As stated:
```
prime_div : ∀ a : Z, 1 < a →
  ∃ p : Z, Prime p ∧ p ∣ a
```
For all $a ∈ ℤ$, if $1 < a$, then there exists a prime $p$ such that $p ∣ a$.
-/
TheoremDoc prime_div as "Prm : prime_div"

Statement prime_div : ∀ a : Z, 1 < a → ∃ p : Z, Prime p ∧ p ∣ a := by
  intro a ha
  by_contra! F
  define S := { a : Z | 1 < a ∧ ∀ p : Z, Prime p → ¬ p ∣ a}
  by_wop S with m ⟨ hm, npf⟩ hmin
  by_cases mnp : Prime m
  exact (npf m mnp) (dvd_refl m)
  obtain ⟨n,hn,ndm,lt⟩ := composite m hm mnp
  by_cases hnS : n ∈ S
  exact lt_self m (le_lt_trans m n m (hmin n hnS) lt)
  simp[mem_def,S] at hnS
  obtain ⟨p,hp,pdn⟩ := hnS hn
  exact (npf p hp) (dvd_trans p n m pdn ndm)
  intro s hs
  simp[mem_Zplus]
  exact lt_trans 0 1 s one_pos hs.left
  use a
  exact And.intro ha F

Conclusion "
"
