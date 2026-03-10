-- import GameServer
import Game.Levels.PrimeWorld.L10_prime

World "PrimeWorld"
Level 11
Title "Prime factorizations exist"

Introduction "
# **Level 11**
***Big boss fight!*** This one will test your mettle -- it's the first half of **FTA**.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
fta_exists
  (a : Z)
  (lt_a : 1 < a) :
    ∃ P : List Z,
    List.prime P ∧ List.prod P = a
```
Every integer greater than $1$ factors into a product of primes.
-/
TheoremDoc fta_exists as "Prm : fta_exists"

Statement fta_exists
  (a : Z)
  (ha : 1 < a) :
  ∃ P : List Z, P.prime ∧ P.prod = a := by
  by_contra! F
  define S := { a : Z | 1 < a ∧ ∀ P : List Z, P.prime → ¬ P.prod = a}
  by_wop S with m hmS hmin
  by_cases mnp : Prime m
  obtain ⟨P,hP,hPm⟩ := prime_singleton m mnp
  exact (hmS.right P hP) hPm
  obtain ⟨p,hp,pdm⟩ := prime_div m hmS.left
  obtain ⟨n,eqm,hn,lt⟩ := factor_of_prime_dvd m p hmS.left mnp hp pdm
  by_cases hnS : n ∈ S
  exact lt_self m (le_lt_trans m n m (hmin n hnS) lt)
  simp[mem_def,S] at hnS
  obtain ⟨Q,hQ,eqn⟩ := hnS hn
  obtain ⟨P,hP,eqpn⟩ := prime_list_step p Q hp hQ
  rw[eqn,← eqm] at eqpn
  exact (hmS.right P hP) eqpn
  intro b hbS
  rw[mem_Zplus]
  exact lt_trans 0 1 b one_pos hbS.left
  use a
  exact And.intro ha F

Conclusion "
🙌 Congrats! You beat Prime World!
"
