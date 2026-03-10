-- import GameServer
import Game.Levels.PrimeWorld.L09_prime

World "PrimeWorld"
Level 10
Title "Enlarging prime lists"

Introduction "
# **Level 10**
Back to lists! This one isn't so bad though.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
prime_list_step
  (p : Z)
  (Q : List Z)
  (hp : Prime p)
  (hQ : Q.prime) :
    ∃ M : List Z, M.prime ∧ M.prod = p * Q.prod
```
-/
TheoremDoc prime_list_step as "Prm : prime_list_step"

Statement prime_list_step (p : Z) (Q : List Z) (hp : Prime p) (hQ : Q.prime) : ∃ M : List Z, M.prime ∧ M.prod = p * Q.prod := by
  use (p :: Q)
  constructor
  rw[List.prime]
  simp
  constructor
  exact hp
  intro a ha
  exact hQ a ha
  rw[List.prod]

Conclusion "
"
