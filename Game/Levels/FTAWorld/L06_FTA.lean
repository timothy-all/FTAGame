-- import GameServer
import Game.Levels.FTAWorld.L05_FTA

World "FTAWorld"
Level 6
Title "Products of prime lists are positive"

Introduction "
# **Level 6**
This exercise is intuitively clear but it ought to give us some easy practice with induction.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
As stated:
```
prime_prod_pos : ∀ l : List Z, l.prime → 0 < l.prod
```
A product of primes is positive.
-/
TheoremDoc prime_prod_pos as "FTA : prime_prod_pos"

/-- A product of primes is positive.-/
Statement prime_prod_pos : ∀ l : List Z, l.prime → 0 < l.prod := by
  intro l hl
  induction l
  rw[List.prod]
  exact one_pos
  rw[List.prod]
  obtain head_pos := prime_pos head (hl head (Mem.head tail))
  obtain tail_pos := tail_ih (prime_tail (head :: tail) hl)
  rw[← mem_Zplus] at head_pos tail_pos ⊢
  exact mul_closure head (tail.prod) head_pos tail_pos

Conclusion "
"
