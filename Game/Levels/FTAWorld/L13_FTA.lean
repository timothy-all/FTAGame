-- import GameServer
import Game.Levels.FTAWorld.L12_FTA


World "FTAWorld"
Level 13
Title "Uniqueness of prime factorizations"

Introduction "
# **Level 13**
***Final boss!***
"

variable {Z : Type} [RRZ : RossRing Z]

open List


/--
As stated:
```
fta_unique
  (P Q : List Z)
  (hP : List.prime P)
  (hQ : List.prime Q)
  (h : List.prod P = List.prod Q) :
  P ~ Q
```
If $P$ and $Q$ are lists of primes such that the product of all primes in the list $P$ is equal to the product of all primes in the list $Q$, then it must be that $P$ and $Q$ are permutations of each other.
-/
TheoremDoc fta_unique as "FTA : fta_unique"

Statement fta_unique
  (P Q : List Z)
  (hP : P.prime)
  (hQ : Q.prime)
  (h : P.prod = Q.prod) :
  P ~ Q := by
  by_contra! F
  by_wop (NUF : Set Z) with m hmS hmin
  obtain ⟨p,n,hp,eq,hnS⟩ := mem_NUF_mem m hmS
  obtain lt : n < m
  rw[eq]
  obtain pos := hpo n hnS
  rw[mem_Zplus] at pos
  exact pos_mul_prime p n pos hp
  exact lt_self m (le_lt_trans m n m (hmin n hnS) lt)
  intro s ⟨p,_,hp,_,sp,_,_⟩
  rw[sp,mem_Zplus]
  exact prime_prod_pos p hp
  use P.prod
  use P
  use Q
  simp
  refine ⟨?_,?_,?_,?_⟩
  exact hP
  exact hQ
  exact h
  exact F


Conclusion "
🙌 You've beaten the FTA game! Congrats!
"
