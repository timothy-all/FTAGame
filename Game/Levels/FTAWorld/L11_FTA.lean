-- import GameServer
import Game.Levels.FTAWorld.L10_FTA

World "FTAWorld"
Level 11
Title "Members of NUF are greater than 1"

Introduction "
# **Level 11**
We introduce the set `NUF` consisting of all those integers that do **N**ot **U**uniquely **F**factor into a product of primes. 🔍 Check out the entry for `NUF` in the **Definitions** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

def NUF : Set Z :=
  {s : Z | ∃ P Q : List Z, P.prime ∧ Q.prime ∧ s = P.prod ∧ s = Q.prod ∧ ¬ P ~ Q}


/--
The set `NUF` represents the set of integers that do **N**ot **U**uniquely **F**factor into a product of primes. Here's how it's defined in Lean:
```
def NUF : Set Z :=
  {s : Z | ∃ P Q : List Z,
  P.prime ∧ Q.prime ∧ s = P.prod ∧ s = Q.prod ∧ ¬ P ~ Q}
```
-/
DefinitionDoc NUF as "NUF"

/--
As stated:
```
mem_FTA_gt_one
  (m : Z)
  (hm : m ∈ FTA) :
  1 < m
```
A member of the set `NUF` must be greater than one.
-/
TheoremDoc mem_NUF_gt as "FTA : mem_NUF_gt_one"


/-- A member of the set `NUF` must be greater than one.-/
Statement mem_NUF_gt
  (m : Z)
  (hm : m ∈ NUF) :
  1 < m := by
  rcases hm with ⟨P,Q,hP,hQ,sP,sQ,nP⟩
  obtain mpos := prime_prod_pos P hP
  rw[← sP] at mpos
  by_contra! F
  rcases F with eq | lt
  rw[eq] at sP sQ
  symm at sP sQ
  obtain Pempty := prime_prod_empty P hP sP
  obtain Qempty := prime_prod_empty Q hQ sQ
  rw[Pempty,Qempty] at nP
  simp at nP
  exact nibzo m mpos lt

Conclusion "
We're getting ready for the big kahuna. This was pretty much the **base case**.
"

NewDefinition NUF
