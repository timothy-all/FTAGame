-- import GameServer
import Game.Levels.FTAWorld.L11_FTA


World "FTAWorld"
Level 12
Title "A smaller member of NUF"

Introduction "
# **Level 12**
This one is tough.
"

variable {Z : Type} [RRZ : RossRing Z]

open List
/--
As stated:
```
mem_NUF_mem
  (m : Z)
  (hmS : m ∈ NUF) :
  ∃ p n: Z, Prime p ∧ m = p * n ∧ n ∈ NUF
```
If $m$ is an element of `NUF`, then there exists a prime $p$ and an integer $n$ such that $m = pn$, and $n$ is also an element of `NUF`.
-/
TheoremDoc mem_NUF_mem as "FTA : mem_NUF_mem"


/-- If $m$ is an element of `NUF`, then there exists a prime $p$ and an integer $n$ such that $m = pn$, and $n$ is also an element of `NUF`. -/
Statement mem_NUF_mem
  (m : Z)
  (mem : m ∈ NUF) :
  ∃ p n: Z, Prime p ∧ m = p * n ∧ n ∈ NUF := by
  obtain ⟨p,hp,hd⟩ := prime_div m (mem_NUF_gt m mem) --get p
  use p
  simp[hp]
  rcases mem with ⟨P,Q,hP,hQ,mP,mQ,np⟩ -- destructure m ∈ NUF
  obtain ⟨Pt, hPt⟩ := mem_perm_cons p P (prime_dvd_prod p P hP hp (Eq.subst mP hd)) --get Pt
  use Pt.prod
  constructor --for existential of statement
  obtain eq := prod_perm_eq_self P (p :: Pt) hPt
  rw[mP,eq,List.prod] -- finished with left
  obtain ⟨Qt, hQt⟩ := mem_perm_cons p Q (prime_dvd_prod p Q hQ hp (Eq.subst mQ hd)) --get Qt
  use Pt ; use Qt --start of Pt ∈ FTA, obviously we use Pt,Qt as witnesses
  refine ⟨?_,?_,rfl,?_,?_⟩ --refine the crap out of the membership prop
  exact prime_tail (p :: Pt) (perm_prime P (p :: Pt) hP hPt) --Pt prime
  exact prime_tail (p :: Qt) (perm_prime Q (p :: Qt) hQ hQt) --Qt prime
  obtain eq1 := prod_perm_eq_self (p :: Pt) P (Perm.symm hPt)
  obtain eq2 := prod_perm_eq_self Q (p :: Qt) hQt
  rw[← mP,mQ,eq2,List.prod,List.prod] at eq1
  exact left_mul_cancel p (List.prod Pt) (List.prod Qt) (prime_ne_zero p hp) eq1
  by_contra F
  obtain F' := Perm.cons p F
  exact np (Perm.trans hPt (Perm.trans F' (Perm.symm hQt)))


Conclusion "
This was a sort-of **inductive step**. And now for the final boss...
"


NewDefinition Eq.subst
