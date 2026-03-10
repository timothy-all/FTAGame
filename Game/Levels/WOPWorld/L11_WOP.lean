-- import GameServer
import Game.Levels.WOPWorld.L10_WOP

World "WOPWorld"
Level 11
Title "A necessary and sufficient condition for divides"

Introduction "
# Level 11
Boss fight! This is sometimes called the **Archimedean** property of $ℤ$.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
induction_principle (P : Z → Prop)
  (base : P 1)
  (indh : ∀ k : Z, P k → P (k + 1)) :
  (∀ n : Z, 1 ≤ n → P n)
```
Suppose $P$ is a predicate with an integer argument. If $P(1)$ is true and for all $k ∈ ℤ$, $P(k)$ implies $P(k+1)$, then $P(n)$ is true for all $n ≥ 1$.
-/
TheoremDoc induction_principle as "WOP : induction_principle"

/-- Suppose $P$ is a predicate with an integer argument. If $P(1)$ is true and for all $k ∈ ℤ$, $P(k)$ implies $P(k+1)$, then $P(n)$ is true for all $n ≥ 1$.-/
theorem induction_principle (P : Z → Prop)
  (base : P 1)
  (indh : ∀ k : Z, P k → P (k + 1)) :
  (∀ n : Z, 1 ≤ n → P n) := by
  intro n hn
  by_contra! F
  define S := { s : Z | 0 < s ∧ ¬ P s}
  by_wop S with m hmS hmin
  obtain lt : 1 < m
  by_contra! le
  rcases le with eq | lt
  rw[eq] at hmS
  exact hmS.right base
  exact nibzo m hmS.left lt
  rw[lt_def,mem_Zplus] at lt
  obtain mem : m + -1 ∈ S
  constructor
  exact lt
  by_contra F'
  obtain F'' := indh (m + -1) F'
  simp[add_assoc] at F''
  exact hmS.right F''
  obtain F' := tle_sub_imp_nonpos m 1 (hmin (m + -1) mem)
  exact lt_self 1 (le_lt_trans 1 0 1 F' one_pos)
  intro s hs
  simpa[mem_Zplus] using hs.left
  use n
  constructor
  rcases hn with eq | lt
  rw[← eq]
  exact one_pos
  exact lt_trans 0 1 n one_pos lt
  exact F


Conclusion "
🙌 Congrats! You've cleared WOPWorld!
"
