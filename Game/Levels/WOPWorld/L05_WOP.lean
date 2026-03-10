-- import GameServer
import Game.Levels.WOPWorld.L04_WOP

World "WOPWorld"
Level 5
Title "Strictly bounded vs bounded"

Introduction "
# **Level 5**
We'd like to improve the last theorem `POW_strict`. This exercise will help.

💪 **Challenge:** try to complete this level using 5 tactic calls or less.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
bdd_imp_strict_bdd
  (S : Set Z)
  (u : Z)
  (umax : ∀ x ∈ S, x ≤ u) :
    (∃ U : Z, ∀ x ∈ S, x < U)
```
If $S$ is a set and $u ∈ ℤ$ such that for all $x ∈ S$, we have $x ≤ u$, then there exists $u' ∈ ℤ$ such that for all $x ∈ S$, we have $x < u'$.
-/
TheoremDoc bdd_imp_strict_bdd as "WOP : bdd_imp_strict_bdd"

/-- If $S$ is bounded above, then $S$ can be strictly bounded above.-/
Statement bdd_imp_strict_bdd (S : Set Z) (u : Z) (umax : ∀ x ∈ S, x ≤ u) : (∃ U : Z, ∀ x ∈ S, x < U) := by
  use (u + 1)
  intro x hxS
  obtain hmax := umax x hxS
  obtain h:= add_le_lt x u 0 1 hmax one_pos
  simpa[h] using h

Conclusion "
"
