-- import GameServer
import Game.Levels.WOPWorld.L05_WOP

World "WOPWorld"
Level 6
Title "POW"

Introduction "
# **Level 6**
This version of `POW_strict` allows for the `umax` hypothesis to be based on `≤` and not the stricter `<`.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
POW
  (S : Set Z)
  (S_ne : S ≠∅)
  (u : Z)
  (umax : ∀ x ∈ S, x ≤ u) :
    (∃ M ∈ S, ∀ x ∈ S, x ≤ M)
```
If $S$ is a non-empty subset of positive integers that is bounded above, then $S$ contains a largest element. More precisely, for every $S ⊆ ℤ$, if $S ≠ ∅$ and there exists $u ∈ ℤ$ such that for all $x ∈ S$, $x < u$, then there exists $M ∈ S$, such that for all $x ∈ S$, $x ≤ M$.
-/
TheoremDoc POW as "WOP : POW"


/-- If $S$ is a non-empty subset of positive integers that is bounded above, then $S$ contains a largest element.-/
Statement POW (S : Set Z) (S_ne : S ≠∅) (hbd : ∃ u : Z, ∀ x ∈ S, x ≤ u) : (∃ M ∈ S, ∀ x ∈ S, x ≤ M) := by
  rcases hbd with ⟨u, umax⟩
  obtain ⟨ u',u'max⟩ := bdd_imp_strict_bdd S u umax
  exact POW_strict S S_ne u' u'max


Conclusion "
"
