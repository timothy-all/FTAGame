-- import GameServer
import Game.Levels.WOPWorld.L06_WOP

World "WOPWorld"
Level 7
Title "No integer between zero and one"

Introduction "
# **Level 7**
Here we prove that there is **n**o **i**nteger **b**etween **z**ero and **o**ne.
### 🔧 The `And.intro` constructor
Suppose we have two assumptions `h₁` and `h₂` but we really need the assumption `h : h₁ ∧ h₂`. The *constructor* for the `∧` connective is `And.intro`. 🔍 Check out the entry for `And.intro` in the **Definitions** tab. For example:
```
obtain h := And.intro h₁ h₂
```
generates the hypothesis `h : h₁ ∧ h₂`. In general, if we need to glue a couple assumptions together with `∧`, then `And.intro` is the tool. This may be helpful in this exercise.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
nibzo : ∀ a : Z, 0 < a → a < 1 → False
```
There does not exist an integer $x$ such that $0 < x$ and $x < 1$.
-/
TheoremDoc nibzo as "WOP : nibzo"

/--
This is the constructor the `∧` operator. Specifically,
```
And.intro : p → q → p ∧ q
```
-/
DefinitionDoc And.intro as "And.intro"


/-- There does not exist an integer strictly greater than zero but strictly less than one.-/
Statement nibzo : ∀ a : Z, 0 < a → a < 1 → False := by
  intro a pos lt1
  Hint "Let's build a relevant set."
  define S := { x : Z | 0 < x ∧ x < 1}
  by_wop S with m hmS hmin
  obtain mm_lt_m := mul_on_left_lt m m 1 hmS.left hmS.right
  obtain mm_pos := mul_on_left_lt m 0 m hmS.left hmS.left
  simp at mm_pos mm_lt_m
  obtain hmmS : m * m ∈ S := And.intro mm_pos (lt_trans (m * m) m 1 mm_lt_m hmS.right)
  exact lt_self m (le_lt_trans m (m * m) m (hmin (m * m) hmmS) mm_lt_m)
  Hint "We now must prove `{S} ⊆ Z⁺`."
  intro x ⟨ xpos,_⟩
  simpa[lt_def] using xpos
  Hint "We now must prove `{S} ≠∅`."
  use a
  exact And.intro pos lt1

Conclusion "
🔧 The theorem `nibzo` is often the last call in proofs by contradiction. And hopefully we're getting used to WOP proofs and the `by_wop` tactic.
"

NewDefinition And.intro
