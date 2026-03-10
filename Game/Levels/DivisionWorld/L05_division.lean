-- import GameServer
import Game.Levels.DivisionWorld.L04_division

World "DivisionWorld"
Level 5
Title "The positive division algorithm"

Introduction "
# **Level 5**
This one is important, it's the linchpin for a lot of arguments involving division.
### ❯ The `by_wop!` tactic
We might find it helpful to use the newly unlocked `by_wop!` tactic in this level. 🔍 Check out the entry for `by_wop!` in the **Tactics** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The tactic `refine e` behaves like `exact e`, except that named (?x) or unnamed (?_) holes in `e` that are not solved by unification with the main goal's target type are converted into new goals, using the hole's name, if any, as the goal case name.

For example, this can be helpful for goals like `⊢ P₁ ∧ P₂ ∧ P₃ ∧ P₄`. Instead of calling `constructor` multiple times we could simply use:
```
refine ⟨?_,?_,?_,?_⟩
```
This will generate four subgoals of the corresponding type. If we have an **Assumption** like `h : P₃`, then we could use:
```
refine ⟨?_,?_,h,?_⟩
```
This will generate three subgoals of the corresponding type (the would-be third goal has been cleared with `exact h`).
-/
TacticDoc refine

/--
The same as
```
by_wop S with m ⟨patt⟩ hmin
```
but
```
by_wop! S with m ⟨patt⟩ hmin
```
will **keep** the hypothesis `hmem : m ∈ S` in addition to destructuring that hypothesis with `⟨patt⟩`. The former version destructures and **consumes** that hypothesis with `⟨patt⟩`.
-/
TacticDoc by_wop!

/--
As stated:
```
div_alg_pos
  (a b : Z)
  (hb : 0 < b) :
  ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < b
```
For all integers $a,b$, if $0 < b$, then there exists $q,r ∈ ℤ$ such that $a = bq + r$ and $0 ≤ r < b$.
-/
TheoremDoc div_alg_pos as "Div : div_alg_pos"

/-- For all integers $a,b$, if $0 < b$, then there exists $q,r ∈ ℤ$ such that $a = bq + r$ and $0 ≤ r < b$.-/
Statement div_alg_pos (a b : Z) (hb : 0 < b) : ∃ q r : Z, a = b * q + r ∧ 0 ≤ r ∧ r < b := by
  Hint "💡 We already know this statement is true if `b ∣ a`. Let's get that case out of the way..."
  by_cases hab : b ∣ a
  exact div_alg_dvd a b hb hab
  by_wop! Rem a b with r ⟨hr, ⟨ q, hq⟩⟩ rmin
  use q
  use r
  Hint "Our goal is a three-part conjunction. So we could use the `constructor` tactic but we'd have to use it twice (eventually). Instead, we could use...
  ### ❯ The `refine` tactic
  The `refine` tactic behaves as a sort of mix between `exact` and `constructor` (at least, in this case). 🔍 Check out the entry for `refine` in the **Tactics** tab. 👉 In this specific situation, try:
  ```
  refine ⟨?_,hr,?_⟩
  ```
  This will split our main goal into just two since we already know the middle part of the conjuntion is true (by the hypothesis `{hr}`).
  "
  refine ⟨?_,hr,?_⟩
  rw[add_comm,hq,add_assoc]
  simp
  by_contra! F
  obtain ⟨ r', hmem', F⟩ := divisor_le_rem a b r hb hmem F
  exact lt_self r (le_lt_trans r r' r (rmin r' hmem') F)
  exact not_dvd_pos a b hab
  obtain ⟨ q, hq⟩ := Archimedean a b hb
  use a + -(b * q)
  refine ⟨hq,?_⟩
  use q
  rfl

Conclusion "
The hypothesis `hb : 0 < b` was overkill; we really only need `b ≠ 0`. The next level will have you generalize `div_alg_pos` to this weaker hypothesis.
"

NewTactic by_wop! refine
