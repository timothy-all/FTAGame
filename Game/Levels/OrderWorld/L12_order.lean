-- import GameServer
import Game.Levels.OrderWorld.L11_order

World "OrderWorld"
Level 12
Title "Dichotomy"

Introduction "
# **Level 12**
We'll need a new tactic for this level.
### ❯ The `by_cases` tactic
  In order to prove a disjunction like `P ∨ Q` it can be handy to breakdown into cases introduced by us. Specifically, if `P` is true, then we're done (this is the first case). If `¬ P` is true, then we should try to prove that `Q` is true specifically (this is the second case). In general, we use the `by_cases` tactic to split our goal in this fashion. 🔍 Check out the documentation for `by_cases` in the **Tactics** tab. 👉 In our situation, try:
  ```
  by_cases aplus : a ∈ Zplus
  ```
### **⌨ Typesetting-tip**
The symbol `∈` is typeset with `\\in`.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
ne_zero_dichotomy
  (a : Z)
  (ha : a ≠ 0) :
    (a ∈ Zplus ∨ -a ∈ Zplus)
```
For all $a ∈ ℤ$, if $a ≠ 0$, then $a ∈ Z⁺$ or $-a ∈ Z⁺$.
-/
TheoremDoc ne_zero_dichotomy as "Ord : ne_zero_dichotomy"

/--
The tactic
```
by_cases h : P
```
will split the goal into two cases. The first case will have the assumption `h : P`. The second case will have the assumption `h : ¬ P`.
-/
TacticDoc by_cases

/-- If an integer is non-zero, then either it is positive or its negative is positive.-/
Statement ne_zero_dichotomy (a : Z) (ha : a ≠ 0) : (a ∈ Zplus ∨ -a ∈ Zplus) := by
  by_cases aplus : a ∈ Zplus
  left
  exact aplus
  Hint "Now we're in the second case. Note that now we have
  ```
  {aplus} : ¬{a} ∈ Z⁺
  ```
  "
  right
  simp[mem_Zplus] at aplus
  rcases aplus with F | T
  contradiction
  simpa[lt_def] using T

Conclusion "
🔧 This dichotomy theorem can often shorten trichotomy arguments by a significant margin.
"

NewTactic by_cases
