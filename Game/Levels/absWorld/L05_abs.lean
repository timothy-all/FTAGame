-- import GameServer
import Game.Levels.absWorld.L04_abs

World "absWorld"
Level 5
Title "Absolute values of positives"

Introduction "
# **Level 5**
We'll use the `obtain` tactic to open subgoals in this exercise.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
abs_eq : ∀ a : Z, 0 < a → a = abs a
```
FFor every integer $a$, if $a$ is positive, then $a = |a|$.
-/
TheoremDoc abs_eq as "Abs : abs_eq"


/-- For every integer $a$, if $a$ is positive, then $a = |a|$. -/
Statement abs_eq : ∀ a : Z, 0 < a → a = abs a := by
  intro a ha
  Hint "### ❯ The `obtain` tactic
  We can use the `obtain` tactic to open a subgoal where the target `⊢` is what we are trying to obtain. 👉 Specifically, try:
  ```
  obtain h : ¬ a < 0
  ```
  This will make the **Active Goal** to prove `¬ a < 0`. This message will repeat after you clear that goal."
  obtain h : ¬ a < 0
  Hint "Now our **Active Goal** is `⊢ ¬ a < 0`."
  by_contra F
  exact lt_self a (lt_trans a 0 a F ha)
  Hint "Now we're back to the original goal `⊢ a = abs a`."
  simp[abs,h]

Conclusion "
🙌 ***Congrats!*** You've beaten Absolute Value World!
"
