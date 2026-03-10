-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L07_test

World "RingWorld"
Level 8
Title "Negatives of sums"

Introduction "
# **Level 8**
Let's get more practice with the syntax from the previous level. Specifically, let's try to guide the contents of the `rw` tactic for the following theorem. We'll also have the opportunity to introduce a new tactic, `apply`, along the way.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
neg_add : ∀ a b : Z, -a + -b = -(a + b)
```
For all $a, b ∈ ℤ$, we have that $-(a + b) = -a + -b$.
-/
TheoremDoc neg_add as "Rng: neg_add"

/--
The `apply` tactic is for goal management. Usual usage might look like:
```
apply h
```
If it succeeds, then the tactic returns as many subgoals as the number of premises that have not been fixed by type inference or type class resolution.
For example, suppose we have a theorem of the form `thm: P → Q` and our goal is `⊢ Q`. Then
```
apply thm
```
will change the goal to `P`. This is logically valid since we know that `Q` follows from `P`.
-/
TacticDoc apply

/-- Negatives distribute over sums.-/
Statement neg_add : ∀ a b : Z, -a + -b = -(a + b) := by
  intro a b
  Hint "Our goal is
  ```
  ⊢ -{a} + -{b} = -({a} + {b})
  ```
  💡 **Does this look like the conclusion of a theorem that we've recently proven?** If so, the `apply` tactic might be good to use here.
  ### ❯ The `apply` tactic
  In general, if the goal is `⊢ Q` and we know that
  ```
  h : P → Q
  ```
  either as a hypothesis or known theorem, then `apply h` turns our new goal into `⊢ P`. In other words, `apply h` is the Lean way of saying *in order to prove `Q`, it suffices to prove `P` since we know `h : P → Q`*. 🔍 Check out the details in the **Tactics** tab."
  apply neg_unique (a + b) (-a + -b)
  Hint "### **💡 Pro-tip**
  You might have introduced a new hypothesis like
  ```
  obtain h := neg_unique ({a} + {b}) (-{a} + -{b})
  ```
  and then used `apply h` to get here. But you could have cut out the middle step with
  ```
  apply neg_unique
  ```
  Without explicit guidance, `apply` will try to unify with the goal like `rw[add_comm]`. ⏮ Go back and give this a shot. **We now just need to be purposeful about simplifying the goal...**"
  rw[add_assoc]
  rw[add_comm (-a)]
  rw[← add_assoc b]
  rw[add_neg_self]
  rw[zero_add]
  rw[add_neg_self]

Conclusion "
Our first mini-boss is next.
"

NewTactic apply
NewTheorem neg_add
