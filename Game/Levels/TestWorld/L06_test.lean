-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L05_test

World "RingWorld"
Level 6
Title "Uniqueness of Negatives"

Introduction "
# **Level 6**
Try to use the `obtain` and `exact` tactics to prove the following exercise. We've also unlocked the **axioms** `add_neg_self` and `add_assoc`. **These will be important in this level.** 🔍 Check these out in the **Definitions** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The existence of additive inverses. In particular, $∀ a ∈ ℤ$, there is an element $-a ∈ ℤ$ such that $a + -a = 0$. This is an **axiom**. Here's what it looks like in Lean:
```
add_neg_self : ∀ a : Z, a + -a = 0
```
-/
DefinitionDoc add_neg_self as "add_neg_self"

/--
Addition is associative. In particular,

$$∀ a, b, c ∈ ℤ, (a + b) + c = a + (b + c).$$

This is an **axiom**. Here's what it looks like in Lean:
```
add_assoc : ∀ a b c : Z, a + b + c = a + (b + c)
```
-/
DefinitionDoc add_assoc as "add_assoc"

/--
As stated:
```
neg_unique : ∀ a b : Z, a + b = 0 → b = -a
```
Negatives are unique. In particular, $∀ a ∈ Z$, if $a + b = 0$, then it must be that $b = -a$.
-/
TheoremDoc neg_unique as "Rng : neg_unique"

/-- Negatives that are codified in `add_neg_self` are also unique. -/
Statement neg_unique : ∀ a b : Z, a + b = 0 → b = -a := by
  intro a b h
  Hint "### **🕵 For secret reasons ...**
  ... it would be better if
  ```
  {h} : {b} + {a} = 0
  ```
  👉 Use `rw` to get `{h}` in this form. We'll explain later."
  rw[add_comm] at h
  Hint "Let's *obtain* the new hypothesis
  ```
  h' : {b} + {a} + -{a} = 0 + -{a}
  ```
  Naturally, we'll use the `obtain` tactic and the freshly minted `add_on_right` theorem. 🔍 Check the entry for `add_on_right` in the **Theorems** tab. Recall that:
  ```
  add_on_right : ∀ a b c : Z, a=b → a+c=b+c
  ```
  This means that, as a *function*, `add_on_right` takes *four* arguments in order:
  * The first is the **left-hand side** of the hypothesis;
  * The second is the **right-hand side** of the hypothesis;
  * The third is the integer to be added on the right;
  * and the fourth is the hypothesis itself.

  👉 Accordingly, try:
  ```
  obtain h' := add_on_right ({b} + {a}) 0 (-{a}) {h}
  ```
  "
  obtain h' := add_on_right (b + a) (0) (-a) h
  Hint "We now need to simplify the hypothesis `
  ```
  {h'} : {b} + {a} + -{a} = 0 + -{a}
  ```
  You might start with the now-proven theorem `zero_add`."
  rw[zero_add] at h'
  Hint (hidden := true) "We might have tried `add_neg_self` but it didn't work! Why? Structurally, Lean inteprets
  ```
  {b} + {a} + -{a}
  ```
  as
  ```
  ({b} + {a}) + -{a}
  ```
  So `add_neg_self` fails to find an expression like `a + -a` within `({b} + {a}) + -{a}`. How to fix this? 🔍 We might check the **Definitions** tab for something useful..."
  rw[add_assoc] at h'
  Hint "***Yes!*** This is exactly what we need. We've got the term `{a} + -{a}` scoped now. What's next?"
  rw[add_neg_self] at h'
  Hint "Right on target. And now...?"
  rw[add_zero] at h'
  Hint "Let's clear the goal with ... ?"
  exact h'


Conclusion "
### **No more secrets**
*Why did we apply `add_comm` in the beginning?* This moment of foresight allowed the definition `add_neg_self` to be eventually applied to `b + a + -a = 0`. If not for `add_comm` in the beginning, we would probably need to know a *theorem* like
```
neg_add_self : ∀ x : Z, -x + x = 0
```
This theorem is definitely true (in fact, it follows immediately from applying `add_comm` to `add_neg_self`), but we haven't proven it yet! Don't worry though, we shouldn't need to be so secretive going forward.
"

NewDefinition add_assoc add_neg_self
NewTheorem neg_unique
