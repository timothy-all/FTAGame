-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L03_test

World "RingWorld"
Level 4
Title "The Left Additive Identity"

Introduction "
# **Level 4**
Here we'll prove `zero_add`. We'll need some freshly unlocked ...
### **Definitions**
🔍 Check out the **Definitions** tab in the right-pane. These are the axioms and definitions that *define* ℤ, the integers and other mathematical objects of relevance. They will unlock as we need them. New **Definitions** (or rather **axioms**) have 🔓unlocked to help out in this level, namely `add_comm` and `add_zero`.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
There exist an additive (right) identity in ℤ, namely 0. In particular, there is an element 0 ∈ ℤ with the following property:

$$∀ a ∈ ℤ, a + 0 = a.$$
This is an **axiom**. Here's what it looks like in Lean:
```
add_zero : ∀ a : Z, a + 0 = a
```
-/
DefinitionDoc add_zero as "add_zero"

/--
As stated:
```
zero_add : ∀ a : Z, 0 + a = a
```
The *right additive identity* guaranteed to exist by **add_zero** is also a *left additive identity*. In other words,

$$∀ a ∈ ℤ, 0 + a = 0.$$
-/
TheoremDoc zero_add as "Rng : zero_add"

/--
Commutativity of addition. In particular,

$$∀ a, b ∈ ℤ, a + b = b + a.$$

This is an **axiom**. Here's what it looks like in Lean
```
add_comm : ∀ a b : Z, a + b = b + a
```
-/
DefinitionDoc add_comm as "add_comm"

/-- The right additive identity codified by `add_zero` in **Definitions** is also a left additive identity. -/
@[simp] Statement zero_add : ∀ a : Z, 0 + a = a := by
  intro a
  Hint "🔍 Check the freshly unlocked **Definitions** in the right-pane. There are two highlighed axioms. 👉 Let's try
  ```
  rw[add_comm]
  ```
  💡 Although `add_comm` is a universally quantified statement, `rw[add_comm]` will attempt some **pattern-matching**. Explicitly, it will find the first expression in our goal of the form `x + y` and replace it with `y + x`."
  Branch
    rw[add_comm]
    Hint "Excellent! What can we try next?"
    rw[add_zero]
  rw[add_comm,add_zero]


Conclusion "
### **💡 Pro-tip**
Instead of using `rw[add_comm]` and `rw[add_zero]` separately, we could have done them (sequentially) in one line with
```
rw[add_comm,add_zero]
```
Sometimes it's hard to see ahead like that though; that being said, you can always ⏮ go back to a rewrite and add to it. This can shorten the number of prompts we need.
"

NewDefinition add_zero add_comm
