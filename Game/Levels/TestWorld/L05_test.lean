-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L04_test

World "RingWorld"
Level 5
Title "Uniqueness of Zero"

Introduction "
# **Level 5**
In this level, we'll learn about two new tactics: `obtain` and `exact`. We'll see how these tactics can be used to prove the given statement about the uniqueness of the additive identity.
### **Navigating the theorems tab**
This will be the first level where we might want to use a theorem from a previous level, specifically `zero_add`. 🔍 Notice how the entry for `zero_add` in the **Theorems** tab is listed as `Rng : zero_add`? The three letter prefix `Rng` is there simply to help group together all theorems proven in **R**i**ng** World. When using this theorem (or any other theorem proven in this game), you should **not** include this three letter prefix.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
zero_unique: ∀ b : Z, (∀ a: Z, a + b = a) → b = 0
```
If $b ∈ ℤ$such that for every $a ∈ ℤ$ we have $a + b = a$, then $b = 0$. In other words, the additive identity is unique.
-/
TheoremDoc zero_unique as "Rng : zero_unique"

/--
This is a finishing move -- `exact h` will clear the goal if the goal is `⊢ h`.
-/
TacticDoc exact

/--
The `obtain` tactic allows you to introduce hypotheses as long as they are proven. The general usage is:
```
obtain ⟨patt⟩ : prop := proof
```
In the above `⟨patt⟩` is a pattern, and `proof` is the proof of that `prop`. We'll learn more about patterns later. If `:= proof` is omitted as in
```
obtain : prop
```
then goal is split in two. The **Active Goal** is to prove `prop`; the second goal is the original with the obtained `prop` added as an assumption.

## **Basic Usage**
For now, basic usage looks like the following:
```
obtain h : prop := proof
```
In the above `h` is the name we give to the new assumption; `prop` is the proposition we want `h` to bind to; and `proof` is the proof that `prop`. Oftentimes, `prop` can be omitted (being implied from `proof`). In that case, usage is even more basic and looks like the following:
```
obtain h := proof
```
### **💡 Pro-tip**
If Lean complains that

*typeclass instance problem is stuck*

when using `obtain h := proof`, try using the more verbose `obtain h : prop := proof` instead.

-/
TacticDoc obtain

/-- The additive identity codified in `add_zero` is unique. -/
Statement zero_unique: ∀ b : Z, (∀ a: Z, a + b = a) → b = 0 := by
  intro b h
  Hint "### ❯ The `obtain` tactic
  It would be good to *obtain* the hypothesis:
  ```
  h' : 0 + {b} = 0
  ```
  and insert it into the proof-state. In order to do so, we'll use the `obtain` tactic. 🔍 Check out `obtain` entry in the **Tactics** tab.

  But how do we supply the `proof` of our proposition? Our current hypothesis `{h}` says
  ```
  {h} : ∀ a : Z, a + {b} = a
  ```
  ### **💡 Propositions as functions**
  We can view `{h}` as a function where the input is say `x` and the output `{h} (x)` or more simply `{h} x` is (the proof of) the proposition `x + {b} = x`. 👉 Accordingly, try:
  ```
  obtain h' := {h} 0
  ```
  "
  obtain h' := h 0
  Hint "We now want to simplify our new hypothesis using a known theorem. 💡 **Remember:** we can apply rewrites to hypotheses with the syntax like
  ```
  rw[thm_name] at {h'}
  ```
  "
  rw[zero_add] at h'
  Hint "### ❯ The `exact` tactic
  We could use the `rw` tactic here. But let's try the `exact` tactic instead. 🔍 Check the the `exact` entry in the **Tactics** tab for guidance. 👉 Specifically, try
  ```
  exact {h'}
  ```
  "
  exact h'


Conclusion "
A similar proof can be written to show `one_unique`.
"

NewTactic exact obtain
