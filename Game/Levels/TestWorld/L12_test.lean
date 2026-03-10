-- import GameServer
import Game.Levels.TestWorld.L11_test

World "RingWorld"
Level 12
Title "Divides is reflexive"

Introduction "
# **Level 12**
The **divides** relation is codified by `dvd_def`. 🔍 Check out this new unlocked definition in the **Definitions** tab.
### **⌨ Important typesetting tip**
The divides relation is written with `∣` typeset with `\\mid`. ***This is different than the vertical bar character found on your keyboard!*** You may not see a difference between the unicode characters `U+007C` (`|`) and `U+2223` (`\\mid`), but Lean does.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The **divides** relation is defined on $ℤ$ as follows: for $a, b ∈ ℤ$,  $a ∣ b$ means there exists $c ∈ ℤ$ such that $b = ac$.

This is a **definition**. Here's what it looks like in Lean:
```
dvd_def : ∀ a b : Z, a ∣ b ↔ ∃ c : Z, b = a * c
```
-/
DefinitionDoc dvd_def as "dvd_def"

/--
There exists a multiplicative identity in the integers. Specifically, there exists an element $1 ∈ ℤ$ such that for all $a ∈ ℤ$, we have $a · 1 = a$. This is an **axiom**. Here's what it looks like in Lean:
```
mul_one : ∀ a : Z, a * 1 = a
```
-/
DefinitionDoc mul_one as "mul_one"

/--
As stated:
```
dvd_refl : ∀ a : Z, a ∣ a
```
The divides relation is *reflexive*. In particular, for all $a ∈ ℤ$, $a ∣ a$.
-/
TheoremDoc dvd_refl as "Rng : dvd_refl"

/--
The `use` tactic use *use*ful (hehe) for existential goals. Specifically, if the goal is of the form `⊢ ∃ x, p x`, then assuming `y` is a known object in the tactic state we get that
```
use y
```
Will change the goal to `⊢ p y`.
-/
TacticDoc use

/-- The divides relation is reflexive.-/
Statement dvd_refl : ∀ a : Z, a ∣ a := by
  intro a
  Hint "Let's rewrite our goal using `dvd_def`."
  rw[dvd_def]
  Hint "### ❯ The `use` tactic
  Our goal is an **existential** statement. In order to reckon with the existential directly, we need to offer a *witness* to the predicate that follows. In our case, our goal is `⊢ ∃ c, a = a * c`. The element that witnesses this existential is `c = 1`. 🔍 Check out the `use` tactic in the **Tactics** tab. 👉 Specifically, try
  ```
  use 1
  ```
  "
  use 1
  Hint "**Note:** our goal is now `⊢ a = a * 1`. 🔍 Check out the newly unlocked `mul_one` axiom in the **Definitions** tab."
  rw[mul_one]

Conclusion "
Next up: we'll show that $1$ is a universal divisor.
"

NewDefinition dvd_def mul_one
NewTactic use
