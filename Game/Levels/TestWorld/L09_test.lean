-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L08_test

World "RingWorld"
Level 9
Title "Multiplication by Zero"

Introduction "
# **Level 9**
Our first mini-boss!

This statement is one that most folks are familiar with, but perhaps have never formally proven. We might find the `symm` tactic helpful in this level. 🔍 Check out the entry for `symm` in the **Tactics** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
mul_zero : ∀ a : Z, a * 0 = 0
```
For all $a ∈ ℤ$, we have that $a * 0 = 0$.
-/
TheoremDoc mul_zero as "Rng : mul_zero"

/--
Multiplication *distributes* over addition. In particular,

$$∀ a,b,c ∈ ℤ, a(b + c) = ab + ac$$

This is an **axiom**. Here's what it looks like in Lean:
```
mul_add : ∀ a b c : Z, a * (b + c) = a * b + a * c
```
-/
DefinitionDoc mul_add as "mul_add"

/--
The tactic `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute `@[symm]` (like equality). It replaces the target with `u ~ t`.

To apply `symm` to a hypothesis `h`, write `symm at h`.
-/
TacticDoc symm

/-- The product of any integer and $0$ is $0$. -/
@[simp] Statement mul_zero : ∀ a : Z, a * 0 = 0 := by
  intro a
  Hint "👉 Given the mix of additive and multiplicative structures here, we're probably going to need to obtain a new hypothesis that uses the **distributivity** property. 🔍 Check out the entry for `mul_add` in the **Definitions** tab."
  obtain h := mul_add a 0 0
  rw[add_zero] at h
  Hint "***Lean can be picky!*** We might be tempted to use the `add_eq_self` theorem at this point. The form of this theorem is:
  ```
  add_eq_self : x + y = x → y = 0
  ```
  The hypothesis `{h}` seems to be backwards though:
  ```
  {a} * 0 = {a} * 0 + {a} * 0
  ```
  ### ❯ The `symm` tactic
  The `symm` tactic is helpful here. If `h : x = y` is a hypothesis, then `symm at h` will produce `h : y = x`. 🔍 Check out the entry to `symm` in the **Tactics** tab for more details. 👉 Try
  ```
  symm at {h}
  ```
  "
  symm at h
  exact add_eq_self (a * 0) (a * 0) h

Conclusion "
### **💡 Pro-tip**
Once you have
```
h : a * 0 + a * 0 = a * 0
```
you might have used the `obtain` tactic along with the theorem `add_eq_self` to get
```
h' : a * 0 = 0
```
At that point, `exact h'` clears the goal. But you could (or rather **should**) have cut out the middle step! ⏮ Go back and try:
```
exact add_eq_self (a * 0) (a * 0) h
```
"
NewTheorem add_eq_self
NewTactic symm
NewDefinition mul_add

@[simp] theorem zero_mul : ∀ a : Z, 0 * a = 0 := by
  intro a
  rw[mul_comm,mul_zero]
