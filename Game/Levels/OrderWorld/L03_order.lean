-- import GameServer
import Game.Levels.OrderWorld.L02_order


World "OrderWorld"
Level 3
Title "One is not equal to zero"

Introduction "
# **Level 3**
We'll need some more order axioms to complete this one. And we'll encounter our first proof-by-contradiction! Let's get started.

## Proof by contradiction
In order to prove a statement, say $P$, it can often be beneficial to assume $¬ P$ and try to prove a **contradiction**. A contradiction is a compound statement that is always False regardless of the True/False values of its component parts. A prototypical example would be a statement like $Q ∧ ¬ Q$:
* if $Q$ is True, then the conjunction is False;
* if $Q$ is False, then the conjunction is still False.

### ❯ The `by_contra` tactic
In Lean, contradictions are merely abbreviated with `False`. The tactic that allows us to attempt a proof-by-contradiction is `by_contra`. 🔍 See the new entry in the **Tactics** tab. 👉 Specifically, try
```
by_contra F
```
"

variable {Z : Type} [RRZ : RossRing Z]

/--
This the tactic used to attempt a *proof by contradiction*. Specifically, if the goal is `⊢ P`, then
```
by_contra h₁
```
will introduce a new hypothesis `h₁ : ¬ P` and change the goal to `False`. If you use
```
by_contra
```
then Lean will create an inaccessible hypothesis `F✝`. So it's best to provide a name for the introduced hypothesis.
-/
TacticDoc by_contra



/--
The set ℤ⁺ is a non-empty subset of ℤ. This is an **axiom**. Here's what it looks like in Lean:
```
∃ x : Z, x ∈ Zplus
```
-/
DefinitionDoc pos_nonempty as "pos_nonempty"

/--
The additive identity $0$ is not an element of $ℤ⁺$. This is an **axiom**. Here's what it looks like in Lean:
```
non_trivial : (0 : Z) ∉ Zplus
```
We needed to write `(0 : Z)` otherwise Lean defaults to thinking of numbers as belonging to the built-in type `Nat`.
-/
DefinitionDoc non_trivial as "non_trivial"


/--
As stated:
```
one_ne_zero : (1 : Z) ≠ 0
```
The multiplicative identity $1 ∈ ℤ$ is not equal to the additive identity $0 ∈ ℤ$.
-/
TheoremDoc one_ne_zero as "Ord : one_ne_zero"

/-- The multiplicative identity $1$ is not equal to the additive identity $0$.-/
Statement one_ne_zero : (1 : Z) ≠ 0 := by
  by_contra F
  Hint "See how the goal is now `⊢ False`? And we have a new hypothesis `{F} : 1 = 0`. Let's bring the axiom `pos_nonempty` into play. 🔍 Check out the entry in the **Definitions** tab. We'll need to be verbose this time and use:
  ```
  obtain h : ∃ x : Z, x ∈ Zplus := pos_nonempty
  ```
  otherwise Lean will lodge the complaint that *typeclass instance problem is stuck*.
  "
  obtain h : ∃ x : Z, x ∈ Zplus := pos_nonempty
  Hint "👉 Try to use `rcases` to destructure the assumption `{h}`."
  rcases h with ⟨ x, x_pos⟩
  Hint "### **💡 Pro-tip**
  We could have been more economical and used the pattern-matching capabilities of `obtain` to destructure the statement `∃ {x} : Z, {x} ∈ Zplus`. Indeed, `obtain` uses `rcases` as a last step. ⏮ **Go back and try**:
  ```
  obtain ⟨{x}, {x_pos}⟩ : ∃ x : Z, x ∈ Zplus := pos_nonempty
  ```
  This kills two birds with one stone."
  rw[← mul_one x] at x_pos
  rw[F] at x_pos
  rw[mul_zero] at x_pos
  Hint "Excellent! We're almost home. We need to use the `non_trivial` axiom. 👉 Try:
  ```
  exact non_trivial {x_pos}
  ```
  "
  exact non_trivial x_pos

Conclusion "
### **💡 Pro-tip**
In general, if `hnp : ¬ P` is a known theorem or hypothesis and `hp : P` is a known theorem or hypothesis, then `hnp hp` is a proof of `False`.

🔧 The `by_contra` tactic will be very handy going forward.
"

NewDefinition pos_nonempty non_trivial
NewTactic by_contra
