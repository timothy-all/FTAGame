-- import GameServer
import Game.Levels.WOPWorld

World "PrimeWorld"
Level 1
Title "Primes are positive"

Introduction "
# **Level 1**
The fact that primes aren't zero isn't hard to prove and will be useful later on, so we start there. 🔍 Check out the entry for `Prime` in the **Definitions** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
Let $p ∈ ℤ$. We say that $p$ is **prime** to mean that the following hold:
* $1 < p$
* for all $a,b ∈ ℤ$, if $a$ and $b$ are positive such that $p = ab$, then $a = 1$ or $b =1$.

This is a **definition**. Here's what it look like in Lean:
```
def Prime (p : Z) : Prop :=
  1 < p ∧ (∀ a b : Z,
    0 < a → 0 < b → p = a * b → a = 1 ∨ b = 1
    )
```
-/
DefinitionDoc Prime as "Prime"

/--
As stated:
```
prime_ne_zero : ∀ p : Z, Prime p → p ≠ 0
```
Primes are nonzero.
-/
TheoremDoc prime_ne_zero as "Prm : prime_ne_zero"

/-- Primes are not zero.-/
Statement prime_ne_zero : ∀ p : Z, Prime p → p ≠ 0 := by
  intro p hp
  Hint "Notice that `{hp}` is somewhat *opaque*. If we wish to make the definition of `Prime` more apparent, we can use the `unfold` tactic. 🔍 Check out the new entry in the **Tactics** tab. 👉 Specifically, try
  ```
  unfold Prime at {hp}
  ```
  "
  unfold Prime at hp
  by_contra F
  obtain pos := hp.left
  rw[F] at pos
  exact lt_self 1 (lt_trans 1 0 1 pos one_pos)

Conclusion "
"

NewDefinition Prime
