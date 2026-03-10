-- import GameServer
import Game.Levels.TestWorld
-- import Game.Notation.RossSet

World "OrderWorld"
Level 1
Title "Less-than is transitive"

Introduction "
# **Level 1**
Welcome to Level 1! First, we'll show that the *less than* relation is transitive.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The relation $a < b$ means that $b + -a ∈ ℤ⁺$. This is a **definition**. Here's how it looks in Lean:
```
instance : LT Z :=
  ⟨ fun a b => b + -a ∈ Zplus ⟩

lt_def : ∀ a b : Z, a < b ↔ (b + -a) ∈ Zplus
```
-/
DefinitionDoc lt_def as "lt_def"

/--
Positives are closed under addition. In particular,

$$ ∀ a, b ∈ ℤ^+ , a + b ∈ ℤ^+.$$

This is an **axiom**. Here's how it looks in Lean:
```
add_closure : ∀ a b : Z,
  a ∈ Z⁺ → b ∈ Z⁺ → (a + b) ∈ Z⁺
```
-/
DefinitionDoc add_closure as "add_closure"

/--
As stated:
```
lt_trans : ∀ a b c : Z, a < b → b < c → a < c
```
The relation *less than* is transitive. This means
$$ ∀ a,b,c ∈ ℤ, a < b → b < c → a < c.$$
-/
TheoremDoc lt_trans as "Ord : lt_trans"

/--
In Lean, we write `Zplus` for the set ℤ⁺. This is a non-empty subset of ℤ that satisfies some special properties, namely:
* **Non-triviality** : 0 is not an element of ℤ⁺
* **Additive closure** : if a,b ∈ ℤ⁺, then a + b ∈ ℤ⁺
* **Multiplicative closure** : if a,b ∈ ℤ⁺, then ab ∈ ℤ⁺.
* **Trichotomy** : for all a ∈ ℤ, precisely one of the following must hold:
  - a ∈ ℤ⁺ and a ≠ 0 and -a ∉ ℤ⁺
  - a ∉ ℤ⁺ and a = 0 and -a ∉ ℤ⁺
  - a ∉ ℤ⁺ and a ≠ 0 and -a ∈ ℤ⁺.

These are **axioms**.
-/
DefinitionDoc Zplus as "ℤ⁺"

/--
The `simp` tactic will try to simplify the target expression using statements tagged with the attribute `@[simp]`. This is **not** a full on auto-simplifier -- but it can simplify expressions like $a + 0$, $0 + a$, and so on. It can also be helpful in unfolding/applying definitions and basic logical structure. For example, we have
```
⊢ P ∧ True
```
Then `simp` will turn the goal into `⊢ P` (where `True` is any trivially true statement, like `a = a`). Similarly, if we have a hypothesis of the form
```
h : ¬ (P ∧ Q)
```
Then `simp at h` will turn the hypothesis into `P → ¬ Q`. More generally:
* `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `@[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.-
If an `hᵢ` is a definition, then it is unfolded.
* `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁ ... hₙ : Tₙ`.

## **Statements tagged with simp**
The following describes a complete list of statements from this game that up to now have been tagged with `@[simp]`.

### **Player proven**
* `zero_add : ∀ a : Z, 0 + a = a`
* `mul_zero : ∀ a : Z, a * 0 = 0`

### **Definitions**
* `add_zero : ∀ a : Z, a + 0 = a`
* `mul_one : ∀ a : Z, a * 1 = a`
* `add_neg_self : ∀ a : Z, a + -a = 0`

### **Other**
These theorems have been included behind the scenes for ease of use.
* `neg_self_add : ∀ a : Z, -a + a = 0`
* `one_mul : ∀ a : Z, 1 * a = a`
* `zero_mul : ∀ a : Z, 0 * a = 0`

-/
TacticDoc simp

/-- The *less-than* relation is transitive.-/
Statement lt_trans : ∀ a b c : Z, a < b → b < c → a < c := by
  intro a b c h1 h2
  Hint "👉 Now would be a good time to rewrite the hypotheses and goal using `lt_def`. **Remember:** we can apply a single rewrite to multiple sources with syntax like
  ```
  rw[lt_def] at {h1} {h2} ⊢
  ```
  The goal is `⊢` (typeset with `\\vdash` -- this is the so-called *turnstile* symbol)."
  rw[lt_def] at h1 h2 ⊢
  Hint "🔍 There's a new **Definition** that would be helpful here."
  Branch
    obtain h := add_closure (b + -a) (c + -b) h1 h2
    Hint "You could have made your life slightly easier by using `add_closure` in a different order. But it's OK! This is workable too. Try to get the hypothesis `{h}` in the following form:
    ```
    h : {b} + -{b} + -{a} + {c} ∈ Z⁺
    ```
    "
    rw[add_comm c] at h
    rw[← add_assoc] at h
    rw[add_assoc b] at h
    rw[add_comm (-a)] at h
    rw[← add_assoc b] at h
    Hint "### The tactic `simp`
  Let's try the new tactic `simp`. Certain simple theorems and axioms (like `{a} + 0 = {a}` and `{a} + -{a} = 0`) have been *tagged* with a special marker, namely `@[simp]`. This means that the `simp` tactic will try to repeatedly use those theorems to rewrite the target expression until it is unchanged. 👉 Try using
  ```
  simp at {h}
  ```
  The main idea here is to relieve us of a bit of tedium when possible."
    simp at h
    Hint "In this case `simp` rewrote `{b} + -{b}` as `0` to get `(0 + -{a}) + {c}`, then it rewrote `0 + -{a} = -{a}` (using the `@[simp]` tagged theorem `zero_add`) to get `{h}` it its current form. We're almost there..."
    rw[add_comm]
    exact h
  obtain h := add_closure (c + -b) (b + -a) h2 h1
  Hint "***Yes!*** We've used `add_closure` in a very efficient way. Try to get the assumption `{h}` into the following form:
  ```
  {h} : {c} + (-{b} + {b} + -{a}) ∈ Z⁺
  ```
  "
  rw[add_assoc] at h
  rw[← add_assoc (-b)] at h
  Hint "
  ### ❯ The tactic `simp`
  Let's try the new tactic `simp`. Certain simple theorems and axioms (like `{a} + 0 = {a}` and `{a} + -{a} = 0`) have been *tagged* with a special marker, namely `@[simp]`. This means that the `simp` tactic will try to repeatedly use those theorems to rewrite the target expression until it is unchanged along with some other basic facts. 🔍 Check out the entry for `simp` in the **Tactics** tab. 👉 Here, let's try using
  ```
  simp at {h}
  ```
  The main idea here is to relieve us of a bit of tedium when possible."
  simp at h
  Hint "In this case `simp` rewrote `-{b} + {b}` as `0` to get
  ```
  {c} + (0 + -{a})
  ```
  then it rewrote `0 + -{a} = -{a}` (using the `@[simp]` tagged theorem `zero_add`) to get `{h}` in its current form. We're almost there..."
  exact h


Conclusion "
### **⚠ A word of caution ⚠**
The tactic `simp` is **not** a full auto-simplifier. For example, if
```
h : (a + b) + (c + -a)
```
then `simp at h` does nothing. The tactic `simp` is *very* basic, and because of this only certain theorems and definitions have been tagged with `@[simp]`. In almost all cases, those theorems and definitions merely state basic equalities where the right-hand side is canonically simpler than the left.

It can be helpful to ask `simp` to use non-`@[simp]` tagged statements with syntax like  `simp[rules] ...`. We'll see this in the future.
"
NewTactic simp
NewDefinition Zplus lt_def add_closure
