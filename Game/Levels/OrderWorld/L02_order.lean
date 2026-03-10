-- import GameServer
import Game.Levels.OrderWorld.L01_order


World "OrderWorld"
Level 2
Title "Less-than-or-equal-to is transitive"

Introduction "
# **Level 2**
Welcome to Level 2! Now we'll show that the *less than or equal to* relation is transitive when coupled with the *less than* relation. 🔍 Check out the definition `le_def` before getting started.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The relation $a ≤ b$ means that $a < b$ or $a = b$. Here's how it looks in Lean:
```
instance : LE Z :=
  ⟨fun a b => a = b ∨ a < b⟩

theorem le_def (a b : Z) : a ≤ b ↔ (a = b ∨ a < b)
```
-/
DefinitionDoc le_def as "le_def"

/--
As stated:
```
le_lt_trans : ∀ a b c : Z,
  a ≤ b → b < c → a < c
```
For all $a,b,c ∈ Z$, if $a ≤ b$ and $b < c$, then $a < c$.
-/
TheoremDoc le_lt_trans as "Ord : le_lt_trans"

/-- For all $a,b,c ∈ ℤ$, if $a ≤ b$ and $b < c$, then $a < c$.-/
Statement le_lt_trans : ∀ a b c : Z, a ≤ b → b < c → a < c := by
  intro a b c a_le_b b_lt_c
  Hint "🔍 Check out the definition for `le_def` in the **Definitions** tab. 👉 Try `rw[le_def] at {a_le_b}` to make the underlying disjunction more visible."
  rw[le_def] at a_le_b
  Hint "### ❯ `rcases` : Disjunctions as hypotheses
  Notice the form of our hypothesis
  ```
  {a_le_b} : {a} = {b} ∨ {a} < {b}
  ```
  At this point, we would break down into *cases*. The tactic `rcases` is also useful in this regard. The *r* stands for *recursive* meaning that we can destructure current hypotheses with some pattern matching. 🔍 Check out the `rcases` entry in the **Tactics**. 👉 Let's try
  ```
  rcases {a_le_b} with aeqb | altb
  ```
  "
  rcases a_le_b with aeqb | altb
  Hint "### **💡 Pro-tip**
  Like with `dvd_def`, we do **not** need `rw[le_def]`. Lean knows that `a ≤ b` is a disjunction. In the future, we can immediately destructure that disjunction with `rcases` and skip the `rw` step.

  At any rate, notice how we now have an **Active Goal** *and* a **Goal 2**?"
  rw[aeqb]
  exact b_lt_c
  Hint "We've cleared the case when `{a} = {b}`. We're now in the case when `{a} < {b}`. 💪 **Challenge:** try to clear this in one line."
  exact lt_trans a b c altb b_lt_c
Conclusion "
In case you didn't figure it out, here's the line that clears the goal in one line:
```
exact lt_trans a b c altb bltc
```
where `bltc : b < c`.

🔧 This theorem will be *very* handy going forward. It is often used to obtain contradictions like `a < a` from hypotheses `a ≤ b` and `b < a`.
"

NewDefinition le_def
