-- import GameServer
import Game.Metadata

World "RingWorld"
Level 1
Title "Addition on the right"

Introduction "
# **Level 1**
Welcome to Level 1! We'll start with a gentle introduction to Lean syntax and proofs by **tactics**. Our first goal is to prove the theorem `add_on_right` in the middle pane.
### **The UI**
The middle-pane will generally contain information about our current *proof state*. This includes current **Objects** and **Assumptions** (in the left column) as well as our current **Active Goal** (in the right column). The left-pane (this pane) contains general 💡tips💡,  👉hints👉 (things to explicitly try), and other info as we move through the levels.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
Introduces one or more hypotheses optionally naming them and or pattern-matching them. Usual usage might look like
```
intro ⟨patt⟩ ⟨patt⟩ ...
```
where `⟨patt⟩` is either an identifier or a pattern to destructure conjunctions (like in `rcases`). For example:
```
theorem silly : ∀ P Q : Prop, (P ∧ Q) → P :=  by
  intro P Q ⟨h1,h2⟩
```
The proof state contains the **Objects** `P Q : Prop` and the **Assumptions** `h1 : P` and `h2 : Q`. We'll learn more about patterns later.
### **Basic usage**
If we have a goal of the form `⊢ ∀ x, P x → Q x`, then
```
intro x h
```
will make `x` an **Object** and `h : P x` an active **Assumption** while the new goal will be `⊢ Q x`.
-/
TacticDoc intro

/--
Same as `rw`, but this version tries to immediately prove the goal by applying `rfl` automatically.
-/
TacticDoc rw

/--
This tactic applies to a goal whose target has the form x ~ x, where ~ is equality, heterogeneous equality or any relation that has a reflexivity lemma tagged with the attribute @[refl].
-/
TacticDoc rfl

/--
The tactic
```
rewrite[e]
```
applies identity `e` as a rewrite rule to the target of the main goal (and then attempts to clear the current goal with `rfl`). The identity `e` is often an equality, like `x = y`, but it can also be a logical equivalence, like `P ↔ Q`.

If `e` is preceded by left arrow (`←` or `<-`), like
```
rewrite[← e]
```
the rewrite is applied in the reverse direction. This perhaps explains why the tactic is logically allowed -- all identities `e` are symmetric (i.e. reversible).

You can apply a `rewrite` to a hypothesis with the syntax `rewrite[e] at h`.
-/
TacticDoc rewrite

/--
As stated:
```
add_on_right : ∀ a b c : Z, a = b → a + c = b + c
```
Addition on the right of an equality: $∀ a,b,c ∈ ℤ$, if a = b, then $a + c = b + c$.
-/
TheoremDoc add_on_right as "Rng : add_on_right"

/--We can add on the right across an equality of integers. More specifically, for all $a,b,c ∈ ℤ$ if $a = b$, then $a + c = b + c$. Here's how this statement looks in Lean:-/
Statement add_on_right : ∀ a b c : Z, a = b → a + c = b + c := by
  Hint "### ❯ The `intro` tactic
  We need to `intro` the variables `a b c` and the hypothesis `h : a = b`. 🔍 Check out the entry for `intro` in the **Tactics** tab. 👉 Specifically, try
  ```
  intro a
  ```
  "
  intro a
  Hint "This has introduced `{a}` as an arbitrary element in ℤ. 💡 Notice also how our goal has changed to
  ```
  ⊢ ∀ b c : Z, a = b → a + c = b + c
  ```
  We should introduce the variables `b c`. We can do both at the same time! 👉 Try
  ```
  intro b c
  ```
  "
  intro b c
  Hint "We now have `{a} {b} {c}` are generic elements of ℤ. Our goal is
  ```
  ⊢ {a} = {b} → {a} + {c} = {b} + {c}
  ```
  The typical strategy here is to assume that the *antecedent* or *hypothesis* of our if-then goal is true. In order to introduce the hypothesis `h : {a} = {b}` we also use `intro`. 👉 Try
  ```
  intro h
  ```
  "
  intro h
  Hint "Truth be told, we could have done this all in one line with
  ```
  intro {a} {b} {c} {h}
  ```
  ⏮ You can go back and try this out now! Just navigate to the **Retry** button on the first prompt. You'll return right back to this spot after trying out the more efficient use of `intro`.
  ### ❯ The `rewrite` tactic
  Now, we now want to subtitute `{a} = {b}` into the goal. We'll use the `rewrite` tactic to do so. 🔍 Check the documentation in the **Tactics** tab. 👉 Specifically, try
  ```
  rewrite[{h}]
  ```
  This will replace all instances of `{a}` with `{b}` in the goal."
  rewrite [h]
  Hint "### ❯ The `rfl` tactic
  Our goal is now `⊢ {b} + {c} = {b} + {c}`. This is true by **reflexitivity**! 👉 Try the tactic
  ```
  rfl
  ```
  This will check if our current goal is of this type and clear it!"
  rfl

Conclusion "
We've proven our first theorem! And we've learned about the tactics `intro`, `rewrite` and `rfl`.

### **💡 Pro-tip**
In practice, we **almost always** use the variant `rw` instead of `rewrite` since the former will automatically try to clear the goal with `rfl` and thereby save us a line. So instead of `rewrite[h]` we could have used `rw[h]` and cleared the goal. ⏮ Go back and give it a try!
"

NewTactic intro rewrite rw rfl
