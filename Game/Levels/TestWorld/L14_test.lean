-- import GameServer
import Game.Levels.TestWorld.L13_test

World "RingWorld"
Level 14
Title "Divides is transitive"

Introduction "
# **Level 14**
We'll need `mul_assoc` for this level. 🔍 Check out the entry for `mul_assoc` in the **Definitions** tab.
### **💻 A word on currying**
You also might have expected the theorem `dvd_trans` to be worded differently. For example, you might have expected:
```
dvd_trans: ∀ a b c:Z,(a ∣ b ∧ b ∣ c) → a ∣ c
```
The form given here, namely:
```
dvd_trans: ∀ a b c:Z, a ∣ b → b ∣ c → a ∣ c
```
is logically equivalent and friendlier for programmatic purposes -- this is called **currying**. To clarify the point, suppose `adb : a ∣ b` and `bdc : b ∣ c`. To use `dvd_trans` in the **first** form, typical usage might look like:
```
obtain adc := dvd_trans a b c (And.intro adb bdc)
```
To use `dvd_trans` in the **second** form, typical usage might look like:
```
obtain adc := dvd_trans a b c adb bdc
```
The **second** form is easier to apply. This phenomenon becomes even more pronounced if the hypothesis is a longer conjunction.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
Multiplication is associative. In particular, for all $a,b,c ∈ ℤ$, we have

$$ (ab)c = a(bc) $$

This is an **axiom**. Here's what it looks like in Lean:
```
mul_assoc : ∀ a b c : Z, a * b * c = a * (b * c)
```
-/
DefinitionDoc mul_assoc as "mul_assoc"

/--
As stated:
```
dvd_trans : ∀ a b c : Z, a ∣ b → b ∣ c → a ∣ c
```
The divides relation is transitive. In particular, for all $a,b,c ∈ ℤ$, if $a ∣ b$ and $b ∣ a$, then $a ∣ c$.
-/
TheoremDoc dvd_trans as "Rng : dvd_trans"

/--
The tactic `rcases` is used to destructure hypotheses or expressions. General usage looks like `rcases h with patt` where `patt` is a pattern matched against `h`. For example, suppose `h : (a ∧ b ∧ c) ∨ (d ∧ e)`. Usual usage might be
```
rcases h with ⟨ha, hb, hc⟩ | ⟨ hd, he⟩
```
In this case, our goal would be split in two. The first goal would contain the hypotheses `ha : a`, `hb : b`, and `hc : c`. The second goal would contain the hypotheses `hd : d` and `he : e`. If a hypothesis will be irrelevant, we might choose to not explicitly name it by using `_`.
### **💡 Pro-tip**
There are scenarios where we may wish to **keep** the original hypothesis `h` in addition to any destructuring done by `rcases`. Usual usage might be
```
rcases hpf : h with ⟨ ha, hb, hc ⟩
```
What does `hpf` contain? The formal proof that `h` can be destructured into `⟨ ha, hb, hc⟩`. Typically, we won't need `hpf`.
### **⌨ Typesetting-tip**
There's a difference between the angled brackets `⟨ ⟩` and the relations `< >`. In order to produce the *angled brackets* use `\\langle` and `\\rangle`.
-/
TacticDoc rcases

/-- The divides relation is transitive.-/
Statement dvd_trans : ∀ a b c : Z, a ∣ b → b ∣ c → a ∣ c := by
  intro a b c hab hbc
  Hint "👉 For the sake of visibility, let's rewrite the hypotheses and goal using `dvd_def`. We can apply a single rewrite to multiple sources with syntax like
  ```
  rw[dvd_def] at {hab} {hbc} ⊢
  ```
  ### **⌨ Typesetting-tip**
  The goal is `⊢` is typeset with `\\vdash` -- this is the so-called *turnstile* symbol."
  rw[dvd_def] at hab hbc ⊢
  Hint "### ❯ `rcases` : Conjunctions as hypotheses
  Notice the form of our hypothesis `{hab}`. This can be thought of as a sort-of conjunction, specifically:
  ```
  {hab} : x : Z ∧ {b} = {a} * x
  ```
  It would be good to **destructure** this conjunction into its component parts. The tactic `rcases` is useful in this regard. The *r* stands for *recursive* meaning that we can destructure current hypotheses with some pattern matching. 🔍 Check out the `rcases` entry in the **Tactics**. 👉 Let's try
  ```
  rcases {hab} with ⟨ x, hx ⟩
  ```
  ### **⌨ Typesetting-tip**
  💡 In order to get the *angled brackets*, use `\\langle` and `\\rangle`.
  "
  rcases hab with ⟨x, hx⟩
  Hint "**Note:** we now have that `{x} : Z` in **Objects** and `{hx} : {b} = {a} * {x}` in **Assumptions**. 👉 Now try to desctructure the hypothesis `{hbc}`."
  rcases hbc with ⟨y, hy⟩
  Hint "### **💡 Pro-tip**
  We did **not** have to use the line `rw[dvd_def]...`. Everything works just as well if that line is removed, in other words we could have immediately started destructuring `a ∣ b` with `rcases`. ⏮ Go back and give it a try.

  At any rate, we wish to prove an existential now. Do we have a potential *witness*?"
  use (x * y)
  rw[hx,mul_assoc] at hy
  exact hy


Conclusion "
🔧 The tactic `rcases` will be *very* handy going forward.
"

NewDefinition mul_assoc
NewTactic rcases
