-- import GameServer
import Game.Levels.WOPWorld.L03_WOP

World "WOPWorld"
Level 4
Title "POW"

Introduction "
# **Level 4**
This level will feature the **W**ell **O**rdering **P**rinciple, abbreviated `WOP`. This is an **axiom** of ℤ; 🔍 check out the entry in the **Definitions** tab. The mathematical goal of this level is to prove a sort-of *flipped* version of `WOP` (whence the previous exercises!).
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
POW_strict
  (S : Set Z)
  (S_ne : S ≠∅)
  (u : Z)
  (umax : ∀ x ∈ S, x < u) :
    (∃ M ∈ S, ∀ x ∈ S, x ≤ M)
```
If $S$ is a non-empty subset of positive integers that is **strictly** bounded above, then $S$ contains a largest element. More precisely, for every $S ⊆ ℤ$, if $S ≠ ∅$ and there exists $u ∈ ℤ$ such that for all $x ∈ S$, $x < u$, then there exists $M ∈ S$, such that for all $x ∈ S$, $x ≤ M$.
-/
TheoremDoc POW_strict as "WOP : POW_strict"

/--
This is the **W**ell **O**rdering **P**rinciple. It says: for every $S ⊆ ℤ$, if $S ⊆ ℤ⁺$ and $S ≠ ∅$, then there exists $m ∈ S$ such that $∀ x ∈ S, m ≤ x$. In other words, every non-empty subset of positive integers contains a smallest element.

This is an **axiom**. Here's what it looks like in Lean:
```
∀ S : Set Z,
  (S ≠∅ ) → (S ⊆ Zplus) →
    ∃ m, m ∈ S ∧ ∀ x, x ∈ S → m ≤ x
```
-/
DefinitionDoc WOP as "WOP"

/--
The `define` tactic is for adding definitions to the local context of the main goal. General usage (in this game) is often for sets. That usage might look like:
```
define S := { x : Z | 0 ≤ x }
```
This is an alias for `let`.
-/
TacticDoc define

/--
The tactic `by_wop` splits the main goal into three subgoals. General usage looks like
```
by_wop S with m ⟨patt⟩ hmin
```
where
* `S` is a non-empty subset of ℤ⁺ (**the tactic will force you to prove this at the end**)
* `m` is the smallest element of `S`
* `⟨patt⟩` is either an identifier, like `hmS`, which identifies the hypothesis that `m ∈ S`, or a *pattern* (like in `rcases`) that can destructure the proposition `m ∈ S`
* `hmin` is the identifier for the hypothesis `hmin : ∀ (x : Z), x ∈ S → m ≤ x`.

### Goal 1
Keeps the original goal and hypotheses but adds the following hypotheses:
```
hne : S ≠∅
hpo : S ⊆ Z⁺
m : Z
hms : m ∈ S -- or destructured according to patt
hmin : ∀ (x : Z), x ∈ S → m ≤ x
```

### Goal 2
The new goal is `⊢ S ⊆ Z⁺` under the original hypotheses and the additional hypothesis `hne : S ≠∅`.

### Goal 3
The new goal is `⊢ S ≠∅` under the original hypotheses.


-/
TacticDoc by_wop

/-- If $S$ is a non-empty subset of positive integers that is **strictly** bounded above, then $S$ contains a largest element.-/
Statement POW_strict (S : Set Z) (S_ne : S ≠∅) (u : Z) (umax : ∀ x ∈ S, x < u) : (∃ M ∈ S, ∀ x ∈ S, x ≤ M) := by
  Hint "### ❯ The `define` tactic
  In order to apply the well ordering principle, we'll need a relevant set of positive integers to call it upon. In order to introduce such a set, we'll use the `define` tactic. 🔍 Check out the entry in the **Tactics** tab. 👉 In our case, try:
  ```
  define T := \{y : Z | ∃ s ∈ S, y = u + -s }
  ```
  ### **⌨ Typesetting-tip**
  The vertical bar `shift + \\` in *set-builder* notation ***is different*** than `\\mid` in *divides* notation.
  "
  define T := {y : Z | ∃ s ∈ S, y = u + -s}
  Hint "**Why define this set to begin with?** The set `{T}` is guaranteed to have a smallest element by the well-ordering principle. From this smallest element, we hope to construct a largest element of `S`. But how do we use `WOP`?
  ### ❯ The `by_wop` tactic
  Although you can use the **axiom** `WOP` directly, it's a little easier to us the custom tactic `by_wop`. 🔍 Check out the entry for `by_wop` in the **Tactics** tab. 👉 Our usage should look like
  ```
  by_wop {T} with m ⟨ patt ⟩ hmin
  ```
  where `⟨ patt ⟩` destructures as in `rcases` the proposition `m ∈ {T}`."
  by_wop T with m ⟨ w, ⟨ hwS, hw⟩⟩ hmin
  Hint "Notice our **Active Goal** is existential. We need a witness..."
  use (u + -m)
  constructor
  rw[hw,← neg_add,← add_assoc]
  simp
  exact hwS
  Hint "👉 The theorem `min_flip_max` should be helpful here."
  exact min_flip_max S u m hmin
  Hint "The theorem `flip_pos_nonempty` should be handy from here on out. The consequent of this theorem is a **conjunction**. 💡 The right-hand side of that conjunction is the current goal. 👉 Accordingly, we can clear the goal `⊢ T ⊆ Z⁺` with:
  ```
  exact (flip_ne_pos S u S_ne umax).right
  ```
   "
  exact (flip_ne_pos S u S_ne umax).right
  Hint "We can clear this goal similarly with one line."
  exact (flip_ne_pos S u S_ne umax).left


Conclusion "
Let's work on strengthening this result.
### **💡 Pro-tip**
The `by_wop` tactic is quite handy especially given the pattern-matching capabilities to destructure the statement `m ∈ S`. On the other hand, we don't **need** to do this. In other words, the usage:
```
by_wop S with m hmS hmin
```
is perfectly valid -- to be precise, we'll end up with `hmS : m ∈ S`.
"

NewDefinition WOP
NewTactic define by_wop
