-- import GameServer
import Game.Levels.GCDWorld.L01_GCD


World "GCDWorld"
Level 2
Title "Greatest common divisors exist"

Introduction "
# **Level 2**
Boss fight! In this level we prove that given two integers $a$ and $b$, as long as they are not both zero, the **g**reatest **c**ommon **d**ivisor exists. The greatest common divisor is exactly as it sounds -- it is the largest integer that simultaneously divides $a$ and $b$ (assuming $a$ and $b$ are not both zero).
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The tactic `refine e` behaves like `exact e`, except that named (?x) or unnamed (?_) holes in `e` that are not solved by unification with the main goal's target type are converted into new goals, using the hole's name, if any, as the goal case name.

For example, this can be helpful for goals like `⊢ P₁ ∧ P₂ ∧ P₃ ∧ P₄`. Instead of calling `constructor` multiple times we could simply use:
```
refine ⟨?_,?_,?_,?_⟩
```
This will generate four subgoals of the corresponding type. If we have an **Assumption** like `h : P₃`, then we could use:
```
refine ⟨?_,?_,h,?_⟩
```
This will generate three subgoals of the corresponding type (the would-be third goal has been cleared with `exact h`).
-/
TacticDoc refine

/--
As stated:
```
gcd_exists
  (a b : Z)
  (hab : ¬ (a = 0 ∧ b = 0) ) :
  ∃ g : Z, g ∣ a ∧ g ∣ b ∧
    (∀ d : Z, (d ∣ a → d ∣ b → d ≤ g))
```
For all $a,b ∈ ℤ$, if at least one of $a$ or $b$ is non-zero, then there exists $g ∈ ℤ$ such that $g ∣ a$, $g ∣ b$, and $∀ d ∈ ℤ$, if $d ∣ a$ and $d ∣ b$, then $d ≤ g$. We call $g$ a **greatest common divisor**.
-/
TheoremDoc gcd_exists as "GCD : gcd_exists"

/-- As long as one of $a$ or $b$ is non-zero, then a greatest common divisor of $a$ and $b$ exists.-/
Statement gcd_exists (a b : Z) ( hab : ¬ (a = 0 ∧ b = 0) ) : ∃ g : Z, g ∣ a ∧ g ∣ b ∧ (∀ d : Z, (d ∣ a → d ∣ b → d ≤ g)) := by
  define S := {d : Z | d ∣ a ∧ d ∣ b}
  Branch
    by_pow S with g hgS gmax
    use g
    Hint "Our goal is a three-part conjunction. So we could use the `constructor` tactic but we'd have to use it twice (eventually). Instead, we could use...
    ### ❯ The `refine` tactic
    The `refine` tactic behaves as a sort of mix between `exact` and `constructor` (at least, in this case). 🔍 Check out the entry for `refine` in the **Tactics** tab. 👉 In this specific situation, try:
    ```
    refine ⟨{hgS}.left,{hgS}.right,?_⟩
    ```
    This will focus our goal on the right-hand side of the conjunction in the goal (since we already know `{g} ∣ {a}` from `{hgS}.left` and `{g} ∣ {b}` from `{hgS}.right`).
    "
    refine ⟨hgS.left, hgS.right,?_⟩
    intro d hda hdb
    exact gmax d (And.intro hda hdb)
    exact bdd_divisors a b hab
    use 1
    exact And.intro (one_dvd a) (one_dvd b)
  by_pow S with g ⟨gda,gdb⟩ gmax
  use g
  Hint "Our goal is a three-part conjunction. So we could use the `constructor` tactic but we'd have to use it twice (eventually). Instead, we could use...
  ### ❯ The `refine` tactic
  The `refine` tactic behaves as a sort of mix between `exact` and `constructor` (at least, in this case). 🔍 Check out the entry for `refine` in the **Tactics** tab. 👉 In this specific situation, try:
  ```
  refine ⟨{gda},{gdb},?_⟩
  ```
  This will focus our goal on the right-hand side of the conjunction in the goal (since we already know `{g} ∣ {a}` from `{gda}` and `{g} ∣ {b}` from `{gdb}`).
  "
  refine ⟨gda,gdb,?_⟩
  intro d hda hdb
  exact gmax d (And.intro hda hdb)
  exact bdd_divisors a b hab
  use 1
  exact And.intro (one_dvd a) (one_dvd b)

Conclusion "
The next level shows how we will use greatest common divisors going forward.
"

NewTactic refine
