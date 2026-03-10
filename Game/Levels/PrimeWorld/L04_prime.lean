-- import GameServer
import Game.Levels.PrimeWorld.L03_prime

World "PrimeWorld"
Level 4
Title "Composites"

Introduction "
# **Level 4**
If $m$ is greater than $1$ and not prime, then we say that $m$ is **composite**. This exercise provides a useful necessary (and sufficient) condition for compositeness.
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
composite (m : Z):
  1 < m → ¬ Prime m →
    ∃ n : Z, 1 < n ∧ n ∣ m ∧ n < m
```
If $m$ is greater than $1$ and not prime, then we say that $m$ is **composite**. If $m$ is composite, then $m$ has a proper non-trivial divisor.
-/
TheoremDoc composite as "Prm : composite"

/-- If $m$ is composite, then $m$ has a proper non-trivial divisor.-/
Statement composite (m : Z) : 1 < m → ¬ Prime m → ∃ n : Z, 1 < n ∧ n ∣ m ∧ n < m:= by
  intro hm mnp
  Hint "👉 Try
  ```
  simp[Prime] at {mnp}
  ```
  This will unfold the definition `Prime` and push the negation through the definition.
  "
  simp[Prime] at mnp
  Hint "Let's combine the hypotheses `{mnp}` and `{hm}` and destructure the result with the `obtain` tactic."
  obtain ⟨n,hn,ndm,hn1,hnm⟩ := mnp hm
  Hint "It seems we have our witness..."
  use n
  Hint "Our goal is a three-part conjunction. So we could use the `constructor` tactic but we'd have to use it twice (eventually). Instead, we could use...
  ### ❯ The `refine` tactic
  The `refine` tactic behaves as a sort of mix between `exact` and `constructor` (at least, in this case). 🔍 Check out the entry for `refine` in the **Tactics** tab. 👉 In this specific situation, try:
  ```
  refine ⟨?_,{ndm},?_⟩
  ```
  This will split our main goal into just two since we already know the middle part of the conjuntion is true (by the hypothesis `{ndm}`)."
  refine ⟨?nontrivial,ndm,?proper⟩
  Hint "Now our current **Active Goal** is the left-hand side of our original conjunction."
  by_contra! F
  rcases F with F1 | F2
  exact hn1 F1
  exact nibzo n hn F2
  Hint "Now our current **Active Goal** is the right-hand side of our original conjunction."
  obtain hn := dvd_le n m ndm (lt_trans 0 1 m one_pos hm)
  rcases hn with F | T
  contradiction
  exact T


Conclusion "
"

NewTactic refine
