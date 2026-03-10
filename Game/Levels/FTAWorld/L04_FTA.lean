-- import GameServer
import Game.Levels.FTAWorld.L03_FTA

World "FTAWorld"
Level 4
Title "Prime lists have prime tails"

Introduction "
# **Level 4**
We'll need a new definition.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
A member of the tail of a list is a member of the list: `a ∈ l → a ∈ b :: l`. Here's what it looks like in Lean (where `α` is an arbitrary Type):
```
Mem.tail {α : Type u} {a : α} (b : α) {as : List α} :
  List.Mem a as → List.Mem a (b :: as)
```
The arguments in curly braces are **implicit**. This means those arguments will be inferred from context. Here's an example of how `Mem.tail` can be used:
```
example (α : Type) : ∀ x y z : α, y ∈ x :: [y,z] := by
  intro x y z
  obtain h : y ∈ [y,z] := Mem.head [z]
  exact Mem.tail x h
```
**Here's what's happening:**
* First, we obtain `h`, the proposition that `y ∈ [y,z] = [x,y,z].tail`.
* The `exact` tactic tells Lean to expect a proof of `y ∈ [x,y,z]`;
* At the same time, `Mem.tail x` has the  type `{_ : α} ∈ {_ : List α} → {_ : α} ∈ x :: {_ : List α}`
* The hypothesis `h : y ∈ [y,z]` helps to unify `Mem.tail x` with the goal;
* Finally, Lean fills the implicit arguments and clears the goal.
-/
DefinitionDoc List.Mem.tail as "Mem.tail"

/--
`List.tail` returns the list created after dropping the `head` (e.g.`[x,y,z].tail` returns `[y,z]`).
-/
DefinitionDoc List.tail as "tail"


/--
As stated:
```
prime_tail : ∀ l : List Z, List.prime l → List.prime l.tail
```
If $l$ is a list of primes, then the **tail** of $l$ is also a list of primes.
-/
TheoremDoc prime_tail as "FTA : prime_tail"

/-- If $l$ is a list of primes, then the **tail** of $l$ is also a list of primes. -/
Statement prime_tail : ∀ l : List Z, l.prime → l.tail.prime := by
  intro l hl
  intro s hs
  Hint "**Remember:** `List` is an inductive type. 👉 Try
  ```
  cases {l}
  ```
  "
  cases l
  Hint "**Note:** the hypothesis `{hs}` reports that `s` belongs to the tail of an empty list. This seems contradictory."
  contradiction
  Hint "Almost there. We'll need to show that if `s ∈ tail` then `s ∈ (head :: tail)`. This is part of the **Definition** of list membership. 🔍 Check out the entry for `Mem.tail`."
  exact hl s (Mem.tail head hs)

Conclusion "
"

NewDefinition List.Mem.tail List.tail
