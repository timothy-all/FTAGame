-- import GameServer
import Game.Levels.PrimeWorld.L06_prime

World "PrimeWorld"
Level 7
Title "The empty list is a prime list"

Introduction "
# **Level 7**
🔍 Check out the entry for `List` in the **Definitions** tab. `List`s are inductive types as well. The constructors are `nil` and `cons`; the former assumes the list is empty while the latter assumes the list is constructed from a head and a tail. 👉 Let's try
```
cases l
```
to break down into these cases.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
The head of a list is a member: `a ∈ a :: as`. Here's what it looks like in Lean:
```
Mem.head {α : Type u} {a : α} (as : List α) :
  List.Mem a (a :: as)
```
The arguments in curly braces are **implicit**. This means those arguments will be inferred from context. Here's an example of how `Mem.head` can be used:
```
theorem silly (α : Type) : ∀ x y z : α, x ∈ [x,y,z] := by
  intro x y z
  exact Mem.head [y,z]
```
**Here's what's happening:**
* The `exact` tactic tells Lean to expect a proof of `x ∈ [x,y,z]`;
* At the same time `Mem.head [y,z]` has the type `_ ∈ _ :: [y,z]` where the underscores correspond to the implicit argument `{a : α}`.
* Lean unifies this type with the goal `x ∈ x :: [x,y]` inferring that `a = x`.
* Finally, Lean fills the implicit argument and clears the goal.
-/
DefinitionDoc List.Mem.head as "Mem.head"

/--
`List.head` returns the first element of a non-empty list (e.g `[x,y,z].head` returns `x`)
-/
DefinitionDoc List.head as "List.head"

/--
`List.tail` returns the list formed by dropping the `head` of `List` (e.g. `[x,y,z].tail` returns `[y,z]`).
-/
DefinitionDoc List.tail as "List.tail"

/--
As stated:
```
prime_prod_one_imp_empty :
  ∀ l : List Z, l.prime → l.prod = 1 → l = []
```
If the product of a list of primes is $1$, then the list is empty.
-/
TheoremDoc prime_prod_empty as "Prm : prime_prod_empty"

/-- If the product of a list of primes is $1$, then the list is empty.-/
Statement prime_prod_empty (l : List Z) (hp : l.prime) (hl : l.prod = 1) : l = [] := by
  cases l
  Hint "We're in the case where we are assuming `l = []`. So the goal is `⊢ [] = []` ... that one is pretty easy to clear."
  rfl
  Hint "Now we're in the case where we are assuming `l` has a `head` and a `tail`, specifically `l = (head :: tail)`. 👉 Our goal seems contradictory ... in fact, try
  ```
  simp
  ```
  "
  simp
  Hint "Lo and behold, our goal is `⊢ False`. So we should try to find a contradiction amongst ඞ our hypotheses. Try to obtain the hypothesis `head ∣ 1`. 👉 **Remember:** you can use `obtain` to open a subgoal like:
  ```
  obtain F : head ∣ 1
  ```
  "
  obtain F : head ∣ 1
  rw[List.prod] at hl
  use tail.prod
  rw[hl]
  Hint "We're getting there, but now we need to know that `head` is, in fact, prime. You'll need to use the hypothesis `hp` as well as the definition for `Mem.head`. 🔍 Check out the entry for `Mem.head` in **Definitions** tab."
  exact prime_dvd_one head (hp head (Mem.head tail)) F


Conclusion "
"

NewDefinition List.Mem.head List.tail List.head


theorem silly (α : Type) : ∀ x y z : α, x ∈ [x,y,z] := by
  intro x y z
  exact Mem.head [y,z]
