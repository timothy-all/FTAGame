-- import GameServer
import Game.Levels.PrimeWorld.L05_prime

World "PrimeWorld"
Level 6
Title "Primes are products of primes"

Introduction "
# **Level 6**
The statement of FTA requires us to codify long products of primes. In order to do so, we'll use Lean's ...
### 🕮 `List` type
🔍 Check out the entries for the following in the **Definitions** tab:
* `List`
* `List.prod`
* `List.Mem`
* `List.prime`
"

variable {Z : Type} [RRZ : RossRing Z]

/--
Assuming `h` is an inductive propostion, `cases h` splits the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor.
-/
TacticDoc cases

/--
If `L : List Z`, then `L` contains an ordered sequence of integers.
* The empty list is written `[]`
* `L.head` returns the first element of `L` (e.g `[x,y,z].head` returns `x`)
* `L.tail` returns the list created after dropping the `head` (e.g.`[x,y,z].tail` returns `[y,z]`)

Lists are constructed inductively from a given head and a tail.

### **Constructors**
* `List.nil` : the empty list, usually written `[]`
* `List.cons (head : Z) (tail : List Z) : List Z` :  the list whose first element is `head` and `tail` is the rest of the list, usually written `head :: tail`. For example, `x :: [y,z]` is the same as `[x,y,z]`.
-/
DefinitionDoc List as "List"

/--
List membership is constructed inductively. If `L : List Z`, then `L.Mem a` or `List.Mem a L` , usually just written `a ∈ L`, means that `a` is a member of the list `L`.
### **Constructors**
* `Mem.head` : the head of a list is a member.
* `Mem.tail` : a member of the tail of a list is a member of the list.
-/
DefinitionDoc List.Mem as "List.Mem"

/--
The product of a `List Z`. This is a custom definition for the FTA game. This definition is recursive. Here's what it looks like in Lean:
```
def List.prod : List Z → Z
| []             => (1:Z) --The product of the empty list is : 1.
| (head :: tail) => head * tail.prod
```
If `l : List Z`, then `l.prod` is equivalent to `List.prod l`.
-/
DefinitionDoc List.prod as "List.prod"

/--
If `L : List Z` then `List.prime L` is the proposition that every element of `L` is a `Prime`. Here's what it looks like in Lean
```
def List.prime (S : List Z) := ∀ s ∈ S, Prime s
```
If `l: List Z`, then `l.prime` is equivalent to `List.prime l`.
-/
DefinitionDoc List.prime as "List.prime"

/--
As stated:
```
prime_singleton :
  ∀ p : Z, Prime p →
  ∃ P : List Z, P.prime ∧ P.prod = p
```
If $p ∈ ℤ$ is prime, then there is a list of primes $P$ for which the product of all primes in $P$ is $p$.
-/
TheoremDoc prime_singleton as "Prm : prime_singleton"

/-- If $p ∈ ℤ$ is prime, then there is a list of primes $P$ for which the product of all primes in $P$ is $p$.-/
Statement prime_singleton : ∀ p : Z, Prime p → ∃ P : List Z, P.prime ∧ P.prod = p := by
  intro p hp
  Hint "We need a `List` to witness the existential goal."
  use [p]
  constructor
  Hint "It might be helpful to `unfold` the meaning of `⊢ [{p}].prime`. 👉 Try:
  ```
  unfold List.prime
  ```
  This step is **not** necessary; it merely makes the proposition `[{p}].prime` more visible.
  "
  unfold List.prime
  Hint "Let's make some introductions."
  intro s hs
  Hint "### ❯ The `cases` tactic
  🔍 Check out the entry for `List.Mem` in the **Definitions** tab. Note: the membership proposition `List.Mem` is inductively constructed. In our situation, we know `{hs}: {s} ∈ [{p}]` and we wish to show `⊢ Prime {s}`. This means there are two cases to consider: either `{s}` is the **head** of the list, or `{s}` belongs in the **tail** of the list. To break down into these inductive *cases*, try:
  ```
  cases {hs}
  ```
  More generally, if `h` is a inductive proposition, then `cases h` will split the main goal into subgoals according to the constructors of that inductive type. Each subgoal will be a general instance of that specific constructor. 🔍 Check out the entry for `cases` in the **Tactics** tab."
  cases hs
  Hint "We're now in the case where we want to show that the **head** of the list `[{p}]` is prime. This comes down to simply showing that `⊢ Prime {p}`."
  exact hp
  Hint "We're now in the case where we want to show that if `{s}` belongs to the **tail** of the list `[{p}]`, then `{s}` is prime. But the tail of this list is empty. One of our hypotheses is contradictory..."
  contradiction
  Hint "Our goal is now `⊢ [{p}].prod = {p}`. 🔍 Check out the entry for `List.prod` in the **Definitions** tab. The defintion of `List.prod` is recursive. This means we can use `rw` to successively apply the recursion rules. 👉 Try
  ```
  rw[List.prod]
  ```
  "
  rw[List.prod]
  Hint "Now our goal is `⊢ {p} * [].prod = {p}`. Applying `rw[List.prod]` again will produce the goal
  ```
  ⊢ p * 1 = p
  ```
  Alternatively, ⏮ we could go back to the first `rw[List.prod]` and simply use
  ```
  simp[List.prod]
  ```
  This will apply `List.prod` and statements tagged with `@[simp]` until either nothing happens or the goal is cleared (the latter of which happens in this case).
  "
  simp[List.prod]


Conclusion "
"

NewDefinition List List.prod List.prime List.Mem
NewTactic cases
