-- import GameServer
import Game.Levels.FTAWorld.L06_FTA

World "FTAWorld"
Level 7
Title "Rearranging a list"

Introduction "
# **Level 7**
This will be our first look at **permutations** of lists.
### 🕮 `Perm`
Typically, we think of one list as being a permutation of another using the language of *bijective functions*. Alternatively, we could take a more **inductive** approach. 🔍 Check out the entry for `Perm` in the **Definitions** tab for more details.
"

variable {Z : Type} [RRZ : RossRing Z]

open List

/--
Two lists `L₁` and `L₂` are permutations of each other, denoted `L₁ ~ L₂` (where `~` is the *tilde* symbol) if they contains the same elements, each occurring the same number of times but not necessarily in the same order. To make things more precise, we define permutations in an **inductive** way. Specifically, by definition we say:
* **nil** : the empty list is a permutation of the empty list: `[] ~ []`.
* **cons** : if `L₁ ~ L₂`, then for all `x` we have `(x :: L₁) ~ (x :: L₂)`
* **swap** : if `L` is a list, then for all `x y` we have `(y :: x :: L) ~ (x :: y :: L)`
* **trans** : if `L₁ L₂ L₃` are lists such that `L₁ ~ L₂` and `L₂ ~ L₃`, then `L₁ ~ L₃`.

These are the constructors for the inductive predicate `List.Perm`.
-/
DefinitionDoc List.Perm as "Perm"

/--
A constructor for `Perm` (where `α` is a generic Type):
```
cons (x : α) {l₁ l₂ : List α} :
  l₁ ~ l₂ → (x :: l₁) ~ (x :: l₂)
```
-/
DefinitionDoc List.Perm.cons as "Perm.cons"

/--
A constructor for `Perm` (where `α` is a generic Type):
```
swap (x y : α) (l : List α) :
  (y :: x :: l) ~ (x :: y :: l)
```
-/
DefinitionDoc List.Perm.swap as "Perm.swap"

/--
A constructor for `Perm` (where `α` is a generic Type):
```
trans :
  l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
```
-/
DefinitionDoc List.Perm.trans as "Perm.trans"

/--
As stated:
```
mem_perm_cons
  {u : Type}
  (l : u) :
  ∀ L : List u, l ∈ L → ∃ Lt : List u, L ~ (l :: Lt)
```
If $l$ is the member of a list $L$, then $L$ is a permutation of a list with $l$ as the head.
-/
TheoremDoc mem_perm_cons as "FTA : mem_perm_cons"

/-- If $l$ is the member of a list $L$, then $L$ is a permutation of a list with $l$ as the head.-/
Statement mem_perm_cons {u : Type} (l : u) : ∀ L : List u, l ∈ L → ∃ Lt : List u, L ~ (l :: Lt) := by
  intro L hl
  induction L
  simp at hl
  Hint "At this point we want to break down `{hl}` into cases. We can do this with either `cases` or `rcases`."
  cases hl
  use tail
  rfl
  obtain ⟨lt,hlt⟩ := tail_ih a
  use (head :: lt)
  Hint "We'll need to use the specific constructors of `Perm` to prove our goal. 🔍 Check out the entries for `Perm.cons`, `Perm.swap`, and `Perm.trans`. We might start by trying to obtain the hypothesis:
  ```
  h1 : head :: l :: {lt} ~ l :: head :: {lt}
  ```
  "
  obtain h1 : (head :: l :: lt) ~ (l ::head :: lt) := Perm.swap l head lt
  obtain h2 : (head :: tail) ~ (head :: l :: lt) := Perm.cons head hlt
  exact Perm.trans h2 h1

Conclusion "
"

NewDefinition List.Perm List.Perm.cons List.Perm.swap List.Perm.trans
