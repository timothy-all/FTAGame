-- import GameServer
import Game.Levels.WOPWorld.L01_WOP

World "WOPWorld"
Level 2
Title "Subsets and nonempty"

Introduction "
# **Level 2**
In this level, we'll see how to show sets are subsets of others and how to show *non-emptiness*.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The `unfold id` tactic unfolds all occurrences of a definition `id` in the current goal. Unfolding can be directed at a hypothesis `h` with `unfold id at h`.
-/
TacticDoc unfold

/--
As stated:
```
flip_ne_pos
  (S : Set Z)
  (u : Z)
  (S_ne : S ≠∅)
  (umax : ∀ x ∈ S, x < u) :
      {y : Z | ∃ s ∈ S, y = u + -s} ≠∅
    ∧ {y : Z | ∃ s ∈ S, y = u + -s} ⊆ Zplus

```
Suppose $S ⊆ ℤ$ is nonempty and strictly bounded above by $u ∈ ℤ$. Then the flipped set

$$ \{ y ∈ ℤ ∣ ∃ s ∈ S, y = u + -s \}$$

is nonempty and contained in $ℤ⁺$
-/
TheoremDoc flip_ne_pos as "WOP : flip_ne_pos"

/--
Let `A : Set Z`. The definitional proposition `A.nonempty` or `Set.nonempty A`, denoted `A ≠∅`, means `∃ x : Z, x ∈ A`. Here's what it looks like in Lean:
```
def Set.nonempty {α : Type} (A : Set α) : Prop :=
  ∃ x, x ∈ A
```
-/
DefinitionDoc Set.nonempty as "Set.nonempty"

/--
Let `A B : Set Z`. The definitional proposition `A.subset B` or `Set.subset A B`, denoted `A ⊆ B`, means `∀ x : Z, x ∈ A → x ∈ B`. Here's what it looks like in Lean:
```
def Set.subset {α : Type} (A B : Set α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B
```
-/
DefinitionDoc Set.subset as "Set.subset"

/--
Let `A : Set Z`. The definitional proposition `A.empty` or `Set.empty A`, denoted `A =∅`, means `¬ (∃ x : Z, x ∈ A)`. Here's what it looks like in Lean:
```
def Set.empty {α : Type} (A : Set α) : Prop :=
  ¬ (∃ x, x ∈ A)
```
-/
DefinitionDoc Set.empty as "Set.empty"

/--
Let `A B : Set Z`. The definitional proposition `A.notsubset B` or `Set.notsubset A B`, denoted `A ⊈ B`, means `∃ x : Z, x ∈ A ∧ ¬ x ∉ B`. Here's what it looks like in Lean:
```
def Set.notsubset {α : Type} (A B : Set α) : Prop :=
  ∃ x : α, x ∈ A ∧ x ∉ B
```
-/
DefinitionDoc Set.notsubset as "Set.notsubset"

/-- Suppose $S ⊆ ℤ$ is nonempty and strictly bounded above by $u ∈ ℤ$. Then the flipped set $\{ y ∈ ℤ | ∃ s ∈ S, y = u + -s \}$ is nonempty and contained in $ℤ⁺$.-/
Statement flip_ne_pos (S : Set Z) (u : Z) (S_ne : S ≠∅) (umax : ∀ x ∈ S, x < u) : ( {y : Z | ∃ s ∈ S, y = u + -s} ≠∅ ∧ {y : Z | ∃ s ∈ S, y = u + -s} ⊆ Zplus) := by
  constructor
  Hint "### ❯ The `unfold` tactic
  It might be helpful to *see* the definition for `≠∅`. To *unfold* a definition, we use the `unfold` tactic. 🔍 Check out the entry for `unfold` in the **Tactics** tab and the entry for `Set.nonempty` in the **Definitions** tab. 👉 In our situation, try:
  ```
  unfold Set.nonempty at S_ne ⊢
  ```
  "
  unfold Set.nonempty at S_ne ⊢
  Hint "See the change in the hypothesis `S_ne`? 💡 We should emphasize that this *unfolding* step is **not** necessary -- it merely makes the definition of `S_ne` more visible. For example, we can (and should) destructure the hypothesis `S_ne` using `rcases`. We could do that **without** unfolding as well."
  rcases S_ne with ⟨s, hs⟩
  use (u + -s)
  use s
  constructor
  exact hs
  rfl
  Hint "It might similarly be helpful to see the precise definition for `⊆`. 🔍 Check out the entry for `Set.subset` in the **Definitions** tab. 👉 In our situation, try
  ```
  unfold Set.subset
  ```
  "
  unfold Set.subset
  Hint "### **💡 Pro-tip**
  We should now `intro` the appropriate contents. But again, we could do that **without unfolding** as well. To `unfold` a definition merely makes the definition more visible to the player. ⏮ In fact, we can go back to the `unfold Set.subset` line and simply use:
  ```
  intro x ⟨ s, ⟨hs,hx⟩ ⟩
  ```
  to completely destructure the hypothesis of the Active Goal.
  "
  intro x ⟨s, ⟨hs,hx⟩⟩
  rw[hx]
  exact umax s hs

Conclusion "
### **💡 Pro-tip**
If `A` and `B` are sets whose membership propositions are `p` and `q` (resp.), then
* `A ⊆ B` means `∀ x, x ∈ A → x ∈ B`
* `A ≠∅ ` means `∃ x, x ∈ A`
* `A =∅ ` means `¬ (∃ x, x ∈ A)`
"

NewTactic unfold
NewDefinition Set.nonempty Set.subset Set.empty Set.notsubset
