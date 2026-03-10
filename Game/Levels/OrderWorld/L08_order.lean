-- import GameServer
import Game.Levels.OrderWorld.L07_order

World "OrderWorld"
Level 8
Title "One is positive"

Introduction "
# **Level 8**
### **🤔 What's the deal with `(0 : Z)`?**
We might wonder why the statement of this level isn't merely:
```
theorem one_pos : 0 < 1 := by
```
Here's what's going on
  - Unless there's enough context to tell it otherwise, Lean will cast digits like `0` to be of the type `Nat`, Lean's built-in ℕatural number type. So when we write `(0 :Z)` we are telling Lean that we are explicitly talking about the *additive identity* of the Ring `Z` which we've constructred from scratch.
  - But then why not write `(1 : Z)` as well? Once Lean sees `(0 : Z)`, it knows to implicitly cast other numbers in the statement to `Z` as well.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The negation of $a ≤ b$ is $b < a$.
-/
TacticDoc not_le --not a tactic

/--
Positives are closed under multiplication. In particular,

$$∀ a,b ∈ ℤ⁺, ab ∈ ℤ⁺ $$

This is an **axiom**. Here's what it looks like in Lean:
```
mul_closure ∀ a b : Z,
  a ∈ Zplus →  b ∈ Zplus
    → (a * b) ∈ Zplus
```
-/
DefinitionDoc mul_closure as "mul_closure"

/--
As stated:
```
one_pos : (0:Z) < 1
```
The multiplicative identity is positive: $0 < 1$.
-/
TheoremDoc one_pos as "Ord : one_pos"

/-- The the additive identity of $ℤ$ is less than multiplicative identity of $ℤ$. -/
Statement one_pos : (0 : Z) < 1 := by
  Branch
    rw[lt_def]
    Hint "👉 The `simp` tactic ought to simplify things a bit here."
    simp
    Hint "There are three cases to consider..."
    obtain ⟨ t1,_,_⟩ | ⟨ _,t2,_ ⟩ | ⟨ _,_,t3 ⟩ := trichotomy (1 : Z)
    exact t1
    Hint "This case seems contradictory..."
    obtain t2' : (1 : Z) ≠ 0 := one_ne_zero
    contradiction
    Hint "💡 We might be thinking to try to show a contradiction here. But don't work too hard -- we need only show that `⊢ 1 ∈ Z⁺` given that `{t3} : -1 ∈ Z⁺`. 🔍 Check newly unlocked items in the **Definitions** tab for a hint."
    obtain t3' := mul_closure (-1) (-1) t3 t3
    rw[← neg_mul_left,← neg_mul_right] at t3'
    simp at t3'
    exact t3'
  Branch
    obtain ⟨ t1,_,_⟩ | ⟨ _,t2,_ ⟩ | ⟨ _,_,t3 ⟩ := trichotomy (1 : Z)
    simp[lt_def,t1]
    Hint "This case seems contradictory..."
    obtain t2' : (1 : Z) ≠ 0 := one_ne_zero
    contradiction
    Hint "💡 We might be thinking to try to show a contradiction here. But don't work too hard -- we need only show that `⊢ 1 ∈ Z⁺` given that `{t3} : -1 ∈ Z⁺`. 🔍 Check newly unlocked items in the **Definitions** tab for a hint."
    obtain t3' := mul_closure (-1) (-1) t3 t3
    rw[← neg_mul_left,← neg_mul_right] at t3'
    simp at t3'
    simp[lt_def,t3']
  by_contra F
  simp at F
  rcases F with F1 | F2
  exact one_ne_zero F1
  rw[lt_def,zero_add] at F2
  obtain F3 := mul_closure (-1) (-1) F2 F2
  rw[← neg_mul_left,← neg_mul_right] at F3
  simp at F3
  obtain F4 := add_closure (1) (-1) F3 F2
  rw[add_neg_self] at F4
  exact non_trivial F4

Conclusion "
### **💡 Pro-tip**
If your first line was `by_contra F`, you might ⏮ go back and try again using the `trichotomy` axiom early on. That turns out to be a little faster.
"

NewDefinition mul_closure
NewHiddenTactic not_le --hack to keep these out of the way
