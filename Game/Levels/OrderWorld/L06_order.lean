-- import GameServer
import Game.Levels.OrderWorld.L05_order

World "OrderWorld"
Level 6
Title "Positive iff greater than zero"

Introduction "
# **Level 6**
Another if-and-only-if to practice on. Also...
### **⟳ `simp` updated**
The `simp` tactic knows the following:
```
neg_zero : (-0 : Z) = 0
```
This can be helpful in this exercise.

### **🤔 But why?**
This level may seem a little silly, but it's surprisingly helpful. Reason being: we know that `a < b` is **definitionally equivalent** to `b + -a ∈ Zplus` via `lt_def`. It's good to have a theorem like `mem_Zplus` around in the event that we want to intentionally interpret `b + -a ∈ Zplus` as saying `0 < b + -a`. This is especially true for propositions like `a ∈ Zplus`. In order to use `lt_def` to interpret this as saying `0 < a` we'd have to wrangle it into the form `a + -0 ∈ Zplus`. The theorem `mem_Zplus` allows us to interpret `a ∈ Zplus` as `0 < a` more gracefully.
"

variable {Z : Type} [RRZ : RossRing Z]

@[simp] theorem not_lt_simp (a b : Z) : ¬(a < b) ↔ b ≤ a := by
  exact not_lt a b

@[simp] theorem not_le (a b : Z) :  ¬ (a ≤ b) ↔ (b < a) := by
  constructor
  intro h
  rw[le_def] at h
  simp at h
  obtain h' := h.right
  rw[le_def] at h'
  rcases h' with beqa | blta
  symm at beqa
  obtain h' := h.left
  contradiction
  exact blta
  intro h
  rw[le_def]
  simp
  constructor
  by_contra F
  rw[F] at h
  rw[lt_def,add_neg_self] at h
  exact non_trivial h
  rw[le_def]
  right
  exact h

/--
As stated:
```
mem_Zplus : ∀ a : Z, a ∈ Zplus ↔ 0 < a
```
For all $a ∈ ℤ$, $a ∈ ℤ⁺$ if and only if $0 < a$.
-/
TheoremDoc mem_Zplus as "Ord : mem_Zplus"

/-- An integer belongs to $ℤ⁺$ if and only if $0$ is less than that integer. -/
Statement mem_Zplus : ∀ a : Z, a ∈ Zplus ↔ 0 < a := by
  intro a
  constructor
  intro h
  rw[lt_def]
  simp
  exact h
  intro h
  rw[lt_def] at h
  simp at h
  exact h

Conclusion "
### **💡 Pro-tip**
You may have written
```
rw[lt_def]
simp
```
But this could have been dealt with in one fell swoop:
```
simp[lt_def]
```
In fact, this level can be beaten with one line! We'll get some more practice with `simp` in the next level.
"
