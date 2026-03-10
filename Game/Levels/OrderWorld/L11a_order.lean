-- import GameServer
import Game.Levels.OrderWorld.L10_order

World "OrderWorld"
Level 11
Title "Subtracting a negative"

Introduction "
# **Level 11**
Racking up another useful theorem.
### ⟳ `simp` updated
From this level going forward, `simp` knows that
```
neg_eq_zero : ∀ a : Z, -a = 0 ↔ a = 0
```
"

variable {Z : Type} [RRZ : RossRing Z]

@[simp] theorem neg_eq_zero : ∀ a : Z, -a = 0 ↔ a = 0 := by
  intro a
  constructor
  intro h
  obtain h' := add_on_right (-a) 0 a h
  simp at h'
  rw[h']
  intro h
  obtain h' := add_on_right a 0 (-a) h
  simp at h'
  rw[h']


/--
As stated:
```
le_sub_imp_nonpos : ∀ a b : Z, a ≤ a + -b → b ≤ 0
```
For all integers $a$ and $b$, if $a ≤ a - b$, then $b ≤ 0$.
-/
TheoremDoc tle_sub_imp_nonpos as "Ord : le_sub_imp_nonpos"

/-- For all integers $a$ and $b$, if $a ≤ a - b$, then $b ≤ 0$.-/
Statement tle_sub_imp_nonpos : ∀ a b : Z, a ≤ a + -b → b ≤ 0 := by
  intro a b h
  rcases h with eq | lt
  symm at eq
  obtain h := add_eq_self a (-b) eq
  simp at h
  left
  exact h
  rw[lt_def,add_assoc,add_comm (-b),← add_assoc] at lt
  simp at lt
  right
  simpa[lt_def] using lt

Conclusion "
"
