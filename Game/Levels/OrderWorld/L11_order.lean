-- import GameServer
import Game.Levels.OrderWorld.L10_order

World "OrderWorld"
Level 11
Title "A positive factor of a positive product"

Introduction "
# **Level 11**
Another relatively straightforward but useful theorem to have in the inventory.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The `by_contra!` tactic is the same as `by_contra` but it attempts to apply `simp` on the introduced hypothesis. So `by_contra! F` is the same as
```
by_contra F
simp at F
```
-/
TacticDoc by_contra!

/--
As stated:
```
pos_mul_pos_left : ∀ a b : Z,
  0 < a * b → 0 < a → 0 < b
```
For all $a,b ∈ ℤ$, if $0 < ab$ and $0 < a$, then $0 < b$.
-/
TheoremDoc pos_mul_pos_left as "Ord : pos_mul_pos_left"

/-- For all $a,b ∈ ℤ$, if $0 < ab$ and $0 < a$, then $0 < b$. -/
Statement pos_mul_pos_left : ∀ a b : Z, 0 < a * b → 0 < a → 0 < b := by
  intro a b h1 h2
  Hint "
  ### ❯ The `by_contra!` tactic
    This might be a good place to try a proof by contradiction. The newly unlocked `by_contra!` tactic can make your life slightly easier here. 🔍 Check out the entry in the **Tactics** tab. 👉 Try
    ```
    by_contra! F
    ```
  "
  by_contra! F
  rcases F with b_zero | b_neg
  rw[b_zero,mul_zero] at h1
  exact lt_self 0 h1
  Hint "💪**Challenge:** we can be done in no more than three tactic calls from here."
  obtain h3 := mul_on_left_lt a b 0 h2 b_neg
  rw[mul_zero] at h3
  exact lt_self (a * b) (lt_trans (a * b) 0 (a * b) h3 h1)

Conclusion "
"

NewTactic by_contra!
