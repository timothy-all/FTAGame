-- import GameServer
import Game.Levels.OrderWorld.L14_order

World "OrderWorld"
Level 15
Title "Simple left cancellation across an inequality"

Introduction "
# **Level 15**
Wait... another boss fight!? This one is more **Rick, the door techniciain** than **Malenia, Blade of Miquella** though.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
left_mul_cancel_lt : ∀ a b : Z,
  0 < a → a * b < a → b < 1
```
For all $a,b ∈ ℤ$, if $0 < a$ and $ab < a$, then $b < 1$.
-/
TheoremDoc left_mul_cancel_lt as "Ord : left_mul_cancel_lt"

/-- For all $a,b ∈ ℤ$, if $0 < a$ and $ab < a$, then $b < 1$.-/
Statement left_mul_cancel_lt : ∀ a b : Z, 0 < a → a * b < a → b < 1 := by
  intro a b ha hab
  by_contra! F
  rcases F with eq | lt
  rw[← eq,mul_one] at hab
  exact lt_self a hab
  obtain F := mul_on_left_lt a 1 b ha lt
  rw[mul_one] at F
  exact lt_self a (lt_trans a (a * b) a F hab)

Conclusion "
🙌 ***Congrats!*** You've beaten OrderWorld!
"
