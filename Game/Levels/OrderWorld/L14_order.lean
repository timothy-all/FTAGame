-- import GameServer
import Game.Levels.OrderWorld.L13_order

World "OrderWorld"
Level 14
Title "Left Cancellation"

Introduction "
# **Level 14**
This is an important consequence of the previous theorem.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
left_mul_cancel : ∀ a b c : Z,
  a ≠ 0 → a * b = a * c → b = c
```
For all $a,b,c ∈ ℤ$, if $a ≠ 0$ and $ab = ac$, then $b = c$.
-/
TheoremDoc left_mul_cancel as "Ord : left_mul_cancel"

/-- For integers $a,b,c$, if $a ≠ 0$ and $ab = ac$, then it must be that $b =c$.-/
Statement left_mul_cancel : ∀ a b c : Z, a ≠ 0 → a * b = a * c → b = c := by
  intro a b c h1 h2
  obtain h := add_on_left (a * b) (a * c) (a * -c) h2
  rw[← mul_add,← mul_add] at h
  simp at h
  obtain h' := mul_eq_zero a (-c + b) h
  simp[h1] at h'
  obtain T := neg_unique (-c) (b) h'
  simp[T]


Conclusion "
🔧 Cancellation will an important tool to use when reckoning with factoring.
"
