-- import GameServer
import Game.Levels.TestWorld.L15_test

World "RingWorld"
Level 16
Title "The divides relation and linear combinations"

Introduction "
# **Level 16**
Boss fight! The hardest part of this boss is the careful rewriting we'll have to do at the end. **Note:** we've already introduced the variables `a b x y d` for you.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
dvd_linear (a b x y d : Z) : d ∣ a → d ∣ b → d ∣ a * x + b * y
```
If an integer $d$ divides a pair of integers, say $a$ and $b$, then $d$ divides any linear combination of $a$ and $b$.
-/
TheoremDoc dvd_linear as "Rng: dvd_linear"


/-- If an integer $d$ divides a pair of integers, say $a$ and $b$, then $d$ divides any linear combination of $a$ and $b$.-/
Statement dvd_linear (a b x y d : Z) : d ∣ a → d ∣ b → d ∣ a * x + b * y := by
  intro da db
  rcases da with ⟨ p, hp ⟩
  rcases db with ⟨ q, hq ⟩
  use x * p + y * q
  Hint "We now need to carefully rewrite."
  rw[mul_add,mul_comm x,mul_comm y,← mul_assoc d,← mul_assoc d,hp,hq]


Conclusion "
🙌 ***Congrats!*** You've beaten Ring World!
"
