-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L01_test

World "RingWorld"
Level 2
Title "Addition on the left"

Introduction "
# **Level 2**
Try to apply what you've learned to prove `add_on_left` This should be *very* similar to how we proved `add_on_right`.
### **Theorems**
🔍 Check out the **Theorems** tab in the right-pane (currently highlighted). These are the theorems that we'll prove as we progress through the game. Theorems cannot be used until they are proven. Once a theorem is proven, then it is 🔓 unlocked and can be used in future levels.

"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
add_on_left : ∀ a b c : Z, a = b → c + a = c + b
```
Addition on the left of an equality. For all $a,b,c ∈ ℤ$, if $a = b$, then $c + a = c + b.$
-/

TheoremDoc add_on_left as "Rng : add_on_left"

/-- Similarly, we can add on the left across an equality of integers. -/
Statement add_on_left : ∀ a b c : Z, a = b → c + a = c + b := by
  intro a b c h
  Hint "Now let's try a rewrite with `rw`."
  rw[h]

Conclusion "
If you used `rewrite` and then `rfl`, ⏮ go back and try just `rw`. Let's try a similar statement but with multiplication.
"
