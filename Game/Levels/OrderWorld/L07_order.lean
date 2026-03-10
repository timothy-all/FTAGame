-- import GameServer
import Game.Levels.OrderWorld.L06_order


World "OrderWorld"
Level 7
Title "Subtraction swap across less-than"

Introduction "
# **Level 7**
This level will give us more practice with `simp`.
"

variable {Z : Type} [RRZ : RossRing Z]



/--
As stated:
```
add_neg_lt_swap : ∀ a b c : Z,
  a + -b < c → a + -c < b
```
For all $a,b c ∈ ℤ$, if $a - b < c$, then $a - c < b$.
-/
TheoremDoc add_neg_lt_swap as "Ord : add_neg_lt_swap"

/-- For all $a,b,c ∈ ℤ$, if $a - b < c$, then $a - c < b$.-/
Statement add_neg_lt_swap : ∀ a b c : Z, a + -b < c → a + -c < b := by
  intro a b c h
  simp[lt_def,← neg_add] at h ⊢
  Hint "We now need to manually simplify either `{h}` or the goal `⊢`."
  rw[← add_assoc,add_comm,add_comm b]
  exact h

Conclusion "
### **💡 Pro-tip**
We'll continue to update `simp` as needed throughout the game.
"
