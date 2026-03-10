-- import GameServer
import Game.Levels.TestWorld.L14_test

World "RingWorld"
Level 15
Title "Dividing a factor implies dividing the product"

Introduction "
# **Level 15**
This will give us a little more practice with `mul_assoc`.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
dvd_mul : ∀ a b c : Z, a ∣ b → a ∣ b * c
```
If an integer divides a factor of a product, then that integer divides the product as well. In particular, for all $a,b,c ∈ ℤ$, if $a ∣ b$, then $a ∣ b · c$.
-/
TheoremDoc dvd_mul as "Rng : dvd_mul"

/-- If an integer divides a factor of a product, then that integer divides the product as well.-/
Statement dvd_mul : ∀ a b c : Z, a ∣ b → a ∣ b * c := by
  intro a b c h
  Hint "### **💡 `rcases` tip**
  First, let's destructure {h} **without** using `rw[dvd_def]`. 👉 Specifically, try:
  ```
  rcases hpf : {h} with ⟨ d,hd ⟩
  ```
  Using this syntax **keeps** the hypothesis `{h}` in addition to adding the destructured content to the proof state."
  rcases hpf : h with ⟨ d, hd ⟩
  Hint "💡 **Note:** we still have the hypothesis `{h}`! This isn't needed here but it can be handy in the future. Now, supply a witness to the existential goal."
  use d * c
  rw[hd,mul_assoc]


Conclusion "
It's nice to be able to `rw[dvd_def]` once or twice to see the definition. But from here on out, we shouldn't bother.
"
