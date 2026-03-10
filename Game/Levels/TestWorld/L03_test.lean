-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L02_test

World "RingWorld"
Level 3
Title "Multiplication on the left"

Introduction "
# **Level 3**
Now try to apply what you've learned to prove `mul_on_left` This should also be *very* similar to how we proved `add_on_right`.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
mul_on_right : ∀ a b c : Z, a = b → a * c = b *c
```
Multiplication on the left of an equality:
$$ ∀ a,b,c ∈ ℤ, if a = b, then ca = cb.$$
-/
TheoremDoc mul_on_left as "Rng : mul_on_left"

/-- We can also multiply on the right across an equality of integers.-/
Statement mul_on_left : ∀ a b c : Z, a = b → c * a  = c * b := by
  intro a b c h
  Hint "### **← Backwards substitution**
  👉 Try
  ```
  rewrite[← {h}]
  ```
  ### **⌨ Typesetting-tip**
  We use `\\left` to produce the pretty printed left-arrow `←`. You can also use `<-`."
  rewrite[← h]
  Hint "💡 **Important:** Notice how this substituted `{a} = {b}` in the *backwards* direction? In other words, it replaced all `{b}`s with `{a}`s in the goal. This is an important feature we'll use a lot going forward."
  rfl

Conclusion "
### **💡 Pro-tip**

The backwards rewrite `rewrite[← h]` and its variant `rw[← h]` are very useful. If `h : a = b` then...
* `rw[h]` is a *forward* substitution (substituting `b` for `a`) while...
* `rw[← h]` is a backward substitution (substituting `a` for `b`).

Rewrites are commonly applied to equalities but they can also be applied hypotheses like `h : p ↔ q`. So `rw[h]`, in this case, would substitute the proposition `q` for the proposition `p`.
"
