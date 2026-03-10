-- import GameServer
import Game.Levels.OrderWorld.L03_order

World "OrderWorld"
Level 4
Title "Less-than is anti-reflexive."

Introduction "
# **Level 4**
This exercise is pretty short, but it'll feature in a lot of proofs by contradiction."

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
lt_self : ∀ a : Z, a < a → False
```
For all $a ∈ ℤ$, the statement $a < a$ is `False`.
-/
TheoremDoc lt_self as "Ord : lt_self"

/-- No integer is less than itself. -/
Statement lt_self : ∀ a : Z, a < a → False := by
  intro a h
  Hint "### ❯ More on `simp`
  We might be tempted to try
  ```
  simp at {h}
  ```
  But lean will complain *simp made no progress*. This is because `lt_def` is **not** tagged with `@[simp]`. That being said, we can instruct the `simp` tactic to use `lt_def`. 👉 Try:
  ```
  simp[lt_def] at {h}
  ```
  "
  simp[lt_def] at h
  Hint "**Here's what happend:**
  1. `simp` used `lt_def` to rewrite `{h}` as `{a} + -{a} ∈ Z⁺`
  2. `simp` used the `@[simp]` tagged axiom `add_neg_self` to rewrite `a + -a ∈ Z⁺` as `0 ∈ Z⁺`."
  exact non_trivial h


Conclusion "
### **⟳ `simp` updated**
This theorem is tagged with `@[simp]` so henceforth the tactic `simp` will replace targets like `a < a` with `False`.
"
