-- import GameServer
import Game.Levels.OrderWorld

World "absWorld"
Level 1
Title "Integers divide their absolute value"

Introduction "
# **Level 1**
We'll need **absolute values** in this world.
### 🕮 `abs`
🔍 Check out the definition for `abs` in the **Definitions** tab. Pay close attention to the definition. 💡 Given that definition, it makes sense to work `by_cases` in a particular way here...
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
dvd_abs : ∀ a : Z, a ∣ abs a
```
For all $a ∈ ℤ$, $a$ divides $|a|$.
-/
TheoremDoc dvd_abs as "Abs : dvd_abs"

/--
The absolute value of an integer. If $a ∈ ℤ$, then $|a| = -a$ if $a <0$; otherwise $|a| = a$. In Lean, we write `abs a` for $|a|$. Here's what it looks like in Lean:
```
noncomputable def abs (a : Z) : Z := by
  classical
  by_cases h : a < 0
  · exact -a
  · exact a
```
-/
DefinitionDoc abs as "abs"

/-- For every integer $a$, $a$ divides $|a|$.-/
Statement dvd_abs : ∀ a : Z, a ∣ abs a := by
  intro a
  by_cases ha : a < 0
  Hint "We'd like to use hypothesis `{ha}` to simplify the term `abs a` in the goal. 👉 We might try
  ```
  simp[abs]
  ```
  This tells the `simp` tactic to use the definition of `abs` to unfold the goal.
  "
  simp[abs]
  Hint "👉 Now try
  ```
  simp[{ha}]
  ```
  This tells the `simp` tactic to try to use `ha` (along with all other statements tagged with `@[simp]`) to try to simplify the target.
  "
  simp[ha]
  Hint "### **💡 Pro-tip**
  We also could have used:
  ```
  simp[abs,ha]
  ```
  to get this all done in one go. ⏮ You can go back and give this a try."
  use -1
  simp[← neg_mul_right]
  simp[abs,ha]
  exact dvd_refl a

Conclusion "
We'll prove that `abs a ∣ a` in the next level for more practice.
"

NewDefinition abs
