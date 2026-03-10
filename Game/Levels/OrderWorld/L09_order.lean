-- import GameServer
import Game.Levels.OrderWorld.L08_order

World "OrderWorld"
Level 9
Title "Addition across an inequality"

Introduction "
# **Level 9**
This level is an exercise in patience. Try to combine rewrites to keep the number of tactic calls down. You can always apply a rewrite, determine the next rewrite from the updated tactic state (if necessary), then ⏮ go back to the previous prompt.
"

variable {Z : Type} [RRZ : RossRing Z]


/--
This is a "finishing" tactic modification of simp. General usage looks like:
* `simpa [rules, ⋯] using e` will simplify the goal and the type of `e` using rules, then try to close the goal using `e`.
* `simpa [rules, ⋯]` will simplify the goal and the type of a hypothesis `this` if present in the context, then try to close the goal using the `assumption` tactic which, in turn, tries to solve the main goal by using a hypothesis of a compatible type.
-/
TacticDoc simpa

/--
As stated:
```
add_le_lt : ∀ a b c d : Z,
  a ≤ b → c < d → a + c < b + d
```
For all $a,b,c,d ∈ ℤ$, if $a$ is less than or equal to $b$ and $c$ is less than $d$, then $a + c$ is less than $b + d$.
-/
TheoremDoc add_le_lt as "Ord : add_le_lt"

/-- For all $a,b,c,d ∈ ℤ$, if $a$ is less than or equal to $b$ and $c$ is less than $d$, then $a + c$ is less than $b + d$.-/
Statement add_le_lt : ∀ a b c d : Z, a ≤ b → c < d → a + c < b + d := by
  intro a b c d aleb cltd
  Hint "Let's try to break `{aleb}` into cases."
  rcases aleb with aeqb | altb
  Hint "Rewrite the goal with `{aeqb}`."
  rw[aeqb]
  Hint "👉 Now try to rewrite the goal in the following form:
  ```
  ⊢ {b} + -{b} + ({d} + -{c}) ∈ Z⁺
  ```
  This will involve quite a few rewrites.
  "
  rw[lt_def,← neg_add,add_assoc,← add_assoc d,add_comm d,add_assoc (-b),← add_assoc]
  Hint "### ❯ The `simpa` tactic
  We're nearly at our goal -- the rest is busy work. We could use
  ```
  simp
  rw[← lt_def]
  exact {cltd}
  ```
  Or we can try the `simpa` tactic. 🔍 Check the entry for `simpa` in the **Tactics** tab. 👉 In our situation, we can clear the goal at this point with
  ```
  simpa[lt_def] using {cltd}
  ```
  Here's how it works in this case:
  * the goal is first simplified to `{d} + -{c}` using tagged `@[simp]` lemmas (namely `add_neg_self` and `zero_add`);
  * the hypothesis `{cltd}` is simplified using `lt_def` thereby turning it into `{cltd} : {d} + -{c} ∈ Z⁺`;
  * finally it attempts to close the goal using `{cltd}` (which succeeds).
  "
  simpa[lt_def] using cltd
  Hint "We're now in the case where `{altb} : {a} < {b}`."
  obtain h := add_closure (b + -a) (d + -c) altb cltd
  rw[add_assoc,← add_assoc (-a),add_comm (-a),add_assoc d,← add_assoc,neg_add] at h
  simpa[lt_def] using h


Conclusion "
### **💡 Pro-tip**
If you find yourself using `simp`, applying a definition, then using `exact` to close a goal, then this might have been a good opportunity to use `simpa`.
"

NewTactic simpa
