-- import GameServer
import Game.Metadata
import Game.Levels.TestWorld.L06_test

World "RingWorld"
Level 7
Title "Simple Cancellation"

Introduction "
# **Level 7**
This level is more of a side quest. We'll need it for the mini-boss in a couple levels. It'll also give us more practice using the `obtain` tactic.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
add_eq_self : ∀ a b : Z, a + b = a → b = 0
```
For all $a, b ∈ ℤ$, we have that $a + b = a$ implies that $b = 0$.
-/
TheoremDoc add_eq_self as "Rng : add_eq_self"

/-- A simple additive cancellation rule.-/
Statement add_eq_self : ∀ a b : Z, a + b = a → b = 0 := by
  intro a b h
  Hint "We'd like to add `-{a}` on the right of the equality stored in the hypothesis `{h}`."
  obtain h' := add_on_right (a + b) a (-a) h
  Hint "Now let's see about using what we know to simplify the hypothesis `{h'}`."
  rw[add_neg_self] at h'
  Hint "That was a natural first step. The next might be tricky. We have
  ```
  {h'} : ({a} + {b}) + -{a}
  ```
  It might be good to commute the `{a} + {b}` term. If we were to try
  ```
  rw[add_comm] at {h'}
  ```
  we would obtain
  ```
  {h'} : -{a} + ({a} + {b}) = 0
  ```
  ***But that's not what we wanted!*** This is because `rw[add_comm] at {h'}` applies the theorem `add_comm` to the *first* addition expression encountered in `{h'}`. We need to supply a little guidance to `add_comm` in order to commute the specific addition expression we have in mind.

  The theorem `add_comm` is the proposition:
  ```
  ∀ x y : Z, x + y = y + x
  ```
  This means that `add_comm {a}` is the proposition:
  ```
  ∀ y : Z, {a} + y = y + {a}
  ```
  👉 Accordingly, you might try to
  ```
  rw[add_comm a] at {h'}
  ```
  "
  rw[add_comm a] at h'
  Hint "Notice how `{a} + {b}` became `b + a`. We could have been even more verbose and used
  ```
  rw[add_comm {a} {b}] at {h'}
  ```
  This tactic would have searched `{h'}` explicitly for expressions of the form `{a} + {b}`. The first such expression it finds gets rewritten as `{b} + {a}`."
  rw[add_assoc] at h'
  rw[add_neg_self] at h'
  rw[add_zero] at h'
  exact h'


Conclusion "
### **💡 Pro-tip**
The moral of the story in this level: *it can be helpful to guide the contents of the `rw` tactic.* In general, we have that
```
rw[add_comm a] at h
```
will search `h` for the first expression of the form `a + x` where `a` is fixed and `x : Z` can be anything. Once found, it will replace `a + x` with `x + a`. The *underscore* character often acts as a wildcard in Lean. For example:
```
rw[add_comm _ b] at h
```
will search `h` for the first expression of the form `x + b` where `b` is fixed and `x : Z` can be anything. Once found, it will replace `x + b` with `b + x`.
"

NewTheorem add_eq_self
