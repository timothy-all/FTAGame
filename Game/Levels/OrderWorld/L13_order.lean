-- import GameServer
import Game.Levels.OrderWorld.L12_order

World "OrderWorld"
Level 13
Title "No zero divisors"

Introduction "
# **Level 13**
Boss fight! This is an important property of $ℤ$.
### **💡 Pro-tip**
In order to reduce the number of steps, focus on being economical here. For example, instead of
```
obtain h := ...
rcases h with ⟨patt⟩
```
just use the pattern matching functionality built-in to `obtain`:
```
obtain ⟨patt⟩ := ...
```
This is **⚠important⚠**, if anything, to keep the UI from feeling too *laggy*.

👉 We might start this level with
```
by_contra! F
```
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
mul_eq_zero : ∀ a b : Z,
  a * b = 0 → (a = 0 ∨ b = 0)
```
For all $a,b ∈ ℤ$, if $ab = 0$, then $a = 0$ or $b = 0$.
-/
TheoremDoc mul_eq_zero as "Ord : mul_eq_zero"

/-- If a product of integers is zero, then at least one of those integers is zero.-/
Statement mul_eq_zero (a b : Z) (h : a * b = 0) : (a = 0 ∨ b = 0):= by
  by_contra! F
  Hint "### **💡 Pro-tip**
  You might be tempted to use `rcases` to destructure `{F}`. We can skip this here though. If we want to refer to the `a ≠ 0` part of `{F}` we could use `{F}.left`. Similarly, `{F}.right` is the assumption `b ≠ 0`."
  obtain apos | aneg := ne_zero_dichotomy a F.left
  obtain bpos | bneg := ne_zero_dichotomy b F.right
  obtain F' := mul_closure a b apos bpos
  rw[h] at F'
  exact non_trivial F'
  obtain F' := mul_closure a (-b) apos bneg
  simp[← neg_mul_right,h] at F'
  exact non_trivial F'
  obtain bpos | bneg := ne_zero_dichotomy b F.right
  obtain F' := mul_closure (-a) b aneg bpos
  simp[← neg_mul_left,h] at F'
  exact non_trivial F'
  obtain F' := mul_closure (-a) (-b) aneg bneg
  simp[← neg_mul_left,← neg_mul_right,h] at F'
  exact non_trivial F'

Conclusion "
This facts separates ℤ from other rings like ℤ/6ℤ.
"
