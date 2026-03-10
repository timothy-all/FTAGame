-- import GameServer
import Game.Levels.GCDWorld.L02_GCD


World "GCDWorld"
Level 3
Title "Greatest common divisors are positive"

Introduction "
# **Level 3**
The real purpose of this level is to showcase how we'll use gcds going forward. That being said, the exercise itself is also useful.
### 🕮 `gcd`
In Lean, we write `(gcd a b).g` for the greatest common divisor of $a$ and $b$. Indeed, the definition of `gcd` is a **structure** whose fields captures relevant data about greatest common divisors:
* `(gcd a b).g` is the **integer** `g` representing the greatest common divisor itself
* `(gcd a b).left` is the **proposition** that `g ∣ a`
* `(gcd a b).right` is the **proposition** that `g ∣ b`
* `(gcd a b).le` is the **proposition** that
```
¬(a=0 ∧ b=0) → ∀ d:Z, d ∣ a → d ∣ b → d ≤ g
```
If `a = 0 ∧ b = 0`, then `(gcd a b).g = 0`, by definition. 🔍 Check out the entry for `gcd` in the **Definitions** tab for more details.
"

variable {Z : Type} [RRZ : RossRing Z]

noncomputable def gcd (a b : Z) : GCD a b := by
  by_cases h : a = 0 ∧ b = 0
  refine
  { g := (0 : Z)
    left := by
      rw[dvd_def]
      use 1
      simp
      exact h.left
    right := by
      rw[dvd_def]
      use 1
      simp
      exact h.right
    le := by
      intro F
      contradiction
    }
  obtain gcd_exists := gcd_exists a b h
  let G : Z := Classical.choose gcd_exists
  obtain G_spec := Classical.choose_spec gcd_exists
  refine
  { g := G
    left := by
      exact G_spec.left
    right := by
      exact G_spec.right.left
    le := by
      intro h'
      exact G_spec.right.right
    }

/--
The definition of `gcd a b` is a **proof** of the structure `GCD a b` which has the following form:
```
structure GCD (a b : Z) where
  (g : Z)
  (left : g ∣ a )
  (right : g ∣ b)
  (le : ¬ (a = 0 ∧ b = 0) →
    ∀ d : Z, (d ∣ a →  d ∣ b → d ≤ g ))
```
This means that `gcd a b` has four fields, specifically:
* `(gcd a b).g` refers to the greatest common divisior itself
* `(gcd a b).left` is the proposition that `g ∣ a`
* `(gcd a b).right` is the proposition that `g ∣ b`
* `(gcd a b).le` is the proposition that `¬ (a = 0 ∧ b = 0) → ∀ d : Z, d ∣ a → d ∣ b → d ≤ g)`.

By convention, we define `(gcd 0 0).g := 0`. For transparency, here is the proof of `gcd a b` -- the hardest part is `gcd_exists` which we've proven together and used here.
```
noncomputable def gcd (a b : Z) : GCD a b := by
  by_cases h : a = 0 ∧ b = 0
  refine
  { g := (0 : Z)
    left := by
      rw[dvd_def]
      use 1
      simp
      exact h.left
    right := by
      rw[dvd_def]
      use 1
      simp
      exact h.right
    le := by
      intro F
      contradiction
    }
  obtain gcd_exists := gcd_exists a b h
  -- choose G to satisfy the predicate
  let G : Z := Classical.choose gcd_exists
  -- obtain spec for G
  obtain G_spec := Classical.choose_spec gcd_exists
  refine
  { g := G
    left := by
      exact G_spec.left
    right := by
      exact G_spec.right.left
    le := by
      intro h'
      exact G_spec.right.right
    }
```
-/
DefinitionDoc gcd as "gcd"

/--
As stated:
```
gcd_pos : ∀ a b : Z, b ≠ 0 → 0 < (gcd a b).g
```
For all $a,b ∈ ℤ$, if $b ≠ 0$, then $0 < \gcd(a,b)$.
-/
TheoremDoc gcd_pos as "GCD : gcd_pos"

/-- For all $a,b ∈ ℤ$, if $b ≠ 0$, then $0 < \gcd(a,b)$.-/
Statement gcd_pos : ∀ a b : Z, b ≠ 0 → 0 < (gcd a b).g := by
  intro a b hb
  obtain h : ¬(a = 0 ∧ b = 0)
  by_contra F
  exact hb F.right
  obtain eq | lt := (gcd a b).le h 1 (one_dvd a) (one_dvd b)
  rw[← eq]
  exact one_pos
  exact lt_trans 0 1 (gcd a b).g one_pos lt



Conclusion "
"

NewDefinition gcd
