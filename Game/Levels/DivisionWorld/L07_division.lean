-- import GameServer
import Game.Levels.DivisionWorld.L06_division

World "DivisionWorld"
Level 7
Title "The actual division algorithm"

Introduction "
# Level 7

"

variable {Z : Type} [RRZ : RossRing Z]

noncomputable def divalg (a b : Z) (hb : b ≠ 0) : DivAlg a b hb := by
  obtain div_alg_ab := div_alg a b hb
  let Q : Z := Classical.choose div_alg_ab
  obtain Q_spec := Classical.choose_spec div_alg_ab
  let R : Z := Classical.choose Q_spec
  obtain R_spec := Classical.choose_spec Q_spec
  refine
  { q := Q
    r := R
    eq := R_spec.left
    nonneg := R_spec.right.left
    lt := R_spec.right.right
  }
attribute [irreducible] divalg

/--
The definition of `divalg a b hb` is a proof of the structure `DivAlg a b hb` which has the following form:
```
structure DivAlg (a b : Z) (hb : b ≠ 0) where
  (q : Z)
  (r : Z)
  (eq : a = b * q + r)
  (nonneg : 0 ≤ r)
  (lt : r < abs b)
```
This means that `divalg a b hb` has five fields, specifically:
* `(divalg a b hb).q` is the quotient of the division algorithm on `a` and `b`
* `(divalg a b hb).r` is the remainder of the division algorithm on `a` and `b`
* `(divalg a b hb).eq` is the equality relating `a b q r`
* `(divalg a b hb).nonneg` is the proposition `0 ≤ r`
* `(divalg a b hb).lt` is the proposition `r < abs b`.

For transparency, here is the proof of `divalg a b hb` -- the hardest part is proving `div_alg` which we proved together.
```
noncomputable def divalg (a b : Z) (hb : b ≠ 0) : DivAlg a b hb := by
  obtain D := div_alg a b hb
  let Q : Z := Classical.choose D
  obtain Q_spec := Classical.choose_spec D
  let R : Z := Classical.choose Q_spec
  obtain R_spec := Classical.choose_spec Q_spec
  refine
  { q := Q
    r := R
    eq := R_spec.left
    nonneg := R_spec.right.left
    lt := R_spec.right.right
  }
```
-/
DefinitionDoc divalg as "divalg"

/--
As stated:
```
div_rem (a b d : Z) (hb : b ≠ 0) :
  let D := divalg a b hb
  d ∣ a → d ∣ b → d ∣ D.r
```
For all $a,b,d ∈ ℤ$, if $b ≠ 0$, $d ∣ a$, and $d ∣ b$, then $d ∣ r$ where $r$ is the remainder produced from the division algorithm on $a$ and $b$.
-/
TheoremDoc dvd_rem as "div_rem"

/-- For all $a,b,d ∈ ℤ$, if $b ≠ 0$, $d ∣ a$, and $d ∣ b$, then $d ∣ r$ where $r$ is the remainder produced from the division algorithm on $a$ and $b$.-/
Statement dvd_rem (a b d : Z) (hb : b ≠ 0) :
  d ∣ a → d ∣ b → d ∣ (divalg a b hb).r := by
  intro hda hdb
  rw[dvd_def] at hda hdb ⊢
  rcases hda with ⟨x, hx ⟩
  rcases hdb with ⟨y, hy ⟩
  use x + -(y * (divalg a b hb).q)
  rw[mul_add,← neg_mul_right,← mul_assoc,← hx,← hy]
  simp[(divalg a b hb).eq]
  rw[add_comm (b * (divalg a b hb).q)]
  simp[add_assoc]


Conclusion "
🙌 Congrats! You've finished WOP World!
"

NewDefinition divalg
