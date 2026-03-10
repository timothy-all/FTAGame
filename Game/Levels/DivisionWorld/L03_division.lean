-- import GameServer
import Game.Levels.DivisionWorld.L02_division

World "DivisionWorld"
Level 3
Title "Divisors and remainders"

Introduction "
# **Level 3**
This level answers the question: what can we conclude if a remainder is at least as large as the divisor?
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
divisor_lt_rem
  (a b r: Z) :
  0 < b → r ∈ Rem a b → b ≤ r →
    ∃ r' : Z, r' ∈ Rem a b ∧ r' < r
```
For all $a,b,r ∈ ℤ$, if $0 < b ≤ r$ and $r ∈ \{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \}$, then $r - b ∈ \{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \}$
-/
TheoremDoc divisor_le_rem as "Div : divisor_le_rem"


/-- For all $a,b,r ∈ ℤ$, if $0 < b ≤ r$ and $r ∈ \{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \}$, then there exists $r' ∈ ℤ$ such that $r' ∈ \{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \}$ and $r' < r$.-/
Statement divisor_le_rem (a b r: Z) : 0 < b → r ∈ Rem a b → b ≤ r → ∃ r' : Z, r' ∈ Rem a b ∧ r' < r := by
  intro hb ⟨hr,q, eq⟩ le
  use r + -b
  constructor
  constructor
  rcases le with rfl | lt
  simp[le_def]
  right
  simpa[lt_def]
  use q + 1
  rw[mul_add,← neg_add,← add_assoc,mul_one]
  rw[eq]
  apply add_neg_lt_swap
  simp[hb]

Conclusion "
"
