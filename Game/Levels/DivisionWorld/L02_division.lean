-- import GameServer
import Game.Levels.DivisionWorld.L01_division

World "DivisionWorld"
Level 2
Title "Positive remainders"

Introduction "
# **Level 2**
This is another helper lemma. Can you anticipate why we might be interested in conditions where our set of remainders is definitely contained in $ℤ⁺$? 👀
"

variable {Z : Type} [RRZ : RossRing Z]

/--
As stated:
```
not_dvd_pos
  (a b : Z) :
    ¬ b ∣ a → Rem a b ⊆ Zplus
```
For all integers $a,b$, if $b$ does not divide $a$, then

$$ \{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \} ⊆ ℤ⁺ $$
-/
TheoremDoc not_dvd_pos as "Div : not_dvd_pos"

/-- For all $a,b ∈ ℤ$, if $b$ does not divide $a$, then
$\{s ∈ ℤ ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \} ⊆ ℤ⁺$. -/
Statement not_dvd_pos (a b : Z) : ¬ b ∣ a → Rem a b ⊆ Zplus:= by
  intro h s hs
  rcases _ : hs with ⟨rfl | lt, q, eq⟩
  rw[← dvd_iff] at hs
  contradiction
  simp[mem_Zplus,lt]


Conclusion "
"
