-- import GameServer
import Game.Levels.WOPWorld
import Game.Levels.absWorld

World "DivisionWorld"
Level 1
Title "A necessary and sufficient condition for divides"

Introduction "
# **Level 1**
For ease of use, we define ...
### 🔧 The set `Rem a b`
For $a, b ∈ ℤ$, the set of all integers $s$ such that $0 ≤ s$ and there exists $q ∈ ℤ$ such that $s = a - bq$ represents all possible **remainders** for $a/b$. In Lean, we've defiend this set as `Rem a b`. 🔍 Check out the entry for `Rem` in the **Definitions** tab. We'll be investigating this set in preparation for the **division algorithm**.
"

variable {Z : Type} [RRZ : RossRing Z]

def Rem (a b : Z) : Set Z :=
  {s : Z | 0 ≤ s ∧ ∃ q : Z, s = a + -(b * q)}

/--
For $a,b ∈ ℤ$, the set `Rem a b` represents the set of all integers $s$ such that $0 ≤ s$ and there exists $q ∈ ℤ$ such that $s = a - bq$. In other words, `Rem a b` represents all possible remainders for $a/b$.

Here's what it looks like in Lean:
```
def Rem (a b : Z) : Set Z :=
  {s : Z | 0 ≤ s ∧ ∃ q : Z, s = a + -(b * q)}
```
-/
DefinitionDoc Rem as "Rem"

/--
As stated:
```
dvd_iff (a b : Z) : b ∣ a ↔ 0 ∈ Rem a b
```
For all integers $a,b$, if $b$ divides $a$, then $0$ is an element of the set

$$ \{ s ∈ Z ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \} $$
-/
TheoremDoc dvd_iff as "Div : dvd_iff"

/-- For all $a,b ∈ ℤ$, if $b ∣ a$, then $0$ is an element of the set
$\{ s ∈ Z ∣ 0 ≤ s ∧ ∃ q ∈ ℤ, s = a - bq \}$. -/
Statement dvd_iff (a b : Z) : b ∣ a ↔ 0 ∈ Rem a b := by
  constructor
  intro hab
  Hint "To belong to the set `Rem a b` is a proposition, specifically a conjunction. 👉 In that case, it makes sense to try `constructor`."
  constructor
  left
  rfl
  rcases hab with ⟨ d , hd⟩
  use d
  rw[hd,add_neg_self]
  intro ⟨ z, ⟨ q, hq ⟩⟩
  use q
  symm at hq
  obtain hq' := neg_unique a (-(b * q)) hq
  simp at hq'
  rw[hq']

Conclusion "
"

NewDefinition Rem
