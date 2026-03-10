-- import GameServer
import Game.Levels.DivisionWorld.L07_division

World "DivisionWorld"
Level 8
Title "The actual division algorithm"

Introduction "
# Level 8

"

variable {Z : Type} [RRZ : RossRing Z]

/--
The tactic `exfalso` converts a goal `⊢ tgt` into `⊢ False`.
-/
TacticDoc exfalso

/--
As stated:
```
dvd_zero_rem (a b : Z) (hb : b ≠ 0) :
  b ∣ a → (divalg a b hb).r = 0
```
For all $a,b ∈ ℤ$, if $b ≠ 0$ and $b ∣ a$, then $r = 0$, where $r$ is the remainder produced from the division algorithm on $a$ and $b$.
-/
TheoremDoc dvd_zero_rem as "dvd_zero_rem"

/-- For all $a,b ∈ ℤ$, if $b ≠ 0$ and $b ∣ a$, then $r = 0$, where $r$ is the remainder produced from the division algorithm on $a$ and $b$.-/
Statement dvd_zero_rem (a b : Z) (hb : b ≠ 0) :
  b ∣ a → (divalg a b hb).r = 0 := by
  intro hba
  define D := divalg a b hb
  obtain h := D.nonneg
  rw[le_def] at h
  rcases h with T | F
  simp[T,D]
  obtain hbb := dvd_refl b
  obtain hbr := dvd_rem a b b hb hba hbb
  obtain habr := dvd_trans (abs b) b D.r (abs_dvd b) hbr
  obtain bler := dvd_le (abs b) D.r habr F
  obtain rltb := (divalg a b hb).lt
  exfalso
  exact lt_self (abs b) (le_lt_trans (abs b) D.r (abs b) bler rltb)



Conclusion "
🙌 Congrats! You've finished WOP World!
"

NewTactic exfalso
