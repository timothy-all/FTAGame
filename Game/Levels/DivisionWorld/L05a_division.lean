-- import GameServer
import Game.Levels.DivisionWorld.L04_division

World "DivisionWorld"
Level 5
Title "The actual division algorithm"

Introduction "
# **Level 5**
This one is important, it's the linchpin for a lot of arguments involving division.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
doc
-/
TheoremDoc rem_ne as "rem_ne"

Statement rem_ne (a b : Z) (hb : b ≠ 0) : {s : Z | 0 ≤ s ∧ ∃ q : Z, s = a + -(b * q)} ≠∅ := by
  by_cases ha : 0 ≤ a
  use a
  constructor
  exact ha
  use 0
  simp
  simp at ha
  by_cases h : b < a
  use a + -b
  constructor
  rw[le_def]
  right
  simpa[lt_def] using h
  use 1
  simp
  simp at h





Conclusion "
🙌 Congrats! You've finished WOP World!
"
