-- import GameServer
import Game.Levels.WOPWorld.L09_WOP

World "WOPWorld"
Level 10
Title "Archimedean Property"

Introduction "
# **Level 10**
Boss fight! This is sometimes called the **Archimedean Property** of $ℤ$.
### ❯ The `by_pow` tactic
  This is a good opportunity to use `POW`. You can use that theorem directly, or we've unlocked a new custom tactic `by_pow` (similar to `by_wop`). 🔍 Check out the entry for `by_pow` in the **Tactics** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

/--
The tactic `by_pow` splits the main goal into three subgoals. General usage looks like
```
by_pow S with M patt hmax
```
where
* `S` is a non-empty subset of ℤ (**the tactic will force you to prove this at the end**)
* `M` is the largest element of `S`
* `patt` is either an identifier, like `hMs`, which holds the hypothesis that `M ∈ S`, or a *pattern* (like in `rcases`) that can destructure the proposition `M ∈ S`
* `hmax` is the identifier for the hypothesis `hmax : ∀ (x : Z), x ∈ S → x ≤ M`.

### Goal 1
Keeps the original goal and hypotheses but adds the following hypotheses:
```
hne : S ≠∅
hbd : ∃ u : Z, ∀ x : Z, x ∈ S → x ≤ u
M : Z
hms : M ∈ S -- or destructured according to patt
hmax: ∀ (x : Z), x ∈ S → x ≤ M
```

### Goal 2
The new goal is `⊢ ∃ u, ∀ x : Z, x ∈ S → x ≤ u` under the original hypotheses and the additional hypothesis `hne : S ≠∅`.

### Goal 3
The new goal is `⊢ S ≠∅` under the original hypotheses.
-/
TacticDoc by_pow

/--
As stated:
```
Archimedean
  (a b : Z)
  (hb : 0 < b) :
    ∃ q : Z, 0 ≤ a + -(b * q)
```
For all $a, b ∈ ℤ$, if $b$ is non-zero, then there exists $q ∈ ℤ$ such that $0 ≤ a - bq$.
-/
TheoremDoc Archimedean as "WOP : Archimedean"

/-- For all a,b ∈ ℤ, if 0 < b, then there exists q ∈ ℤ such that 0 ≤ a - bq. -/
Statement Archimedean
  (a b : Z)
  (hb : 0 < b) :
    ∃ q : Z, 0 ≤ a + -(b * q) := by
  by_contra! F
  define S := { s : Z | ∃ x : Z, s = a + -(b * x)}
  by_pow S with M ⟨x,hx⟩ hmax
  obtain ⟨y, hy⟩ := mul_step_up a b x hb
  obtain hyS : (a + -(b * y)) ∈ S
  use y
  rfl
  obtain F' := hmax (a + -(b * y)) hyS
  rw[← hx] at hy
  exact lt_self (a + -(b * y)) (le_lt_trans (a + -(b * y)) M (a + -(b * y)) F' hy)
  use 0
  intro s ⟨x, hx⟩
  right
  rw[hx]
  exact F x
  use a
  use 0
  simp


Conclusion "
🙌 ***Congrats!*** You've cleared WOP World!
"

NewTactic by_pow
