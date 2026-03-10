-- import GameServer
import Game.Levels.GCDWorld.L03_GCD

World "GCDWorld"
Level 4
Title "Symmetry of linear combinations"

Introduction "
# **Level 4**
We want to know more about the set of positive linear combinations of two given integers $a$ and $b$. Accordingly we've defined ...
### 🕮 The set `Bez a b`
For `a b : Z` we define `Bez a b` to be the set of all positive linear combinations of `a` and `b`. 🔍 Check out the definition of the set `Bez` in the **Definitions** tab.
"

variable {Z : Type} [RRZ : RossRing Z]

def Bez (a b : Z) : Set Z :=
  {d : Z | 0 < d ∧ ∃ x y : Z, a * x + b * y = d}

/--
For `a b : Z`, the set `Bez a b` is defined as follows:
```
def Bez (a b : Z) : Set Z :=
  {d : Z | 0 < d ∧ ∃ x y : Z, a * x + b * y = d}
```
In other words, `Bez a b` represents the set of positive linear combinations of `a` and `b`.
-/
DefinitionDoc Bez as "Bez"

/--
As stated:
```
Bez_symm
  (a b : Z) :
  (Bez a b ⊆ Bez b a) ∧ (Bez b a ⊆ Bez a b)
```
The set of positive linear combinations of $a$ and $b$ is equal to the set of positive linear combinations of $b$ and $a$.
-/
TheoremDoc Bez_symm as "GCD : Bez_symm"


/-- The set of positive linear combinations of $a$ and $b$ is equal to the set of positive linear combinations of $b$ and $a$.-/
Statement Bez_symm (a b : Z) : (Bez a b ⊆ Bez b a) ∧ (Bez b a ⊆ Bez a b):= by
  constructor
  intro d ⟨hd,x,y,eq⟩
  refine ⟨hd,?_⟩
  use y; use x
  rw[add_comm]
  exact eq
  intro d ⟨hd,x,y,eq⟩
  refine ⟨hd,?_⟩
  use y; use x
  rw[add_comm]
  exact eq

Conclusion "
🔧 This exercise will keep us from redundantly, superfluously, and repeatedly repeating ourselves over and over and over again.
"

NewDefinition Bez
