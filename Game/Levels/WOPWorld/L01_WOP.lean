-- import GameServer
import Game.Levels.OrderWorld

World "WOPWorld"
Level 1
Title "Set membership"

Introduction "
# **Level 1**
We'll need to know how to reckon with sets in this world (and future worlds).
### 🕮 `Set`
The main purpose of this level is to introduce how sets are codified in Lean. 🔍 Check out the entries for the following in the **Definitions** tab:
* `Set`
* `Set.mem`
* `mem_def`
"

variable {Z : Type} [RRZ : RossRing Z]


/--
As stated:
```
mem_flip_set
  (S : Set Z)
  (u x : Z) :
  x ∈ S → u + -x ∈ {y : Z | ∃ s ∈ S, y = u + -s}
```
Suppose $S ⊆ ℤ$, $u ∈ ℤ$, and $x ∈ S$. Then $u + -x$ belongs to the inverted set

$$ u + -x ∈ \{y ∈ Z ∣ ∃ s ∈ S, y = u + -s\} $$
-/
TheoremDoc mem_flip_set as "WOP : mem_flip_set"

/--
`Set` is a *structure* with a single field `mem` (codifying membership). Here's what it looks like in Lean.
```
structure Set (α : Type) where
  mem : α → Prop
```
-/
DefinitionDoc Set as "Set"

/--
Set membership is handled via the following *instance*
```
instance {α : Type} : Membership α (Set α) where
  mem S x := S.mem x
```
In summary, `x ∈ S` means `S.mem x` -- in other words, sets are really just defined by the propositions that specify their membership rules in the `mem` field of their structure.
-/
DefinitionDoc Set.mem as "Set.mem"

/--
This is a helper lemma for unfolding membership propositions of explicit sets.
If `S` is an explicit set with an explicit membership proposition, this can be exposed with the help of:
```
theorem mem_def {α : Type} (S : Set α) (x : α) :
  x ∈ S ↔ S.mem x
```
For example, suppose `S := {s : Z | 0 < s ∧ s ∣ a}` and we have the hypothesis `h : d ∈ S`. Then `simp[S,mem_def] at h` will unfold the proposition behind the membership and produce:
```
h : 0 < d ∧ d ∣ a
```
Similarly, if `h : ¬ d ∈ S`, then `simp[S,mem_def]` will produce
```
h : 0 < d → ¬ (d ∣ a)
```
-/
DefinitionDoc mem_def as "mem_def"

/-- Suppose $S ⊆ ℤ$, $u ∈ ℤ$, and $x ∈ S$. Then $u + -x$ belongs to the flipped set $ \{y ∈ Z ∣ ∃ s ∈ S, y = u + -s\}. $-/
Statement mem_flip_set (S : Set Z) (u x : Z)  : x ∈ S → u + -x ∈ {y : Z | ∃ s ∈ S, y = u + -s} := by
  intro hx
  Hint "### **Set membership**
  Our goal is of the form `a ∈ A`. ***This is just a proposition in disguise!*** Specifically, in **set-builder** notation (like what we're using here) the proposition proceeding the `∣` symbol (unicode U+007C i.e. the *vertical bar*) is our **membership proposition**. In this particular setting, this means that to say `x ∈ S` like in `{hx}` is just sugar for:
  ```
  ∃ s : Z, s ∈ S ∧ x = u + -s
  ```
  Similarly, this means our goal is an *existential* statement in disguise. We need a witness...
  "
  use x
  Hint "👉 The `simp` tactic might be handy here."
  simp[hx]


Conclusion "
### **💡 Pro-tip**
If `A` is a set whose membership proposition is `p` then `a ∈ A` means `p a` (or rather the proposition `p a` is true).
"

NewDefinition Set Set.mem mem_def
