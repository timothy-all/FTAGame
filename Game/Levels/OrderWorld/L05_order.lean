-- import GameServer
import Game.Levels.OrderWorld.L04_order

World "OrderWorld"
Level 5
Title "Not less-than"

Introduction "
# **Level 5**
Here's our first **if and only if** statement. Remember: `P ↔ Q` means
```
(P → Q) ∧ (Q → P)
```
So our goal in this level is a **conjunction**.
### ❯ The `constructor` tactic
If we have a goal of the form `⊢ G₁ ∧ G₂`, then we typically just split our work into two goals -- first we prove `G₁`, then we prove `G₂`. The tactic that implements this strategy is `constructor`. 🔍 Check out the entry in the **Tactics** tab. Note: we've already introduced `a b : Z` this time. 👉 Try:
```
constructor
```
to get started.
"

variable {Z : Type} [RRZ : RossRing Z]

@[simp] theorem lt_self_simp (a : Z) : ¬ a < a := by
  by_contra F
  exact lt_self a F

@[simp] theorem neg_neg : ∀ a : Z, - -a = a := by
  intro a
  obtain h := neg_self_add a
  symm
  exact neg_unique (-a) (a) h

@[simp] theorem neg_eq : ∀ a b : Z, -a = -b ↔ a = b := by
  intro a b
  constructor
  intro h
  obtain h1 := add_on_right (-a) (-b) a h
  simp at h1
  symm at h1
  obtain want := neg_unique (-b) a h1
  rw[neg_neg] at want
  exact want
  intro h
  obtain h1 := add_on_right a b (-a) h
  simp at h1
  symm at h1
  obtain want := neg_unique b (-a) h1
  exact want

/--
As stated:
```
not_lt (a b : Z) : ¬(a < b) ↔ b ≤ a
```
The negation of $a < b$ is $b ≤ a$.
-/
TheoremDoc not_lt as "Ord : not_lt"

/--
For all a ∈ ℤ, precisely one of the following must hold:
* a ∈ ℤ⁺ and a ≠ 0 and -a ∉ ℤ⁺
* a ∉ ℤ⁺ and a = 0 and -a ∉ ℤ⁺
* a ∉ ℤ⁺ and a ≠ 0 and -a ∈ ℤ⁺.
This is an **axiom**. Here's what it looks like in Lean:
```
trichotomy : ∀ a : Z,
    ( a ∈ Zplus ∧ a ≠ 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a = 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a ≠ 0 ∧ (-a) ∈ Zplus )
```
-/
DefinitionDoc trichotomy as "trichotomy"

/--
∀ a : Z, - -a = a
-/
TacticDoc neg_neg -- not a tactic


/--
∀ a b : Z, -a = -b ↔ a = b
-/
TacticDoc neg_eq -- not a tactic

/--
If the goal is of the form `⊢ P ∧ Q`,
```
constructor
```
will make two goals: the Active Goal will become `⊢ P` while Goal 2 becomes `⊢ Q`.
-/
TacticDoc constructor

/--
The `contradiction` tactic closes the main goal if its hypotheses are "trivially contradictory". Typically one will use this when there are two hypotheses in play like:
```
h₁ :   P
h₂ : ¬ P
```
-/
TacticDoc contradiction

/--
If our goal is of the form `⊢ P ∨ Q`, the tactic `left` will make our goal `⊢ P`.
-/
TacticDoc left

/--
If our goal is of the form `⊢ P ∨ Q`, the tactic `right` will make our goal `⊢ Q`.
-/
TacticDoc right

/-- For all $a, b ∈ ℤ$, if $a$ is not less than $b$, then $b$ is less than or equal to $a$.-/
Statement not_lt (a b : Z) : ¬(a < b) ↔ b ≤ a := by
  constructor
  Hint "The **Active Goal** is now the forward implication."
  intro h
  Hint "👉 Let's unpack `lt_def`."
  rw[lt_def] at h
  Hint "We now have that `{h} : b + -a ∉ Z⁺`. Now seems like a good time to bring the newly unlocked **trichotomy** axiom in play. 🔍 Check out the entry for `trichotomy` in the **Definitions** tab."
  obtain tri := trichotomy (b + -a)
  Hint "The hypothesis `{tri}` is a three-part disjunction whose individual parts are themselves three-part conjunctions. Use `rcases` to destructure this hypothesis appropriately."
  rcases tri with ⟨t1,_,_⟩ | ⟨_,t2,_⟩ | ⟨ _,_,t3⟩
  Hint "### 💡 Pro-tip
  Even better, we could have done this in one line using the pattern matching ability of `obtain`:
  ```
  obtain ⟨t1,_,_⟩ | ⟨_,t2,_⟩ | ⟨_,_,t3⟩ := trichotomy (b + -a)
  ```
  ⏮ Go back and give this a try. **Note:** the *underscores* utilize Lean's automatic naming conventions. These hypotheses are irrelevant in the present context, so we didn't feel the need to give them a special name. This took a little malice aforethought -- there's no harm in manually naming them all.

  ### ❯ The `contradiction` tactic
  We have contradictory hypotheses, namely
  ```
  {t1} : b + -a ∈ Z⁺
  {h} : ¬ b + -a ∈ Z⁺
  ```
  In situations like this, we can clear the goal with the tactic `contradiction`. 🔍 Check out this new tactic in the **Tactics** tab. Logically speaking, the `contradiction` tactic uses the fact that a statement like `(P ∧ ¬ P) → Q` is tautological. 👉 In our present situation, try
  ```
  contradiction
  ```
  "
  contradiction
  Hint "We cleared the first goal!
  ### ❯ Disjunctions as goals: the `left` & `right` tactics
  Our Active Goal is a disjunction, namely `⊢ b = a ∨ b < a`. Given our hypothesis `{t2}` we should be able to easily solve for the left-hand side of that disjunction. 👉 Try the tactic:
  ```
  left
  ```
  This will target the left component of our goal. 🔍 Check the new entry in the **Tactics** tab for info about `left`."
  left
  Hint "### **⟳ `simp` updated**
  We've added some functionality to `simp`. The tactic `simp` now knows the following
  ```
  @[simp] neg_neg : ∀ a : Z, - -a = a
  @[simp] neg_eq : ∀ a b : Z, -a = -b ↔ a = b
  ```
  This might be helpful going forward.
  "
  obtain aeqb := neg_unique b (-a) t2
  simp at aeqb
  symm
  exact aeqb
  Hint "Great! We've made it to the case where
  ```
  {t3}: -(b + -a) ∈ Z⁺
  ```
  Accordingly, we want to target the right-hand side of the disjunction in our goal. ***🔍 Which tactic is helpful here?***"
  right
  rw[← neg_add] at t3
  simp at t3
  rw[lt_def,add_comm]
  exact t3
  Hint "Excellent, we've proven the forward-implication. We're now trying to prove the backward implication. 💪 **Challenge:** You can finish this with no more than three tactic calls."
  intro h
  by_contra F
  exact lt_self b (le_lt_trans b a b h F)

Conclusion "
### **💡 Pro-tip**
In case you didn't figure it out, here's how to meet the 💪 **Challenge:**
```
intro h
by_contra F
exact lt_self b (le_lt_trans b a b h F)
```
### **⟳ `simp` updated**
This theorem is tagged with `@[simp]` so henceforth the tactic `simp` will replace targets like `¬ a < b` with `b ≤ a`. We've also made `simp` aware of the companion fact:
```
not_le (a b : Z) :  ¬ (a ≤ b) ↔ (b < a)
```
"

NewDefinition trichotomy
NewTactic constructor contradiction left right
NewHiddenTactic neg_neg neg_eq--hack to keep these out of the way
