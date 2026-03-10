import GameServer

/-
Custom Set structure
-/

structure Set (α : Type) where
  mem : α → Prop

instance {α : Type} : Membership α (Set α) where
  mem S x := S.mem x

syntax "{ " ident " : " term " | " term " }" : term

macro_rules
  | `({ $x:ident : $α | $P }) =>
      `(Set.mk (fun $x : $α => $P))

syntax "{ " term " | " ident " ∈ " term " }" : term --this doesn't work well

macro_rules
  | `({ $e | $x:ident ∈ $S }) =>
      `(Set.mk (fun y => Exists (fun $x => $x ∈ $S ∧ y = $e)))

def Set.subset {α : Type} (A B : Set α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B
notation:50 A " ⊆ " B => Set.subset A B

def Set.notsubset {α : Type} (A B : Set α) : Prop :=
  ∃ x : α, x ∈ A ∧ x ∉ B
notation:50 A " ⊈ " B => Set.notsubset A B

def Set.nonempty {α : Type} (A : Set α) : Prop :=
  ∃ x, x ∈ A
notation A " ≠∅" => Set.nonempty A

def Set.empty {α : Type} (A : Set α) : Prop :=
  ¬ (∃ x, x ∈ A)
notation:50 A " =∅" => Set.empty A

@[simp]
theorem nonempty_iff_not_empty {α : Type} (S : Set α) :
  ¬ (S =∅) ↔ S ≠∅ :=
by
  unfold Set.nonempty Set.empty
  simp

@[simp]
theorem not_nonempty_iff_not_empty {α : Type} (S : Set α) :
  ¬ (S ≠∅) ↔ S =∅ :=
by
  unfold Set.nonempty Set.empty
  simp

@[simp]
theorem notcontained_iff_not_subset {α : Type} (A B : Set α) :
  ¬ (A ⊆ B) ↔ A ⊈ B := by
  unfold Set.subset Set.notsubset
  simp

@[simp]
theorem not_notcontained_iff_subset {α : Type} (A B : Set α) :
  ¬ (A ⊈ B) ↔ A ⊆ B := by
  unfold Set.subset Set.notsubset
  simp

theorem mem_def {α : Type} (S : Set α) (x : α) :
  x ∈ S ↔ S.mem x :=
Iff.rfl

open Lean PrettyPrinter Delaborator SubExpr Meta

@[delab app.Set.mk]
def delabSetMk : Delab := do
  let e ← SubExpr.getExpr
  match e with
  | Expr.app (Expr.app _ α) f =>
      match f with
      | Expr.lam n ty body _bi =>
          let tyStx ← delab ty
          let xId := mkIdent n
          let bodyStx ← withLocalDecl n BinderInfo.default ty fun xLocal =>
            delab (body.instantiate1 xLocal)
          `({ $xId : $tyStx | $bodyStx })
      | _ => failure
  | _ => failure

/- Definition of ℤ -/

class RossRing Z : Type extends Zero Z, One Z, Add Z, Mul Z, Neg Z where
  add_comm : ∀ a b : Z, a + b = b + a
  mul_comm : ∀ a b : Z, a * b = b * a
  add_assoc : ∀ a b c : Z, a + b + c = a + (b + c)
  mul_assoc : ∀ a b c : Z, a * b * c = a * (b * c)
  mul_add : ∀ a b c : Z, a * (b + c) = a * b + a * c
  add_zero : ∀ a : Z, a + 0 = a
  add_neg_self : ∀ a : Z, a + -a = 0
  mul_one : ∀ a : Z, a * 1 = a
  Zplus : Set Z
  pos_nonempty: ∃ a : Z, a ∈ Zplus
  add_closure : ∀ a b : Z, a ∈ Zplus →  b ∈ Zplus → (a + b) ∈ Zplus
  mul_closure : ∀ a b : Z, a ∈ Zplus →  b ∈ Zplus → (a * b) ∈ Zplus
  non_trivial : 0 ∉ Zplus
  trichotomy  : ∀ a : Z,
    ( a ∈ Zplus ∧ a ≠ 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a = 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a ≠ 0 ∧ (-a) ∈ Zplus )
  WOP : ∀ S : Set Z,
    (S ≠∅ ) →
    (S ⊆ Zplus) →
    ∃ m, m ∈ S ∧ ∀ x, x ∈ S → (m = x ∨ x + -m ∈ Zplus)

variable {Z : Type} [RRZ : RossRing Z]

def Zplus {Z : Type} [RossRing Z] : Set Z :=
  RossRing.Zplus
notation "Z⁺" => Zplus

/- Axioms wrapped in theorems for use in Lean4Game -/

theorem add_comm : ∀ a b : Z, a + b = b + a := by
  intro a b
  rw[RossRing.add_comm]

theorem mul_comm : ∀ a b : Z, a * b = b * a := by
  intro a b
  rw[RossRing.mul_comm]

@[simp] theorem add_zero : ∀ a : Z, a + 0 = a := by
  intro a
  rw[RossRing.add_zero]

@[simp] theorem mul_one : ∀ a : Z, a * 1 = a := by
  intro a
  rw[RossRing.mul_one]

@[simp] theorem add_neg_self : ∀ a : Z, a + -a = 0 := by
  intro a
  rw[RossRing.add_neg_self]

theorem add_assoc : ∀ a b c : Z, a + b + c = a + (b + c) := by
  intro a b c
  rw[RossRing.add_assoc]

theorem mul_assoc : ∀ a b c : Z, a * b * c = a * (b * c) := by
  intro a b c
  rw[RossRing.mul_assoc]

theorem mul_add : ∀ a b c : Z, a * (b + c) = a * b + a * c := by
  intro a b c
  rw[RossRing.mul_add]

instance : LT Z :=
  ⟨ fun a b => b + -a ∈ Zplus ⟩

theorem lt_def (a b : Z): a < b ↔ (b + -a) ∈ Zplus := Iff.rfl

instance : LE Z :=
  ⟨fun a b => a = b ∨ a < b⟩

theorem le_def (a b :Z ) : a ≤ b ↔ (a = b ∨ a < b) := Iff.rfl

instance : Dvd Z :=
  ⟨fun a b => ∃ c : Z, b = a * c⟩

theorem dvd_def (a b : Z) : a ∣ b ↔ ∃ c : Z, b = a * c := Iff.rfl

theorem add_closure :  ∀ a b : Z, a ∈ Zplus → b ∈ Zplus → (a + b) ∈ Zplus := by
  intro a b ha hb
  exact RossRing.add_closure a b ha hb

theorem trichotomy : ∀ a : Z,
    ( a ∈ Zplus ∧ a ≠ 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a = 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a ≠ 0 ∧ (-a) ∈ Zplus ) := by
  intro a
  exact RossRing.trichotomy a

theorem non_trivial : (0 : Z) ∉ Zplus := by
  exact RossRing.non_trivial

theorem pos_nonempty :  ∃ x : Z, x ∈ Zplus := by
  exact RossRing.pos_nonempty

theorem mul_closure : ∀ a b : Z, a ∈ Zplus →  b ∈ Zplus → (a * b) ∈ Zplus := by
  intro a b ha hb
  exact RossRing.mul_closure a b ha hb

theorem WOP : ∀ S : Set Z, (S ≠∅ ) → (S ⊆ Zplus) → ∃ m, m ∈ S ∧ ∀ x, x ∈ S → m ≤ x := by
  exact RossRing.WOP

/- Custom tactics -/

open Lean Elab Tactic

syntax "define " ident " := " term : tactic

macro_rules
  | `(tactic| define $x := $t) =>
      `(tactic| let $x := $t)

syntax "use " term : tactic

macro_rules
  | `(tactic| use $w) =>
      `(tactic| refine Exists.intro $w ?_)

-- consume
syntax "by_wop " term " with " ident rcasesPat ident : tactic

elab_rules : tactic
| `(tactic| by_wop $S with $m $pat $hmin) => do
      let hne := Lean.mkIdent `hne
      let hpo := Lean.mkIdent `hpo
      evalTactic (← `(tactic|
        have $hne : $S ≠∅ := ?nem
      ))
      evalTactic (← `(tactic|
        have $hpo : $S ⊆ Zplus := ?pos
      ))
      evalTactic (← `(tactic|
        obtain ⟨$m, ⟨ $pat, $hmin⟩⟩ := WOP $S $hne $hpo
      ))

-- keep (auto name)
syntax "by_wop! " term " with " ident rcasesPat ident : tactic

elab_rules : tactic
| `(tactic| by_wop! $S with $m $pat $hmin) => do
      let hne  := mkIdent `hne
      let hpo  := mkIdent `hpo
      let hmem := mkIdent `hmem
      evalTactic (← `(tactic|
        have $hne : $S ≠∅ := ?nem
      ))
      evalTactic (← `(tactic|
        have $hpo : $S ⊆ Zplus := ?pos
      ))
      evalTactic (← `(tactic|
        have ⟨$m, ⟨ $hmem, $hmin⟩⟩ := WOP $S $hne $hpo;
        rcases _ : $hmem with $pat
      ))

axiom POW_tactic : --so we don't need to prove pow to define the tactic
  (S : Set Z) →
  S ≠∅ →
  (∃ u : Z, ∀ x ∈ S, x ≤ u) →
  ∃ M ∈ S, ∀ x ∈ S, x ≤ M

-- consume
syntax "by_pow " term " with " ident rcasesPat ident : tactic

-- keep (auto name)
syntax "by_pow " term " with " ident " keep " rcasesPat ident : tactic

elab_rules : tactic
  | `(tactic| by_pow $S with $m $pat $hmax) => do
      let hne := Lean.mkIdent `hne
      let hbd := Lean.mkIdent `hbd
      evalTactic (← `(tactic|
        have $hne : $S ≠∅ := ?nem
      ))
      evalTactic (← `(tactic|
        have $hbd : ∃ u : $(mkIdent `Z), ∀ x, x ∈ $S → x ≤ u := ?bdd
      ))
      evalTactic (← `(tactic|
        obtain ⟨$m, ⟨ $pat, $hmax⟩⟩ := POW_tactic $S $hne $hbd
      ))
  | `(tactic| by_pow $S with $m keep $pat $hmax) => do
      let hne  := mkIdent `hne
      let hbd  := mkIdent `hbd
      let hmem := mkIdent `hmem
      evalTactic (← `(tactic|
        have $hne : $S ≠∅ := ?nem
      ))
      evalTactic (← `(tactic|
        have $hbd : ∃ u : $(mkIdent `Z), ∀ x, x ∈ $S → x ≤ u := ?bdd
      ))
      evalTactic (← `(tactic|
        have ⟨$m, ⟨ $hmem, $hmax⟩⟩ := POW_tactic $S $hne $hbd;
        rcases _ : $hmem with $pat
      ))

syntax "by_contra" (ppSpace binderIdent)? : tactic

macro_rules
  | `(tactic| by_contra $h:binderIdent) =>
      `(tactic| false_or_by_contra; rename _ => F; rename_i $h:binderIdent) --hack
  | `(tactic| by_contra) =>
      `(tactic| false_or_by_contra; rename _ => F) --hack

syntax "by_contra!" (ppSpace ident)? : tactic

macro_rules
  | `(tactic| by_contra! $h) =>
      `(tactic| by_contra $h:ident; simp at $h:ident)

  | `(tactic| by_contra!) =>
      `(tactic| by_contra; simp at F)

/- Invisible theorems tagged with simp to keep clutter at a minimum -/

@[simp] theorem neg_self_add : ∀ a : Z, -a + a = 0 := by
  intro a
  rw[add_comm,add_neg_self]

@[simp] theorem neg_zero : (-0 : Z) = 0 := by
  obtain h := RossRing.add_neg_self (0 : Z)
  rw[RossRing.add_comm,RossRing.add_zero] at h
  exact h

@[simp] theorem one_mul : ∀ a : Z, 1 * a = a := by
  intro a
  rw[RossRing.mul_comm,RossRing.mul_one]

/- Custome structures and defintions -/

def Prime (p : Z) : Prop :=
  1 < p ∧ (∀ d : Z, 0 < d → d ∣ p → (d = 1 ∨ d = p))

def List.prod : List Z → Z
| []             => (1:Z) --The product of the empty list is the empty product: 1.
| (head :: tail) => head * tail.prod

def List.prime (S : List Z) := ∀ s ∈ S, Prime s

noncomputable def abs (a : Z) : Z := by
  classical
  by_cases h : a < 0
  · exact -a
  · exact a

structure GCD (a b : Z) where
  (g : Z)
  (left : g ∣ a )
  (right : g ∣ b)
  (le : ¬ (a = 0 ∧ b = 0) → ∀ d : Z, (d ∣ a →  d ∣ b → d ≤ g ))

structure DivAlg (a b : Z) (hb : b ≠ 0) where
  (q : Z)
  (r : Z)
  (eq : a = b * q + r)
  (nonneg : 0 ≤ r)
  (lt : r < abs b)
