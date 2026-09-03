class ExistsUnique {α: Type u} (P: α → Prop): Prop where
  exist: ∃ x, P x
  unique: ∀ x y, P x → P y → x = y

theorem contrapose {P Q: Prop}: (¬Q → ¬P) → (P → Q) := by
  intro h hP
  by_cases hQ: Q
  · exact hQ
  · have := h hQ
    contradiction

theorem contrapose_iff {P Q: Prop}: (¬Q ↔ ¬P) → (P ↔ Q) := by
  intro ⟨h1, h2⟩
  constructor
  · apply contrapose
    exact h1
  · apply contrapose
    exact h2

def And.associative (P Q R: Prop): P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R := by
  constructor
  intro ⟨p, q, r⟩
  exact ⟨⟨p, q⟩, r⟩
  intro ⟨⟨p, q⟩, r⟩
  exact ⟨p, q, r⟩

-- type class notation for ⊥ and ⊤ (bottom and top elements) in an order

class Bot (X: Type u) where
  bot: X

notation "⊥" => Bot.bot

class Top (X: Type u) where
  top: X

notation "⊤" => Top.top

-- type class notation for set complement Sᶜ

class Compl (X: Type u) where
  compl: X → X

postfix:max "ᶜ" => Compl.compl


variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

-- Set

def Set (X: Type u₁): Type u₁ :=
  X → Prop

instance (X: Type u₁): CoeSort (Set X) (Type u₁) := ⟨Subtype⟩

namespace Set

-- Membership

def Mem (A: Set X) (a: X): Prop :=
  A a

instance: Membership X (Set X) := ⟨Mem⟩

-- Subset

def Subset (A B: Set X): Prop :=
  ∀ x, A x → B x

instance: HasSubset (Set X) := ⟨Subset⟩

-- Empty set

def empty: Set X :=
  λ _ ↦ False

instance: EmptyCollection (Set X) := ⟨empty⟩

instance: Bot (Set X) := ⟨empty⟩ -- allows ⊥ notation for empty set

theorem empty_subset (A: Set X): ⊥ ⊆ A := by
  exact λ _ ↦ False.elim

-- Full set

def full: Set X :=
  λ _ ↦ True

instance: Top (Set X) := ⟨full⟩ -- allows ⊤ notation for full set

theorem subset_full (A: Set X): A ⊆ ⊤ := by
  exact λ _ _ ↦ trivial

def singleton (a: X): Set X :=
  fun x => x = a


-- Intersection

def intersection (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set X) := ⟨intersection⟩

theorem inter_left {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

theorem inter_right {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right

-- Union

def union (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: _root_.Union (Set X) := ⟨union⟩

theorem union_left {A B: Set X} {a: X} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

theorem union_right {A B: Set X} {a: X} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h

-- Complement

def complement (A: Set X): Set X :=
  λ x ↦ x ∉ A

instance: Compl (Set X) := ⟨complement⟩

-- Nonempty

def Nonempty (S: Set X): Prop :=
  ∃ a, a ∈ S

theorem nonempty_iff {S: Set X}: S.Nonempty ↔ S ≠ ⊥ := by
  constructor
  · intro ⟨a, ha⟩
    intro h
    have: a ∉ S := by exact of_eq_false (congrFun h a)
    contradiction
  · apply contrapose
    simp [Nonempty]
    intro h
    funext _
    simp
    constructor
    · intro h'
      exact h _ h'
    · intro h'
      exact False.elim h'

theorem not_nonempty_iff {S: Set X}: ¬S.Nonempty ↔ S = ⊥ := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff

theorem complement_empty_iff {S: Set X}: Sᶜ = ⊥ ↔ S = ⊤ := by
  constructor
  · intro h
    funext x
    simp
    constructor
    · intro
      trivial
    · intro _
      by_cases hx: x ∈ S
      · exact hx
      · have: x ∈ Sᶜ := by exact hx
        simp_all
        contradiction
  · intro h
    funext x
    simp
    constructor
    · intro h'
      by_cases hx: x ∈ S
      · contradiction
      · rw [h] at hx
        have: x ∈ full := by trivial
        contradiction
    · intro h'
      contradiction

end Set

structure Bijection (X: Type u) (Y: Type v) where
  map: X → Y
  inv: Y → X
  map_inv: map ∘ inv = id
  inv_map: inv ∘ map = id

def Finite (α: Type u): Prop :=
  ∃ n, _root_.Nonempty (Bijection α (Fin n))

theorem Set.finite {α: Type u} (h: Finite α): Finite (Set α) := by
  sorry
