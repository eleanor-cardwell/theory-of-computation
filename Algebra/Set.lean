variable {P Q R: Prop} {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

theorem contrapose: (¬Q → ¬P) → (P → Q) := by
  intro h hP
  by_cases hQ: Q
  · exact hQ
  · have := h hQ
    contradiction

theorem contrapose_iff: (¬Q ↔ ¬P) → (P ↔ Q) := by
  intro ⟨h1, h2⟩
  constructor
  · apply contrapose
    exact h1
  · apply contrapose
    exact h2

def And.associative: P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R := by
  constructor
  intro ⟨p, q, r⟩
  exact ⟨⟨p, q⟩, r⟩
  intro ⟨⟨p, q⟩, r⟩
  exact ⟨p, q, r⟩

-- type class notation for set complement Sᶜ

class Compl (X: Type u) where
  compl: X → X

postfix:max "ᶜ" => Compl.compl



/-
Sets
-/
def Set (X: Type u₁): Type u₁ :=
  X → Prop

instance (X: Type u₁): CoeSort (Set X) (Type u₁) := ⟨Subtype⟩

namespace Set

def Mem (S: Set X) (x: X): Prop :=
  S x

instance: Membership X (Set X) := ⟨Mem⟩
def Subset (A B: Set X): Prop :=
  ∀ x, A x → B x

instance: HasSubset (Set X) := ⟨Subset⟩

def empty: Set X :=
  λ _ ↦ False

instance: EmptyCollection (Set X) := ⟨empty⟩

theorem empty_subset (A: Set X): empty ⊆ A := by
  exact λ _ ↦ False.elim

def full: Set X :=
  λ _ ↦ True

theorem subset_full (A: Set X): A ⊆ full := by
  exact λ _ _ ↦ trivial

def singleton (a: X): Set X :=
  λ x ↦ x = a



/-
Set intersection
-/
def intersection (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set X) := ⟨intersection⟩

theorem inter_left {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

theorem inter_right {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right



/-
Set union
-/
def union (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: _root_.Union (Set X) := ⟨union⟩

theorem union_left {A B: Set X} {a: X} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

theorem union_right {A B: Set X} {a: X} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h



/-
Set complement and nonempty
-/
def complement (A: Set X): Set X :=
  λ x ↦ x ∉ A

instance: Compl (Set X) := ⟨complement⟩

theorem compl_compl (S: Set X): S.complement.complement = S := by
  sorry

def Nonempty (S: Set X): Prop :=
  ∃ a, a ∈ S

theorem nonempty_iff {S: Set X}: S.Nonempty ↔ S ≠ empty := by
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

theorem not_nonempty_iff {S: Set X}: ¬S.Nonempty ↔ S = empty := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff

theorem complement_empty_iff {S: Set X}: S.complement = empty ↔ S = full := by
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
      · have: x ∈ S.complement := by exact hx
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



/-
Image and range
-/
def image (f: X → Y) (S: Set X): Set Y :=
  λ y ↦ ∃ x ∈ S, f x = y

def range (f: X → Y): Set Y :=
  λ y ↦ ∃ x, f x = y

noncomputable def range_map (f: X → Y) (t: X → X) (y: Set.range f): Set.range f :=
  let x := Classical.choose y.property
  ⟨f (t x), by exists (t x)⟩

def range_mem (f: X → Y) (x: X): Set.range f :=
  ⟨f x, by exists x⟩

theorem range_mem_eq (f: X → Y) (x: X): (range_mem f x).val = f x :=
  rfl

theorem range_map_mem (f: X → Y) (t: X → X) (x: X): range_map f t (range_mem f x) = range_mem f (t x) := by
  sorry
  
  
  
/-
Useful definitions
-/
def prod (A: Set X) (B: Set Y): Set (X × Y) :=
  λ (x, y) ↦ x ∈ A ∧ y ∈ B

def inl {X: Type u} (S: Set X) {Y: Type v}: Set (X ⊕ Y) :=
  fun xy => match xy with
  | Sum.inl x => S x
  | Sum.inr _ => False

def inr {X: Type u} {Y: Type v} (S: Set Y) : Set (X ⊕ Y) :=
  fun xy => match xy with
  | Sum.inl _ => False
  | Sum.inr y => S y
  
end Set
