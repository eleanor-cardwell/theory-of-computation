import Algebra.Set
import Algebra.Monoid

variable {α: Type u} {β: Type v}



/-
A string is either the empty string, or consists of a string and an appended 
symbol.
-/
inductive Str (α: Type u) where
| empty: Str α
| append: Str α → α → Str α

namespace Str

  
  
/-
Basic notation
-/
instance: HAdd (Str α) α (Str α) := {
  hAdd := append
}

theorem append_eq (s: Str α) (a: α): s + a = append s a := by
  rfl

notation "ε" => empty

theorem empty_eq: (ε: Str α) = empty := by
  rfl

def singleton (a: α): Str α :=
 append empty a
 
 
 
/-
Prepend a symbol to a string
-/
def prepend (a: α) (s: Str α): Str α :=
  match s with
  | empty => singleton a
  | append t h => append (prepend a t) h
  
instance: HAdd α (Str α) (Str α) := {
  hAdd := prepend
}

theorem prepend_eq (a: α) (s: Str α): a + s = prepend a s := by
  rfl



/-
Concatenate two strings
-/
def concat (s₁ s₂: Str α): Str α :=
 match s₂ with
 | empty => s₁
 | append t a => append (concat s₁ t) a
 
instance: Add (Str α) := {
  add := concat
}

theorem concat_eq (s₁ s₂: Str α): s₁ + s₂ = concat s₁ s₂ := by
  rfl

theorem concat_empty_right (s: Str α): s + ε = s := by
  rfl

theorem concat_empty_left (s: Str α): ε + s = s := by
  induction s with
  | empty => rfl
  | append h t ih => 
    have h₁: ε + (append h t) = append (ε + h) t := by rfl
    rw [h₁, ih]
    
theorem concat_assoc (s₁ s₂ s₃: Str α): s₁ + (s₂ + s₃) = (s₁ + s₂) + s₃ := by
  induction s₃ with
  | empty => rfl
  | append s₃ a ih =>
    apply congrArg (λ s ↦ append s a) ih



/-
Reverse a string
-/
def reverse (s: Str α): Str α :=
  match s with
  | empty => empty
  | append t a => prepend a (reverse t)
  
instance: Inv (Str α) := ⟨reverse⟩

theorem reverse_eq (s: Str α): s⁻¹ = reverse s := by
  rfl
    
theorem reverse_empty: (ε: Str α)⁻¹ = ε := by
  rfl

theorem prepend_concat (a₁: α) (s₁ s₂: Str α): a₁ + (s₁ + s₂) = (a₁ + s₁) + s₂ := by
  induction s₂ with
  | empty => rfl
  | append s₂ a₂ ih =>
    apply congrArg (λ s ↦ append s a₂) ih

theorem inv_concat (s₁ s₂: Str α): (s₁ + s₂)⁻¹ = s₂⁻¹ + s₁⁻¹ := by
  induction s₂ with
  | empty => 
    rw [reverse_empty, concat_empty_left, concat_empty_right]
  | append t a ih =>
    calc
      (s₁ + (t + a))⁻¹
      _ = ((s₁ + t) + a)⁻¹ := by rfl
      _ = a + (s₁ + t)⁻¹   := by rfl
      _ = a + (t⁻¹ + s₁⁻¹) := by rw [ih]
      _ = (a + t⁻¹) + s₁⁻¹ := by rw [prepend_concat]
      _ = (t + a)⁻¹ + s₁⁻¹ := by rfl

theorem inv_prepend (a₁: α) (s: Str α): (a₁ + s)⁻¹ = s⁻¹ + a₁ := by
  induction s with
  | empty => rfl
  | append s a₂ ih =>
    rw [prepend_eq, prepend, reverse_eq, reverse, ←reverse_eq, ←prepend_eq a₁ s, ih]
    rfl

theorem inv_inv (s: Str α): s⁻¹⁻¹ = s := by
  induction s with
  | empty => rfl
  | append t a ih => 
    rw [reverse_eq]
    calc
      (t + a)⁻¹⁻¹
      _ = (a + t⁻¹)⁻¹ := by rfl
      _ = t + a := by rw [inv_prepend, ih]



/-
Length of a string
-/
def length (s: Str α): Nat :=
 match s with
 | empty => 0
 | append t _ => t.length + 1

theorem length_prepend (a: α) (s: Str α): length (a + s) = 1 + length s := by
  induction s with
  | empty => rfl
  | append s a₁ ih =>
    rw [prepend_eq, prepend, length, ←prepend_eq, ih, length, Nat.add_assoc]

theorem length_concat (s t: Str α): length (s + t) = length s + length t := by
  induction t with
  | empty => rfl
  | append t a ih =>
    rw [concat_eq, concat, length, ←concat_eq, ih, length, Nat.add_assoc]

theorem length_reverse (s: Str α): length s⁻¹ = length s := by
  induction s with
  | empty => rfl
  | append s a ih =>
    rw [reverse_eq, reverse, ←prepend_eq, length_prepend, ←reverse_eq, ih, length, Nat.add_comm]
 
 
 
/-
Flatten a string of strings
-/
def flatten (s: Str (Str α)): Str α :=
  match s with
  | empty => empty
  | append t h => concat (flatten t) h



/-
"Lift" a map α → β to a new map Str α → Str β
-/
def map (f: α → β) (s: Str α): Str β :=
  match s with
  | empty => empty
  | append t h => map f t + f h



/-
We can form a monoid on strings on any type
-/
instance (α: Type u): Monoid (Str α) where
  zero := ε
  assoc := by
    intro s₁ s₂ s₃
    exact Eq.symm (concat_assoc s₁ s₂ s₃)
  unit_left := concat_empty_left
  unit_right := concat_empty_right

  

/-
We can put an order on strings using the "prefix" relation
-/
def is_prefix (s t: Str α): Prop :=
  ∃ u: Str α, s + u = t

instance: LE (Str α) := {
  le := is_prefix
}



/-
todo: 
· prefix is reflexive/transitive/antisymmetric
· s ≤ t implies length(s) ≤ length(t)
-/


/-
Symbol -> Singleton coercion
(Keep at bottom of file or it messes with some earlier theorems)
-/
 
instance: Coe α (Str α) := {
  coe := singleton
}
