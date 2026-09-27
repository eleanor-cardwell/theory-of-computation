import Algebra.Cardinal
import Automata.Language

variable {α: Type u}



/-
An automaton consists of
· an alphabet, α;
· a set of states, Q;
· a transition function; δ: Q × α → Q;
· an initial state, q₀ ∈ Q; and
· a set of final states, F ⊆ Q.
-/
structure Automaton (α: Type u) where
  State: Type u
  transition: State → α → State
  initial: State
  final: Set State
  
  

/-
For a machine M and a string s, define the resulting state after running the
string recursively
-/
def Automaton.run (M: Automaton α) (s: Str α): M.State :=
  match s with
  | ε => M.initial
  | Str.append t a => M.transition (M.run t) a



/-
The langauge of a machine is the set of strings for which the state after
running is a final state.
-/
def Automaton.language (M: Automaton α): Language α :=
  λ a ↦ M.run a ∈ M.final

theorem Automaton.language_empty_if {M: Automaton α} (h: M.final = Set.empty): M.language = Set.empty := by
  funext
  unfold Automaton.language
  rw [h]
  rfl

theorem Automaton.language_full_if {M: Automaton α} (h: M.final = Set.full): M.language = Set.full := by
  funext
  unfold Automaton.language
  rw [h]
  rfl
  
  
  
/-
Union and intersection automaton constructions

Given two machines M₁ = (α, Q₁, δ₁, q₀₁, F₁) and M₂ = (α, Q₂, δ₂, q₀₂, F₂), we
define the union automaton and intersection automaton as the machines where

· the alphabet is α;
· the state set is Q₁ × Q₂;
· the transition function is given by 
    δ((q₁, q₂), a) := (δ₁(q₁, a), δ₂(q₂, a)) 
· the initial state is (q₀₁, q₀₂)

The final state set of the union machine M₁ ∪ M₂ is

  { (q₁, q₂) ∈ Q₁ × Q₂ | q₁ ∈ F₁ ∨ q₂ ∈ F₂ }

The final state set of the intersection machine M₁ ∩ M₂ is

  { (q₁, q₂) ∈ Q₁ × Q₂ | q₁ ∈ F₁ ∧ q₂ ∈ F₂ } = F₁ × F₂
  
Notice that if M₁ recognizes L₁ and M₂ recognizes L₂, we have that M₁ ∪ M₂
recognizes L₁ ∪ L₂, and M₁ ∩ M₂ recognizes L₁ ∩ L₂.

-/
def Automaton.union (M₁ M₂: Automaton α): Automaton α := {
  State := M₁.State × M₂.State
  transition := λ (q₁, q₂) a ↦ (M₁.transition q₁ a, M₂.transition q₂ a)
  initial := (M₁.initial, M₂.initial)
  final := λ (q₁, q₂) ↦ M₁.final q₁ ∨ M₂.final q₂
}

instance: Union (Automaton α) := ⟨Automaton.union⟩

theorem Automaton.language_union (M₁ M₂: Automaton α): (M₁ ∪ M₂).language = M₁.language ∪ M₂.language := by
  sorry

def Automaton.inter (M₁ M₂: Automaton α): Automaton α := {
  State := M₁.State × M₂.State
  transition := λ (q₁, q₂) a ↦ (M₁.transition q₁ a, M₂.transition q₂ a)
  initial := (M₁.initial, M₂.initial)
  final := λ (q₁, q₂) ↦ M₁.final q₁ ∧ M₂.final q₂
}

instance: Inter (Automaton α) := ⟨Automaton.inter⟩
 
theorem Automaton.language_inter (M₁ M₂: Automaton α): (M₁ ∩ M₂).language = M₁.language ∩ M₂.language := by
  sorry




/-
Complement automaton construction

Given a machine M = (α, Q, δ, q₀, F), construct a new machine 
Mᶜ = (α, Q, δ, q₀, Fᶜ).

Notice if M recognizes language L, then Mᶜ recognizes α* \ L. 
-/
def Automaton.complement (M: Automaton α): Automaton α := {
  State := M.State
  transition := M.transition
  initial := M.initial
  final := Set.complement M.final
}

instance: Compl (Automaton α) := ⟨Automaton.complement⟩

theorem Automaton.complement_run (M: Automaton α): Mᶜ.run = M.run := by
  ext s
  induction s with
  | empty => rfl
  | append t h ih => calc
    Mᶜ.run (t + h)
      = Mᶜ.transition (Mᶜ.run t) h := by rfl
    _ = Mᶜ.transition (M.run t) h  := by rw [ih]
    _ = M.transition (M.run t) h   := by rfl
    _ = M.run (t + h) := by rfl


theorem Automaton.complement_language_compl (M: Automaton α): Mᶜ.language = (M.language)ᶜ := by
  funext s
  simp
  calc
    s ∈ (Mᶜ).language
    _ ↔ Mᶜ.run s ∈ Mᶜ.final := by rfl
    _ ↔ M.run s ∈ Mᶜ.final  := by rw [M.complement_run]
    _ ↔ M.run s ∉ M.final   := by rfl
    _ ↔ s ∉ M.language  := by rfl



/-
Size and finiteness of a machine
-/
def Automaton.size (M: Automaton α): Cardinal :=
  cardinality M.State

def Automaton.finite (M: Automaton α): Prop :=
  M.size.finite
