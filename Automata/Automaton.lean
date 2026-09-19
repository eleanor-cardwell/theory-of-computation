import Basic.Set
import Basic.Cardinal
import Automata.Language

variable {α: Type u}

structure Automaton (α: Type u) where
  State: Type u
  transition: State → α → State
  initial: State
  final: Set State

def Automaton.size (A: Automaton α): Cardinal :=
  cardinality A.State

def Automaton.finite (A: Automaton α): Prop :=
  A.size.finite

def Automaton.run (A: Automaton α) (s: Str α): A.State :=
  match s with
  | ε => A.initial
  | Str.append t a => A.transition (A.run t) a

def Automaton.language (A: Automaton α): Language α :=
  λ s ↦ A.run s ∈ A.final

theorem Automaton.language_empty_if {A: Automaton α} (h: A.final = .empty): A.language = .empty := by
  funext
  unfold Automaton.language
  rw [h]
  rfl

theorem Automaton.language_full_if {A: Automaton α} (h: A.final = .full): A.language = .full := by
  funext
  unfold Automaton.language
  rw [h]
  rfl



-- TODO: define the trivial automata with 1 state and which always/never accept respectively.
-- (why? idk)

def Automaton.complement (A: Automaton α): Automaton α := {
  State := A.State
  transition := A.transition
  initial := A.initial
  final := Set.complement A.final
}

instance: Compl (Automaton α) := ⟨Automaton.complement⟩

theorem Automaton.complement_run (A: Automaton α): Aᶜ.run = A.run := by
  ext s
  induction s with
  | empty => rfl
  | append t h ih => calc
    Aᶜ.run (t + h)
      = Aᶜ.transition (Aᶜ.run t) h := by rfl
    _ = Aᶜ.transition (A.run t) h  := by rw [ih]
    _ = A.transition (A.run t) h   := by rfl
    _ = A.run (t + h) := by rfl


theorem Automaton.complement_language_compl (A: Automaton α): Aᶜ.language = (A.language)ᶜ := by
  funext s
  simp
  calc
    s ∈ (Aᶜ).language
    _ ↔ Aᶜ.run s ∈ Aᶜ.final := by rfl
    _ ↔ A.run s ∈ Aᶜ.final  := by rw [A.complement_run]
    _ ↔ A.run s ∉ A.final   := by rfl
    _ ↔ s ∉ A.language  := by rfl

def Automaton.union (A₁ A₂: Automaton α): Automaton α := {
  State := A₁.State × A₂.State
  transition := fun (a₁, a₂) s => (A₁.transition a₁ s, A₂.transition a₂ s)
  initial := (A₁.initial, A₂.initial)
  final := fun (a₁, a₂) => A₁.final a₁ ∨ A₂.final a₂
}

instance: Union (Automaton α) := ⟨Automaton.union⟩

theorem Automaton.language_union (A₁ A₂: Automaton α): (A₁ ∪ A₂).language = A₁.language ∪ A₂.language := by
  sorry

def Automaton.inter (A₁ A₂: Automaton α): Automaton α := {
  State := A₁.State × A₂.State
  transition := fun (a₁, a₂) s => (A₁.transition a₁ s, A₂.transition a₂ s)
  initial := (A₁.initial, A₂.initial)
  final := fun (a₁, a₂) => A₁.final a₁ ∧ A₂.final a₂
}

instance: Inter (Automaton α) := ⟨Automaton.inter⟩

theorem Automaton.language_inter (A₁ A₂: Automaton α): (A₁ ∩ A₂).language = A₁.language ∩ A₂.language := by
  sorry
