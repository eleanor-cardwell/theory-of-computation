import Automata.Set
import Automata.Language

variable {α: Type u}

structure DFAutomaton (α: Type u) where
  State: Type
  finite: Finite State
  transition: State → α → State
  initial: State
  final: Set State

def DFAutomaton.run (A: DFAutomaton α) (s: Str α): A.State :=
  match s with
  | Str.empty       => A.initial
  | Str.append t a => A.transition (A.run t) a

def DFAutomaton.language (A: DFAutomaton α): Language α :=
  λ s ↦ A.run s ∈ A.final

theorem language_empty_if {A: DFAutomaton α} (h: A.final = ⊥): A.language = ⊥ := by
  funext
  unfold DFAutomaton.language
  rw [h]
  rfl

theorem language_full_if {A: DFAutomaton α} (h: A.final = ⊤): A.language = ⊤ := by
  funext
  unfold DFAutomaton.language
  rw [h]
  rfl

-- TODO: define the trivial automata with 1 state and which always/never accept respectively.
-- (why? idk)

def DFAutomaton.complement (A: DFAutomaton α): DFAutomaton α := {
  State := A.State
  finite := A.finite
  transition := A.transition
  initial := A.initial
  final := Set.complement A.final
}

instance: Compl (DFAutomaton α) := ⟨DFAutomaton.complement⟩

theorem DFAutomaton.complement_run (A: DFAutomaton α): Aᶜ.run = A.run := by
  ext s
  induction s with
  | empty => rfl
  | append t h ih => calc
    Aᶜ.run (t + h)
      = Aᶜ.transition (Aᶜ.run t) h := by rfl
    _ = Aᶜ.transition (A.run t) h  := by rw [ih]
    _ = A.transition (A.run t) h   := by rfl
    _ = A.run (t + h) := by rfl


theorem DFAutomaton.complement_language_compl (A: DFAutomaton α): Aᶜ.language = (A.language)ᶜ := by
  funext s
  simp
  calc
    s ∈ (Aᶜ).language
    _ ↔ Aᶜ.run s ∈ Aᶜ.final := by rfl
    _ ↔ A.run s ∈ Aᶜ.final  := by rw [A.complement_run]
    _ ↔ A.run s ∉ A.final   := by rfl
    _ ↔ s ∉ A.language  := by rfl

def DFAutomaton.union (A₁ A₂: DFAutomaton α): DFAutomaton α := {
  State := A₁.State × A₂.State
  finite := sorry -- need the product of two finite types is finite.
  transition := fun (a₁, a₂) s => (A₁.transition a₁ s, A₂.transition a₂ s)
  initial := (A₁.initial, A₂.initial)
  final := fun (a₁, a₂) => A₁.final a₁ ∨ A₂.final a₂
}

instance: Union (DFAutomaton α) := ⟨DFAutomaton.union⟩

theorem DFAutomata.language_union (A₁ A₂: DFAutomaton α): (A₁ ∪ A₂).language = A₁.language ∪ A₂.language := by
  funext s
  match s with
  | ε => rfl
  | Str.append s t => sorry
