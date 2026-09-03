import Automata.Set
import Automata.language

variable {α: Type u}

structure Automaton (α: Type u) where
  State: Type
  finite: Finite State
  transition: α → State → State
  initial: State
  final: Set State

def Automaton.run (A: Automaton α) (S: Str α): A.State :=
  match S with
  | Str.empty       => A.initial
  | Str.append s S' => A.transition s (A.run S')

instance: CoeFun (Automaton α) (fun A => Str α → A.State) := ⟨Automaton.run⟩

def Automaton.language (A: Automaton α): Language α :=
  λ S ↦ A.run S ∈ A.final

theorem language_empty_if {A: Automaton α} (h: A.final = ⊥): A.language = ⊥ := by
  funext
  unfold Automaton.language
  rw [h]
  rfl

theorem language_full_if {A: Automaton α} (h: A.final = ⊤): A.language = ⊤ := by
  funext
  unfold Automaton.language
  rw [h]
  rfl

-- TODO: define the trivial automata with 1 state and which always/never accept respectively.
-- (why? idk)

def Automaton.complement (A: Automaton α): Automaton α := {
  State := A.State
  finite := A.finite
  transition := A.transition
  initial := A.initial
  final := Set.complement A.final
}

instance: Compl (Automaton α) := ⟨Automaton.complement⟩

theorem Automaton.complement_run (A: Automaton α): Aᶜ.run = A.run := by
  ext s
  induction s with
  | empty => rfl
  | append h t ih => calc
    Aᶜ.run (h + t)
      = Aᶜ.transition h (Aᶜ t) := by rfl
    _ = Aᶜ.transition h (A t)  := by rw [ih]
    _ = A.transition h (A t)   := by rfl
    _ = A (h + t) := by rfl


theorem Automaton.complement_language_compl (A: Automaton α): Aᶜ.language = (A.language)ᶜ := by
  funext s
  simp
  calc
    s ∈ (Aᶜ).language
    _ ↔ Aᶜ s ∈ Aᶜ.final := by rfl
    _ ↔ A s ∈ Aᶜ.final  := by rw [A.complement_run]
    _ ↔ A s ∉ A.final   := by rfl
    _ ↔ s ∉ A.language  := by rfl
