
import Automata.RegularLanguage
import Automata.Automaton

variable {α: Type u}

def Automaton.union (A₁ A₂: Automaton α): Automaton α := {
  State := A₁.State × A₂.State
  finite := sorry -- need the product of two finite types is finite.
  transition := fun s (a₁, a₂) => (A₁.transition s a₁, A₂.transition s a₂)
  initial := (A₁.initial, A₂.initial)
  final := fun (a₁, a₂) => A₁.final a₁ ∨ A₂.final a₂
}

instance: Union (Automaton α) := ⟨Automaton.union⟩

theorem Automata.language_union (A₁ A₂: Automaton α): (A₁ ∪ A₂).language = A₁.language ∪ A₂.language := by
  funext S
  match S with
  | ε => rfl
  | Str.append s t => sorry

-- TODO: state similar theorems for intersection
-- TODO: move this to automaton.lean?
