
import Automata.RegularLanguage
import Automata.Automaton

variable {σ: Type u}

def Automaton.union (A₁ A₂: Automaton σ): Automaton σ := {
  State := A₁.State × A₂.State
  finite := sorry -- need the product of two finite types is finite.
  transition := fun s (a₁, a₂) => (A₁.transition s a₁, A₂.transition s a₂)
  initial := (A₁.initial, A₂.initial)
  final := fun (a₁, a₂) => A₁.final a₁ ∨ A₂.final a₂
}

instance: Union (Automaton σ) := ⟨Automaton.union⟩

theorem Automata.language_union (A₁ A₂: Automaton σ): (A₁ ∪ A₂).Language = A₁.Language ∪ A₂.Language := by
  funext S
  match S with
  | ε => rfl
  | Str.append s t => sorry

-- TODO: state similar theorems for intersection
-- TODO: move this to automaton.lean?
