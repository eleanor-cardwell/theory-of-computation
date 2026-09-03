import Automata.Set
import Automata.Automaton

structure NondeterministicAutomaton (α: Type) where
  State: Type
  finite: Finite State
  transition: α → State → Set State
  initial: State
  final: Set State

abbrev NFA (α: Type): Type 1 :=
  NondeterministicAutomaton α

def NondeterministicAutomaton.Run {α: Type} (A: NFA α) (S: Str α): Set A.State :=
  match S with
  | Str.empty => Set.singleton A.initial
  | Str.append s S' => λ q ↦ ∃ p, p ∈ A.Run S' ∧ q ∈ A.transition s p


def NondeterministicAutomaton.toAutomaton {α: Type} (A: NFA α): Automaton α := {
  State := Set A.State
  finite := Set.finite A.finite
  transition := λ s S ↦ (λ q ↦ ∃ p ∈ S, q ∈ A.transition s p)
  initial := Set.singleton A.initial
  final := λ S ↦ (S ∩ A.final).Nonempty
}
