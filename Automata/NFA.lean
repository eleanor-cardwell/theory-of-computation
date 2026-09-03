import Automata.Set
import Automata.Automaton

structure NondeterministicAutomaton (σ: Type) where
  State: Type v
  finite: Finite State
  transition: σ → State → Set State
  initial: State
  final: Set State

abbrev NFA (σ: Type): Type 1 :=
  NondeterministicAutomaton σ

def NondeterministicAutomaton.Run {σ: Type} (M: NFA σ) (S: Str σ): Set M.State :=
  match S with
  | Str.empty => Set.Singleton M.initial
  | Str.append s S' => λ q ↦ ∃ p, p ∈ M.Run S' ∧ q ∈ M.transition s p



def NondeterministicAutomaton.toAutomaton {σ: Type} (M: NFA σ): Automaton σ := {
  State := Set M.State
  finite := Set.finite M.finite
  transition := λ s S ↦ (λ q ↦ ∃ p ∈ S, q ∈ M.transition s p)
  initial := Set.Singleton M.initial
  final := λ S ↦ (S ∩ M.final).Nonempty
}
