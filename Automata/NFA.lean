import Automata.Set
import Automata.Automaton

variable {α: Type}

structure NondeterministicAutomaton (α: Type) where
  State: Type
  finite: Finite State
  transition: α → State → Set State
  initial: State
  final: Set State

abbrev NFA (α: Type): Type 1 :=
  NondeterministicAutomaton α

def NondeterministicAutomaton.run (A: NFA α) (s: Str α): Set A.State :=
  match s with
  | Str.empty => Set.singleton A.initial
  | Str.append a t => λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition a p

def NondeterministicAutomaton.language (A: NFA α): Language α :=
  λ s ↦ (A.run s ∩ A.final).Nonempty

def NondeterministicAutomaton.toAutomaton (A: NFA α): Automaton α := {
  State := Set A.State
  finite := Set.finite A.finite
  transition := λ a S ↦ (λ q ↦ ∃ p ∈ S, q ∈ A.transition a p)
  initial := Set.singleton A.initial
  final := λ S ↦ (S ∩ A.final).Nonempty
}

instance (A: NFA α): Membership A.State A.toAutomaton.State := ⟨id⟩

def NondeterministicAutomaton.run_eq (A: NFA α): A.run = A.toAutomaton.run := by
  funext s
  induction s with
  | empty => rfl
  | append a t ih => calc
    A.run (Str.append a t)
      = λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition a p := by rfl
    _ = λ q ↦ ∃ p, p ∈ A.toAutomaton.run t ∧ q ∈ A.transition a p := by rw [←ih]
    _ = A.toAutomaton.run (Str.append a t) := rfl

def NondeterministicAutomaton.language_eq (A: NFA α): A.language = A.toAutomaton.language := by
  funext s
  simp
  calc
    A.language s
      ↔  A.run s ∈ A.toAutomaton.final := by rfl
    _ ↔ A.toAutomaton.run s ∈ A.toAutomaton.final := by rw [←NondeterministicAutomaton.run_eq]
    _ = A.toAutomaton.language s := by rfl
