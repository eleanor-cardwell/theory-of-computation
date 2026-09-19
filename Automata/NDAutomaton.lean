import Basic.Set
import Automata.Automaton

variable {α: Type u}

structure NDAutomaton (α: Type u) where
  State: Type u
  transition: State → α → Set State
  initial: State
  final: Set State

def NDAutomaton.size (A: NDAutomaton α): Cardinal := cardinality A.State

def NDAutomaton.finite (A: NDAutomaton α): Prop :=
  Finite A.State

def NDAutomaton.run (A: NDAutomaton α) (s: Str α): Set A.State :=
  match s with
  | Str.empty => Set.singleton A.initial
  | Str.append t a => λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition p a

def NDAutomaton.language (A: NDAutomaton α): Language α :=
  λ s ↦ (A.run s ∩ A.final).Nonempty

def NDAutomaton.toAutomaton (A: NDAutomaton α): Automaton α := {
  State := Set A.State
  transition := λ S a ↦ (λ q ↦ ∃ p ∈ S, q ∈ A.transition p a)
  initial := Set.singleton A.initial
  final := λ S ↦ (S ∩ A.final).Nonempty
}

instance (A: NDAutomaton α): Membership A.State A.toAutomaton.State := ⟨id⟩

def NDAutomaton.run_eq (A: NDAutomaton α): A.run = A.toAutomaton.run := by
  funext s
  induction s with
  | empty => rfl
  | append t a ih => calc
    A.run (Str.append t a)
      = λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ A.toAutomaton.run t ∧ q ∈ A.transition p a := by rw [←ih]
    _ = A.toAutomaton.run (Str.append t a) := rfl

def NDAutomaton.language_eq (A: NDAutomaton α): A.language = A.toAutomaton.language := by
  funext s
  simp
  calc
    A.language s
      ↔  A.run s ∈ A.toAutomaton.final := by rfl
    _ ↔ A.toAutomaton.run s ∈ A.toAutomaton.final := by rw [←NDAutomaton.run_eq]
    _ = A.toAutomaton.language s := by rfl

def Automaton.toNDAutomaton (A: Automaton α): NDAutomaton α := {
  State := A.State
  transition := fun q a => Set.singleton (A.transition q a)
  initial := A.initial
  final := A.final
}

theorem Automaton.toNDAutomaton_run (A: Automaton α) (s: Str α): A.toNDAutomaton.run s = Set.singleton (A.run s) := by
  induction s with
  | empty => rfl
  | append t a ht => calc
    A.toNDAutomaton.run (Str.append t a)
    _ = λ q ↦ ∃ p, p ∈ A.toNDAutomaton.run t ∧ q ∈ A.toNDAutomaton.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ A.toNDAutomaton.run t ∧ q ∈ Set.singleton (A.transition p a) := by rfl
    _ = λ q ↦ ∃ p, p ∈ Set.singleton (A.run t) ∧ q ∈ Set.singleton (A.transition p a) := by simp_all; rfl
    _ = λ q ↦ ∃ p, p = A.run t ∧ q = A.transition p a := by rfl
    _ = λ q ↦ q = A.transition (A.run t) a := by simp
    _ = Set.singleton (A.run (Str.append t a)) := by rfl
