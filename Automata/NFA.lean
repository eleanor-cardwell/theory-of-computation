import Automata.Set
import Automata.DFA

variable {α: Type u}

structure NFAutomaton (α: Type u) where
  State: Type
  finite: Finite State
  transition: State → α → Set State
  initial: State
  final: Set State

abbrev NFA (α: Type u): Type (max u 1) :=
  NFAutomaton α

def NFAutomaton.run (A: NFA α) (s: Str α): Set A.State :=
  match s with
  | Str.empty => Set.singleton A.initial
  | Str.append t a => λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition p a

def NFAutomaton.language (A: NFA α): Language α :=
  λ s ↦ (A.run s ∩ A.final).Nonempty

def NFAutomaton.toAutomaton (A: NFA α): DFAutomaton α := {
  State := Set A.State
  finite := Set.finite A.finite
  transition := λ S a ↦ (λ q ↦ ∃ p ∈ S, q ∈ A.transition p a)
  initial := Set.singleton A.initial
  final := λ S ↦ (S ∩ A.final).Nonempty
}

instance (A: NFA α): Membership A.State A.toAutomaton.State := ⟨id⟩

def NFAutomaton.run_eq (A: NFA α): A.run = A.toAutomaton.run := by
  funext s
  induction s with
  | empty => rfl
  | append t a ih => calc
    A.run (Str.append t a)
      = λ q ↦ ∃ p, p ∈ A.run t ∧ q ∈ A.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ A.toAutomaton.run t ∧ q ∈ A.transition p a := by rw [←ih]
    _ = A.toAutomaton.run (Str.append t a) := rfl

def NFAutomaton.language_eq (A: NFA α): A.language = A.toAutomaton.language := by
  funext s
  simp
  calc
    A.language s
      ↔  A.run s ∈ A.toAutomaton.final := by rfl
    _ ↔ A.toAutomaton.run s ∈ A.toAutomaton.final := by rw [←NFAutomaton.run_eq]
    _ = A.toAutomaton.language s := by rfl

def DFAutomaton.toNFAutomaton (A: DFAutomaton α): NFAutomaton α := {
  State := A.State
  finite := A.finite
  transition := fun q a => Set.singleton (A.transition q a)
  initial := A.initial
  final := A.final
}

theorem Automaton.toNFAutomaton_run (A: DFAutomaton α) (s: Str α): A.toNFAutomaton.run s = Set.singleton (A.run s) := by
  induction s with
  | empty => rfl
  | append t a ht => calc
    A.toNFAutomaton.run (Str.append t a)
    _ = λ q ↦ ∃ p, p ∈ A.toNFAutomaton.run t ∧ q ∈ A.toNFAutomaton.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ A.toNFAutomaton.run t ∧ q ∈ Set.singleton (A.transition p a) := by rfl
    _ = λ q ↦ ∃ p, p ∈ Set.singleton (A.run t) ∧ q ∈ Set.singleton (A.transition p a) := by simp_all; rfl
    _ = λ q ↦ ∃ p, p = A.run t ∧ q = A.transition p a := by rfl
    _ = λ q ↦ q = A.transition (A.run t) a := by simp
    _ = Set.singleton (A.run (Str.append t a)) := by rfl
