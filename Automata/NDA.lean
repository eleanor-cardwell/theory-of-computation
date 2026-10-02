import Algebra.Set
import Automata.Automaton

variable {α: Type u}

/-
A nondeterministic automaton (NDA) consists of
· an alphabet, α;
· a set of states, Q;
· a transition function, δ: Q × α → 𝓟(Q);
· an initial state, q₀ ∈ Q; and
· a set of final states, F ⊆ Q.
-/
structure NDA (α: Type u) where
  State: Type v
  transition: State → α → Set State
  initial: State
  final: Set State

def NDA.run (M: NDA α) (s: Str α): Set M.State :=
  match s with
  | Str.empty => Set.singleton M.initial
  | Str.append t a => λ q ↦ ∃ p, p ∈ M.run t ∧ q ∈ M.transition p a

def NDA.language (M: NDA α): Language α :=
  λ s ↦ (M.run s ∩ M.final).Nonempty



/-
Size and finiteness of a nondeterministic automaton
-/
def NDA.size (M: NDA α): Cardinal := 
  cardinality M.State

def NDA.finite (M: NDA α): Prop :=
  Finite M.State



/-
For a given nondeterministic automaton, there is a deterministic automaton which
recognizes the same language.
-/
def NDA.toAutomaton (M: NDA α): Automaton α := {
  State := Set M.State
  transition := λ S a ↦ (λ q ↦ ∃ p ∈ S, q ∈ M.transition p a)
  initial := Set.singleton M.initial
  final := λ S ↦ (S ∩ M.final).Nonempty
}

instance (M: NDA α): Membership M.State M.toAutomaton.State := ⟨id⟩

def NDA.toAutomaton.run_eq (M: NDA α): M.run = M.toAutomaton.run := by
  funext s
  induction s with
  | empty => rfl
  | append t a ih => calc
    M.run (Str.append t a)
      = λ q ↦ ∃ p, p ∈ M.run t ∧ q ∈ M.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ M.toAutomaton.run t ∧ q ∈ M.transition p a := by rw [←ih]
    _ = M.toAutomaton.run (Str.append t a) := rfl

def NDA.toAutomaton.language_eq (M: NDA α): M.language = M.toAutomaton.language := by
  funext s
  simp
  calc
    M.language s
      ↔  M.run s ∈ M.toAutomaton.final := by rfl
    _ ↔ M.toAutomaton.run s ∈ M.toAutomaton.final := by rw [←NDA.toAutomaton.run_eq]
    _ = M.toAutomaton.language s := by rfl



/-
For a given deterministic automaton, there is (trivially) a nondeterministic
automaton which recognizes the same language.
-/
def Automaton.toNDA (M: Automaton α): NDA α := {
  State := M.State
  transition := λ q a ↦ Set.singleton (M.transition q a)
  initial := M.initial
  final := M.final
}

theorem Automaton.toNDA.run_eq (M: Automaton α) (s: Str α): M.toNDA.run s = Set.singleton (M.run s) := by
  induction s with
  | empty => rfl
  | append t a ht => calc
    -- TODO simplify with funext
    M.toNDA.run (Str.append t a)
    _ = λ q ↦ ∃ p, p ∈ M.toNDA.run t ∧ q ∈ M.toNDA.transition p a := by rfl
    _ = λ q ↦ ∃ p, p ∈ M.toNDA.run t ∧ q ∈ Set.singleton (M.transition p a) := by rfl
    _ = λ q ↦ ∃ p, p ∈ Set.singleton (M.run t) ∧ q ∈ Set.singleton (M.transition p a) := by simp_all; rfl
    _ = λ q ↦ ∃ p, p = M.run t ∧ q = M.transition p a := by rfl
    _ = λ q ↦ q = M.transition (M.run t) a := by simp
    _ = Set.singleton (M.run (Str.append t a)) := by rfl
