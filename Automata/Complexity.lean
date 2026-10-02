import Algebra.Cardinal
import Automata.Automaton

variable {α: Type u}

/-
Using well-orderedness of the cadinals, we can definie the complexity of a
language as the cardinality of the least element in the set of machines which
recognize that language.
-/
def Language.string_automaton (L: Language α): Automaton α := {
  State := Str α
  transition := Str.append
  initial := ε
  final := L
}

theorem Language.string_automaton_language_eq (L: Language α): L.string_automaton.language = L := by
  sorry

def Language.recognizers (L: Language α): Set (Automaton α) :=
  λ A ↦ A.language = L

theorem Language.recognizers_nonempty (L: Language α): L.recognizers.Nonempty := by
  exists L.string_automaton
  exact L.string_automaton_language_eq

def Language.recognizer_sizes (L: Language α): Set Cardinal :=
  Set.image Automaton.size L.recognizers

def Language.recognizer_sizes_nonempty (L: Language α): L.recognizer_sizes.Nonempty :=
  sorry

noncomputable def Language.complexity (L: Language α): Cardinal :=
  Classical.choose (Cardinal.well_ordered _ L.recognizer_sizes_nonempty)

theorem Language.complexity_le {L: Language α} {A: Automaton α} (h: A.language = L): L.complexity ≤ A.size := by
  sorry



/-
For any language, we can find an automaton recognizing that language with size
equal to that language's complexity.
-/
theorem Language.exists_minimal_automaton (L: Language α): ∃ A: Automaton α, A.language = L ∧ A.size = L.complexity := by
  sorry

theorem Language.complexity_compl_le (L: Language α): Lᶜ.complexity ≤ L.complexity := by
  have ⟨A, hA₁, hA₂⟩ := L.exists_minimal_automaton
  have := Language.complexity_le A.complement_language_compl
  rw [←hA₂, ←hA₁]
  exact this
  
theorem Language.complexity_compl_eq (L: Language α): Lᶜ.complexity = L.complexity := by
  apply Cardinal.le_antisymm
  exact L.complexity_compl_le
  have: L.complexity = Lᶜᶜ.complexity := by rw [Set.compl_compl L]
  rw [this]
  apply Lᶜ.complexity_compl_le
  
