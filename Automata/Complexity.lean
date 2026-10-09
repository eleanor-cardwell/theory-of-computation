import Algebra.Function
import Automata.Automaton

variable {α: Type u}



/-
Every language has a recognizer.
-/
def Language.string_automaton (L: Language α): Automaton α := {
  State := Str α
  transition := Str.append
  initial := ε
  final := L
}

theorem Language.string_automaton_language_eq (L: Language α): L.string_automaton.language = L := by
  have h (s: Str α): L.string_automaton.run s = s := by
    induction s with
    | empty => rfl
    | append s a ih =>
      unfold Automaton.run
      rw [ih]
      rfl
  funext s
  unfold Automaton.language
  rw [h]
  rfl

def Language.recognizers (L: Language α): Set (Automaton α) :=
  λ M ↦ M.language = L

theorem Language.recognizers_nonempty (L: Language α): L.recognizers.Nonempty := by
  exists L.string_automaton
  exact L.string_automaton_language_eq



/-
A machine has size n when its state set is in bijection with Fin n.
The complexity of a finitely recognizable language is the least natural
number that occurs as the size of one of its recognizers.
-/
def Language.finitely_recognizable (L: Language α): Prop :=
  ∃ M: Automaton α, M.finite ∧ M.language = L

def Language.recognizer_sizes (L: Language α): Set Nat :=
  λ n ↦ ∃ M: Automaton α, ∃ h: M.finite, M.language = L ∧ (Automaton.size h).val = n

theorem Language.recognizer_sizes_nonempty {L: Language α} (h: L.finitely_recognizable): L.recognizer_sizes.Nonempty := by
  have ⟨M, hM₁, hM₂⟩ := h
  exact ⟨(Automaton.size hM₁).val, M, hM₁, hM₂, rfl⟩

private theorem nat_exists_least {S: Set Nat} (h: S.Nonempty): ∃ n ∈ S, ∀ m ∈ S, n ≤ m := by
  have ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h: ∃ m, m < n ∧ m ∈ S
    · have ⟨m, hm₁, hm₂⟩ := h
      exact ih m hm₁ hm₂
    · exists n
      constructor
      · exact hn
      · intro m hm
        apply Nat.le_of_not_gt
        intro hm₁
        exact h ⟨m, hm₁, hm⟩

noncomputable def Language.complexity (L: Language α) (h: L.finitely_recognizable): Nat :=
  Classical.choose (nat_exists_least (Language.recognizer_sizes_nonempty h))

theorem Language.complexity_le {L: Language α} (h: L.finitely_recognizable) {M: Automaton α} (hM₁: M.finite) (hM₂: M.language = L): L.complexity h ≤ (Automaton.size hM₁).val := by
  exact (Classical.choose_spec (nat_exists_least (Language.recognizer_sizes_nonempty h))).right (Automaton.size hM₁).val ⟨M, hM₁, hM₂, rfl⟩



/-
For any finitely recognizable language, a recognizer attains its complexity.
-/
theorem Language.exists_minimal_automaton (L: Language α) (h: L.finitely_recognizable): ∃ M: Automaton α, ∃ hM: M.finite, M.language = L ∧ (Automaton.size hM).val = L.complexity h := by
  exact (Classical.choose_spec (nat_exists_least (Language.recognizer_sizes_nonempty h))).left

theorem Language.finitely_recognizable_compl {L: Language α} (h: L.finitely_recognizable): Lᶜ.finitely_recognizable := by
  have ⟨M, hM₁, hM₂⟩ := h
  exists Mᶜ
  constructor
  · exact hM₁
  · rw [M.complement_language_compl, hM₂]

theorem Language.complexity_compl_le (L: Language α) (h: L.finitely_recognizable): Lᶜ.complexity (Language.finitely_recognizable_compl h) ≤ L.complexity h := by
  have ⟨M, hM₁, hM₂, hM₃⟩ := L.exists_minimal_automaton h
  rw [←hM₃]
  apply Language.complexity_le (M := Mᶜ) _ hM₁
  rw [M.complement_language_compl, hM₂]
  
theorem Language.complexity_compl_eq (L: Language α) (h: L.finitely_recognizable): Lᶜ.complexity (Language.finitely_recognizable_compl h) = L.complexity h := by
  apply Nat.le_antisymm
  · exact L.complexity_compl_le h
  · have ⟨M, hM₁, hM₂, hM₃⟩ := Lᶜ.exists_minimal_automaton (Language.finitely_recognizable_compl h)
    rw [←hM₃]
    apply Language.complexity_le (M := Mᶜ) h hM₁
    rw [M.complement_language_compl, hM₂]
    exact Set.compl_compl L
  
