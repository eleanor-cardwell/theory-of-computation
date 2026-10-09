import Automata.RegularExpression
import Automata.NDA

open Classical



/-
NDA recognizing the empty language
-/
def NDA.empty (α: Type u): NDA α := {
  State := Fin 1
  transition := λ _ _ ↦ Set.singleton 0
  initial := 0
  final := Set.empty
}

theorem empty_finite {α: Type u}: Finite (NDA.empty α).State := by
  exact fin_finite 1
  
theorem empty_language_eq {α: Type u}: (NDA.empty α).language = ∅ := by
  apply Set.ext
  intro s
  constructor
  · intro h
    unfold NDA.language at h
    have ⟨_, _, hq⟩ := h
    exact hq
  · intro h
    exact False.elim h



/-
NDA recognizing the singleton language
-/
def NDA.singleton {α: Type u} [DecidableEq α] (a₀: α): NDA α := {
  State := Fin 2
  transition := λ q a q' ↦ q = 0 ∧ a = a₀ ∧ q' = 1
  initial := 0
  final := Set.singleton 1
}

theorem singleton_finite {α: Type u} (a₀: α): Finite (NDA.singleton a₀).State := by
  exact fin_finite 2
  
theorem singleton_language_eq {α: Type u} (a₀: α): (NDA.singleton a₀).language = Set.singleton (Str.singleton a₀) := by
  apply Set.ext
  intro s
  constructor
  · intro h
    unfold Set.singleton
    unfold NDA.language at h
    have ⟨q, hq₁, hq₂⟩ := h
    clear h
    cases s with
    | empty =>
      have h: (0: Fin 2) = 1 := Eq.trans (Eq.symm hq₁) hq₂
      cases congrArg Fin.val h
    | append s₁ a₁ =>
      have ⟨q₁, hq₁, hq₀, ha, _⟩ := hq₁
      cases s₁ with
      | empty =>
        rw [ha]
        rfl
      | append s₂ a₂ =>
        have ⟨q₂, _, _, _, hq₂⟩ := hq₁
        have h: (0: Fin 2) = 1 := Eq.trans (Eq.symm hq₀) hq₂
        cases congrArg Fin.val h
  · intro h
    unfold Set.singleton at h
    subst s
    exists (1: Fin 2)
    constructor
    · exists (0: Fin 2)
    · rfl



/-
For two NDA recognizing languages L₁ and L₂, define an NDA which recognizes
L₁ ∪ L₂
-/
def NDA.union {α: Type u} (M₁ M₂: NDA α): NDA α := {
  State := Option (M₁.State ⊕ M₂.State)
  transition := λ q a q' ↦
    match q, q' with
    | none, some (Sum.inl q') => q' ∈ M₁.transition M₁.initial a
    | none, some (Sum.inr q') => q' ∈ M₂.transition M₂.initial a
    | some (Sum.inl q), some (Sum.inl q') => q' ∈ M₁.transition q a
    | some (Sum.inr q), some (Sum.inr q') => q' ∈ M₂.transition q a
    | _, _ => False
  initial := none
  final := λ q ↦
    match q with
    | none => M₁.initial ∈ M₁.final ∨ M₂.initial ∈ M₂.final
    | some (Sum.inl q) => q ∈ M₁.final
    | some (Sum.inr q) => q ∈ M₂.final
}

theorem union_finite {α: Type u} {M₁ M₂: NDA α} (h₁: Finite M₁.State) (h₂: Finite M₂.State): Finite (NDA.union M₁ M₂).State := by
  sorry
  
theorem union_run_mem {α: Type u} (M₁ M₂: NDA α): ∀ (s: Str α) (a: α) (q: (NDA.union M₁ M₂).State), q ∈ (NDA.union M₁ M₂).run (Str.append s a) ↔ match q with
    | none => False
    | some (Sum.inl q) => q ∈ M₁.run (Str.append s a)
    | some (Sum.inr q) => q ∈ M₂.run (Str.append s a) := by
  intro s
  induction s with
  | empty =>
    intro a q
    rw [←Str.singleton, NDA.run_singleton]
    cases q with
    | none => rfl
    | some q =>
      cases q with
      | inl q =>
        rw [NDA.run_singleton M₁]
        rfl
      | inr q =>
        rw [NDA.run_singleton M₂]
        rfl
  | append s a₁ ih =>
    intro a₂ q
    cases q with
    | none =>
      constructor
      · intro ⟨p, _, ht⟩
        cases p with
        | none => exact ht
        | some p => cases p <;> exact ht
      · intro h
        exact False.elim h
    | some q =>
      cases q with
      | inl q =>
        constructor
        · intro ⟨p, hp, ht⟩
          cases p with
          | none => exact False.elim ((ih a₁ none).mp hp)
          | some p =>
            cases p with
            | inl p => exact ⟨p, (ih a₁ (some (Sum.inl p))).mp hp, ht⟩
            | inr p => exact False.elim ht
        · intro ⟨p, hp, ht⟩
          exact ⟨some (Sum.inl p), (ih a₁ (some (Sum.inl p))).mpr hp, ht⟩
      | inr q =>
        constructor
        · intro ⟨p, hp, ht⟩
          cases p with
          | none => exact False.elim ((ih a₁ none).mp hp)
          | some p =>
            cases p with
            | inr p => exact ⟨p, (ih a₁ (some (Sum.inr p))).mp hp, ht⟩
            | inl p => exact False.elim ht
        · intro ⟨p, hp, ht⟩
          exact ⟨some (Sum.inr p), (ih a₁ (some (Sum.inr p))).mpr hp, ht⟩



theorem union_language_eq {α: Type u} (M₁ M₂: NDA α): (NDA.union M₁ M₂).language = M₁.language ∪ M₂.language := by
  apply Set.ext
  intro s
  cases s with
  | empty =>
    rw [NDA.mem_language_empty]
    exact (or_congr (NDA.mem_language_empty M₁) (NDA.mem_language_empty M₂)).symm
  | append s a =>
    constructor
    · intro ⟨q, hq, hf⟩
      cases q with
      | none => exact False.elim ((union_run_mem M₁ M₂ s a none).mp hq)
      | some q =>
        cases q with
        | inl q => exact Or.inl ⟨q, (union_run_mem M₁ M₂ s a (some (Sum.inl q))).mp hq, hf⟩
        | inr q => exact Or.inr ⟨q, (union_run_mem M₁ M₂ s a (some (Sum.inr q))).mp hq, hf⟩
    · intro h
      cases h with
      | inl h =>
        have ⟨q, hq, hf⟩ := h
        exact ⟨some (Sum.inl q), (union_run_mem M₁ M₂ s a (some (Sum.inl q))).mpr hq, hf⟩
      | inr h =>
        have ⟨q, hq, hf⟩ := h
        exact ⟨some (Sum.inr q), (union_run_mem M₁ M₂ s a (some (Sum.inr q))).mpr hq, hf⟩



/-
For two NDA recognizing languages L₁ and L₂, define an NDA which recognizes
the concatenation of L₁ and L₂
-/
def NDA.concat {α: Type u} (M₁ M₂: NDA α): NDA α := {
  State := M₁.State ⊕ M₂.State
  transition := λ q a q' ↦
    match q, q' with
    | Sum.inl q, Sum.inl q' => q' ∈ M₁.transition q a
    | Sum.inl q, Sum.inr q' => q ∈ M₁.final ∧ q' ∈ M₂.transition M₂.initial a
    | Sum.inr q, Sum.inr q' => q' ∈ M₂.transition q a
    | Sum.inr _, Sum.inl _ => False
  initial := Sum.inl M₁.initial
  final := λ q ↦
    match q with
    | Sum.inl q => q ∈ M₁.final ∧ M₂.initial ∈ M₂.final
    | Sum.inr q => q ∈ M₂.final
}

theorem concat_finite {α: Type u} (M₁ M₂: NDA α) (h₁: Finite M₁.State) (h₂: Finite M₂.State): Finite (NDA.concat M₁ M₂).State := by
  sorry
  
theorem concat_transition_inl {α: Type u} (M₁ M₂: NDA α) (q₁ q₂: M₁.State) (a: α): Sum.inl q₂ ∈ (NDA.concat M₁ M₂).transition (Sum.inl q₁) a ↔ q₂ ∈ M₁.transition q₁ a := by
  rfl

theorem concat_transition_cross {α: Type u} (M₁ M₂: NDA α) (q₁: M₁.State) (q₂: M₂.State) (a: α): Sum.inr q₂ ∈ (NDA.concat M₁ M₂).transition (Sum.inl q₁) a ↔ q₁ ∈ M₁.final ∧ q₂ ∈ M₂.transition M₂.initial a := by
  rfl

theorem concat_run_inl {α: Type u} (M₁ M₂: NDA α) (s: Str α) (q: M₁.State): Sum.inl q ∈ (NDA.concat M₁ M₂).run s ↔ q ∈ M₁.run s := by
  induction s generalizing q with
  | empty =>
    constructor
    · intro h
      exact Sum.inl.inj h
    · intro h
      exact congrArg Sum.inl h
  | append s a ih =>
    constructor
    · intro ⟨p, hp, ht⟩
      cases p with
      | inl p => exact ⟨p, (ih p).mp hp, (concat_transition_inl M₁ M₂ p q a).mp ht⟩
      | inr p => exact False.elim ht
    · intro ⟨p, hp, ht⟩
      exact ⟨Sum.inl p, (ih p).mpr hp, (concat_transition_inl M₁ M₂ p q a).mpr ht⟩

theorem concat_run_inr_split {α: Type u} (M₁ M₂: NDA α) (s: Str α) (q: M₂.State) (h: Sum.inr q ∈ (NDA.concat M₁ M₂).run s): ∃ s₁ ∈ M₁.language, ∃ s₂, q ∈ M₂.run s₂ ∧ s = s₁ + s₂ := by
  induction s generalizing q with
  | empty => cases h
  | append s a ih =>
    have ⟨p, hp, ht⟩ := h
    cases p with
    | inl p =>
      have ⟨hf, ht⟩ := (concat_transition_cross M₁ M₂ p q a).mp ht
      exact ⟨s, ⟨p, (concat_run_inl M₁ M₂ s p).mp hp, hf⟩, Str.singleton a, ⟨M₂.initial, rfl, ht⟩, rfl⟩
    | inr p =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := ih p hp
      exact ⟨s₁, hs₁, Str.append s₂ a, ⟨p, hs₂, ht⟩, congrArg (λ s ↦ Str.append s a) hs⟩

theorem concat_run_inr {α: Type u} (M₁ M₂: NDA α) (s₁: Str α) (h₁: s₁ ∈ M₁.language) (s₂: Str α) (a: α) (q: M₂.State) (h₂: q ∈ M₂.run (Str.append s₂ a)): Sum.inr q ∈ (NDA.concat M₁ M₂).run (s₁ + Str.append s₂ a) := by
  induction s₂ generalizing a q with
  | empty =>
    have ⟨q₁, hq₁, hf⟩ := h₁
    rw [←Str.singleton, NDA.run_singleton] at h₂
    exact ⟨Sum.inl q₁, (concat_run_inl M₁ M₂ s₁ q₁).mpr hq₁, (concat_transition_cross M₁ M₂ q₁ q a).mpr ⟨hf, h₂⟩⟩
  | append s₂ a₁ ih =>
    have ⟨p, hp, ht⟩ := h₂
    exact ⟨Sum.inr p, ih a₁ p hp, ht⟩

theorem concat_language_eq {α: Type u} (M₁ M₂: NDA α): (NDA.concat M₁ M₂).language = Language.concat M₁.language M₂.language := by
  apply Set.ext
  intro s
  constructor
  · intro ⟨q, hq, hf⟩
    cases q with
    | inl q =>
      exact ⟨s, ⟨q, (concat_run_inl M₁ M₂ s q).mp hq, hf.1⟩, Str.empty, (NDA.mem_language_empty M₂).mpr hf.2, rfl⟩
    | inr q =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := concat_run_inr_split M₁ M₂ s q hq
      exact ⟨s₁, hs₁, s₂, ⟨q, hs₂, hf⟩, hs⟩
  · intro ⟨s₁, hs₁, s₂, hs₂, hs⟩
    rw [hs]
    cases s₂ with
    | empty =>
      have ⟨q₁, hq₁, hf₁⟩ := hs₁
      exact ⟨Sum.inl q₁, (concat_run_inl M₁ M₂ s₁ q₁).mpr hq₁, hf₁, (NDA.mem_language_empty M₂).mp hs₂⟩
    | append s₂ a =>
      have ⟨q₂, hq₂, hf₂⟩ := hs₂
      exact ⟨Sum.inr q₂, concat_run_inr M₁ M₂ s₁ hs₁ s₂ a q₂ hq₂, hf₂⟩



/-
For an NDA recognizing L, define an NDA which recognizes L*
-/
def NDA.star {α: Type u} (M: NDA α): NDA α := {
  State := Option M.State
  transition := λ q a q' ↦
    match q, q' with
    | none, some q' => q' ∈ M.transition M.initial a
    | some q, some q' => q' ∈ M.transition q a ∨ (q ∈ M.final ∧ q' ∈ M.transition M.initial a)
    | _, none => False
  initial := none
  final := λ q ↦
    match q with
    | none => True
    | some q => q ∈ M.final
}

theorem star_finite {α: Type u} (M: NDA α) (h: Finite M.State): Finite (NDA.star M).State := by
  sorry
  



theorem star_run_none {α: Type u} (M: NDA α) (s: Str α) (h: none ∈ (NDA.star M).run s): s = Str.empty := by
  cases s with
  | empty => rfl
  | append s a =>
    have ⟨q, _, ht⟩ := h
    cases q <;> exact False.elim ht

theorem star_run_some_split {α: Type u} (M: NDA α) (s: Str α) (q: M.State) (h: some q ∈ (NDA.star M).run s): ∃ s₁ ∈ M.language.star, ∃ s₂, q ∈ M.run s₂ ∧ s = s₁ + s₂ := by
  induction s generalizing q with
  | empty => cases h
  | append s a ih =>
    have ⟨p, hp, ht⟩ := h
    cases p with
    | none =>
      exists Str.empty, Language.star_empty M.language, Str.singleton a
      constructor
      · rw [NDA.run_singleton]
        exact ht
      · rw [star_run_none M s hp]
        rfl
    | some p =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := ih p hp
      cases ht with
      | inl ht =>
        exact ⟨s₁, hs₁, Str.append s₂ a, ⟨p, hs₂, ht⟩, congrArg (λ s ↦ Str.append s a) hs⟩
      | inr ht =>
        exists s
        constructor
        · rw [hs]
          exact Language.star_append M.language s₁ s₂ hs₁ ⟨p, hs₂, ht.1⟩
        · exact ⟨Str.singleton a, ⟨M.initial, rfl, ht.2⟩, rfl⟩

theorem star_run_append {α: Type u} (M: NDA α) (s₁: Str α) (h₁: s₁ ∈ (NDA.star M).language) (s₂: Str α) (a: α) (q: M.State) (h₂: q ∈ M.run (Str.append s₂ a)): some q ∈ (NDA.star M).run (s₁ + Str.append s₂ a) := by
  induction s₂ generalizing a q with
  | empty =>
    have ⟨p, hp, hf⟩ := h₁
    rw [←Str.singleton, NDA.run_singleton] at h₂
    exists p, hp
    cases p with
    | none => exact h₂
    | some p => exact Or.inr ⟨hf, h₂⟩
  | append s₂ a₁ ih =>
    have ⟨p, hp, ht⟩ := h₂
    exact ⟨some p, ih a₁ p hp, Or.inl ht⟩

theorem star_language_append {α: Type u} (M: NDA α) (s₁ s₂: Str α) (h₁: s₁ ∈ (NDA.star M).language) (h₂: s₂ ∈ M.language): s₁ + s₂ ∈ (NDA.star M).language := by
  cases s₂ with
  | empty => exact h₁
  | append s₂ a =>
    have ⟨q, hq, hf⟩ := h₂
    exact ⟨some q, star_run_append M s₁ h₁ s₂ a q hq, hf⟩

theorem star_language_eq {α: Type u} (M: NDA α): (NDA.star M).language = Language.star M.language := by
  apply Set.ext
  intro s
  constructor
  · intro ⟨q, hq, hf⟩
    cases q with
    | none =>
      rw [star_run_none M s hq]
      exact Language.star_empty M.language
    | some q =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := star_run_some_split M s q hq
      rw [hs]
      exact Language.star_append M.language s₁ s₂ hs₁ ⟨q, hs₂, hf⟩
  · intro ⟨t, ht⟩
    rw [ht]
    clear ht
    induction t with
    | empty => exact (NDA.mem_language_empty (NDA.star M)).mpr trivial
    | append t w ih =>
      exact star_language_append M (Str.flatten (Str.map (λ w ↦ w.val) t)) w.val ih w.property



/-
For any regular language, there is a nondeterministic finite automata recognizing that language.
-/
theorem regular_nda (α: Type u) {L: Language α} (hL: L.regular): ∃ M: NDA.{u, 0} α, (M.finite ∧ M.language = L) := by
  have ⟨R, hR⟩ := hL
  rw [←hR]
  clear hL hR L
  induction R with
  | empty =>
    exists NDA.empty α
    constructor
    · exact empty_finite
    · exact empty_language_eq
  | singleton a =>
    exists NDA.singleton a
    constructor
    · exact singleton_finite a
    · exact singleton_language_eq a
  | union R₁ R₂ ih₁ ih₂ =>
    have ⟨M₁, h₁⟩ := ih₁
    have ⟨M₂, h₂⟩ := ih₂
    exists NDA.union M₁ M₂
    constructor
    · exact union_finite h₁.1 h₂.1
    · sorry
  | concat R₁ R₂ ih₁ ih₂ =>
    have ⟨M₁, h₁⟩ := ih₁
    have ⟨M₂, h₂⟩ := ih₂
    exists NDA.concat M₁ M₂
    constructor
    sorry
    sorry
  | star R ih =>
    have ⟨M, h⟩ := ih
    exists NDA.star M
    constructor
    exact star_finite M h.1
    sorry



/-
Kleene's theorem
A language is regular if and only if it is accepted by some finite automaton.
-/
theorem Kleene'sTheorem {α: Type u} {L: Language α}: L.regular ↔ ∃ M: Automaton α, (M.finite ∧ M.language = L) := by
  sorry
