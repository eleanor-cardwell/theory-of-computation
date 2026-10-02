import Automata.RegularExpression
import Automata.NDA

open Classical

/-
TODO move lemmas to appropriate files
-/
theorem Set.ext {X: Type u} {S₁ S₂: Set X} (h: ∀ x, x ∈ S₁ ↔ x ∈ S₂): S₁ = S₂ := by
  funext x
  exact propext (h x)

theorem NDA.mem_language_empty {α: Type u} (A: NDA α): Str.empty ∈ A.language ↔ A.initial ∈ A.final := by
  constructor
  · intro ⟨q, hq, hf⟩
    have hq: q = A.initial := hq
    rw [hq] at hf
    exact hf
  · intro h
    exact ⟨A.initial, rfl, h⟩

theorem NDA.run_singleton {α: Type u} (A: NDA α) (a: α): A.run (Str.singleton a) = A.transition A.initial a := by
  apply Set.ext
  intro q
  constructor
  · intro ⟨p, hp, ht⟩
    have hp: p = A.initial := hp
    rw [hp] at ht
    exact ht
  · intro h
    exact ⟨A.initial, rfl, h⟩

theorem fin_finite (n: Nat): Finite (Fin n) := by
  exists n
  apply Quotient.sound
  exists λ q ↦ ULift.up q
  constructor
  · intro q₁ q₂ h
    exact congrArg ULift.down h
  · intro q
    exists q.down



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
def NDA.union {α: Type u} (A₁ A₂: NDA α): NDA α := {
  State := Option (A₁.State ⊕ A₂.State)
  transition := λ q a q' ↦
    match q, q' with
    | none, some (Sum.inl q') => q' ∈ A₁.transition A₁.initial a
    | none, some (Sum.inr q') => q' ∈ A₂.transition A₂.initial a
    | some (Sum.inl q), some (Sum.inl q') => q' ∈ A₁.transition q a
    | some (Sum.inr q), some (Sum.inr q') => q' ∈ A₂.transition q a
    | _, _ => False
  initial := none
  final := λ q ↦
    match q with
    | none => A₁.initial ∈ A₁.final ∨ A₂.initial ∈ A₂.final
    | some (Sum.inl q) => q ∈ A₁.final
    | some (Sum.inr q) => q ∈ A₂.final
}

theorem union_finite {α: Type u} (A₁ A₂: NDA α) (h₁: Finite A₁.State) (h₂: Finite A₂.State): Finite (NDA.union A₁ A₂).State := by
  sorry
  
theorem union_run_mem {α: Type u} (A₁ A₂: NDA α): ∀ (s: Str α) (a: α) (q: (NDA.union A₁ A₂).State), q ∈ (NDA.union A₁ A₂).run (Str.append s a) ↔ match q with
    | none => False
    | some (Sum.inl q) => q ∈ A₁.run (Str.append s a)
    | some (Sum.inr q) => q ∈ A₂.run (Str.append s a) := by
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
        rw [NDA.run_singleton A₁]
        rfl
      | inr q =>
        rw [NDA.run_singleton A₂]
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

theorem Set.exists_singleton {X: Type u} (x: X) (P: X → Prop): (∃ y, Set.singleton x y ∧ P y) ↔ P x := by
  constructor
  · intro ⟨y, hy, h⟩
    have hy: y = x := hy
    rw [hy] at h
    exact h
  · intro h
    exact ⟨x, rfl, h⟩

theorem Set.exists_union {X: Type u} (S₁ S₂: Set X) (P: X → Prop): (∃ x, (S₁ ∪ S₂) x ∧ P x) ↔ (∃ x, S₁ x ∧ P x) ∨ (∃ x, S₂ x ∧ P x) := by
  constructor
  · intro ⟨x, hx, h⟩
    cases hx with
    | inl hx => exact Or.inl ⟨x, hx, h⟩
    | inr hx => exact Or.inr ⟨x, hx, h⟩
  · intro h
    cases h with
    | inl h =>
      have ⟨x, hx, h⟩ := h
      exact ⟨x, Or.inl hx, h⟩
    | inr h =>
      have ⟨x, hx, h⟩ := h
      exact ⟨x, Or.inr hx, h⟩

theorem Set.exists_image {X: Type u} {Y: Type v} (f: X → Y) (S: Set X) (P: Y → Prop): (∃ y, Set.image f S y ∧ P y) ↔ ∃ x, S x ∧ P (f x) := by
  constructor
  · intro ⟨y, ⟨x, hx, hxy⟩, h⟩
    rw [←hxy] at h
    exact ⟨x, hx, h⟩
  · intro ⟨x, hx, h⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, h⟩

theorem union_run {α: Type u} (A₁ A₂: NDA α) (s: Str α) (a: α): (NDA.union A₁ A₂).run (Str.append s a) = Set.image (λ q ↦ some (Sum.inl q)) (A₁.run (Str.append s a)) ∪ Set.image (λ q ↦ some (Sum.inr q)) (A₂.run (Str.append s a)) := by
  apply Set.ext
  intro q
  constructor
  · intro h
    cases q with
    | none => exact False.elim ((union_run_mem A₁ A₂ s a none).mp h)
    | some q =>
      cases q with
      | inl q => exact Or.inl ⟨q, (union_run_mem A₁ A₂ s a (some (Sum.inl q))).mp h, rfl⟩
      | inr q => exact Or.inr ⟨q, (union_run_mem A₁ A₂ s a (some (Sum.inr q))).mp h, rfl⟩
  · intro h
    cases h with
    | inl h =>
      have ⟨q₁, hq, h⟩ := h
      rw [←h]
      exact (union_run_mem A₁ A₂ s a (some (Sum.inl q₁))).mpr hq
    | inr h =>
      have ⟨q₂, hq, h⟩ := h
      rw [←h]
      exact (union_run_mem A₁ A₂ s a (some (Sum.inr q₂))).mpr hq

theorem union_language_eq {α: Type u} (A₁ A₂: NDA α): (NDA.union A₁ A₂).language = A₁.language ∪ A₂.language := by
  apply Set.ext
  intro s
  cases s with
  | empty =>
    rw [NDA.mem_language_empty]
    exact (or_congr (NDA.mem_language_empty A₁) (NDA.mem_language_empty A₂)).symm
  | append s a =>
    unfold NDA.language
    dsimp only [Union.union, Set.union, Set.Nonempty, Inter.inter, Set.intersection, Membership.mem, Set.Mem]
    rw [union_run, Set.exists_union, Set.exists_image, Set.exists_image]
    rfl



/-
For two NDA recognizing languages L₁ and L₂, define an NDA which recognizes
the concatenation of L₁ and L₂
-/
def NDA.concat {α: Type u} (A₁ A₂: NDA α): NDA α := {
  State := A₁.State ⊕ A₂.State
  transition := λ q a ↦
    match q with
    | Sum.inl q =>
      if q ∈ A₁.final then
        Set.inl (A₁.transition q a) ∪ Set.inr (A₂.transition A₂.initial a)
      else
        Set.inl (A₁.transition q a)
    | Sum.inr q => Set.inr (A₂.transition q a)
  initial := Sum.inl A₁.initial
  final := λ q ↦
    match q with
    | Sum.inl q => q ∈ A₁.final ∧ A₂.initial ∈ A₂.final
    | Sum.inr q => q ∈ A₂.final
}

theorem concat_finite {α: Type u} (A₁ A₂: NDA α) (h₁: Finite A₁.State) (h₂: Finite A₁.State): Finite (NDA.concat A₁ A₂).State := by
  sorry
  
theorem concat_transition_inl {α: Type u} (A₁ A₂: NDA α) (q₁ q₂: A₁.State) (a: α): Sum.inl q₂ ∈ (NDA.concat A₁ A₂).transition (Sum.inl q₁) a ↔ q₂ ∈ A₁.transition q₁ a := by
  dsimp only [NDA.concat]
  by_cases h: q₁ ∈ A₁.final
  · rw [if_pos h]
    constructor
    · intro h
      cases h with
      | inl h => exact h
      | inr h => exact False.elim h
    · exact Or.inl
  · rw [if_neg h]
    rfl

theorem concat_transition_cross {α: Type u} (A₁ A₂: NDA α) (q₁: A₁.State) (q₂: A₂.State) (a: α): Sum.inr q₂ ∈ (NDA.concat A₁ A₂).transition (Sum.inl q₁) a ↔ q₁ ∈ A₁.final ∧ q₂ ∈ A₂.transition A₂.initial a := by
  dsimp only [NDA.concat]
  by_cases h: q₁ ∈ A₁.final
  · rw [if_pos h]
    constructor
    · intro ht
      cases ht with
      | inl ht => exact False.elim ht
      | inr ht => exact ⟨h, ht⟩
    · intro ⟨_, ht⟩
      exact Or.inr ht
  · rw [if_neg h]
    constructor
    · intro ht
      exact False.elim ht
    · intro ⟨hf, _⟩
      exact False.elim (h hf)

theorem concat_run_inl {α: Type u} (A₁ A₂: NDA α) (s: Str α) (q: A₁.State): Sum.inl q ∈ (NDA.concat A₁ A₂).run s ↔ q ∈ A₁.run s := by
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
      | inl p => exact ⟨p, (ih p).mp hp, (concat_transition_inl A₁ A₂ p q a).mp ht⟩
      | inr p => exact False.elim ht
    · intro ⟨p, hp, ht⟩
      exact ⟨Sum.inl p, (ih p).mpr hp, (concat_transition_inl A₁ A₂ p q a).mpr ht⟩

theorem concat_run_inr_split {α: Type u} (A₁ A₂: NDA α) (s: Str α) (q: A₂.State) (h: Sum.inr q ∈ (NDA.concat A₁ A₂).run s): ∃ s₁ ∈ A₁.language, ∃ s₂, q ∈ A₂.run s₂ ∧ s = s₁ + s₂ := by
  induction s generalizing q with
  | empty => cases h
  | append s a ih =>
    have ⟨p, hp, ht⟩ := h
    cases p with
    | inl p =>
      have ⟨hf, ht⟩ := (concat_transition_cross A₁ A₂ p q a).mp ht
      exact ⟨s, ⟨p, (concat_run_inl A₁ A₂ s p).mp hp, hf⟩, Str.singleton a, ⟨A₂.initial, rfl, ht⟩, rfl⟩
    | inr p =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := ih p hp
      exact ⟨s₁, hs₁, Str.append s₂ a, ⟨p, hs₂, ht⟩, congrArg (λ s ↦ Str.append s a) hs⟩

theorem concat_run_inr {α: Type u} (A₁ A₂: NDA α) (s₁: Str α) (h₁: s₁ ∈ A₁.language) (s₂: Str α) (a: α) (q: A₂.State) (h₂: q ∈ A₂.run (Str.append s₂ a)): Sum.inr q ∈ (NDA.concat A₁ A₂).run (s₁ + Str.append s₂ a) := by
  induction s₂ generalizing a q with
  | empty =>
    have ⟨q₁, hq₁, hf⟩ := h₁
    rw [←Str.singleton, NDA.run_singleton] at h₂
    exact ⟨Sum.inl q₁, (concat_run_inl A₁ A₂ s₁ q₁).mpr hq₁, (concat_transition_cross A₁ A₂ q₁ q a).mpr ⟨hf, h₂⟩⟩
  | append s₂ a₁ ih =>
    have ⟨p, hp, ht⟩ := h₂
    exact ⟨Sum.inr p, ih a₁ p hp, ht⟩

theorem concat_language_eq {α: Type u} (A₁ A₂: NDA α): (NDA.concat A₁ A₂).language = Language.concat A₁.language A₂.language := by
  apply Set.ext
  intro s
  constructor
  · intro ⟨q, hq, hf⟩
    cases q with
    | inl q =>
      exact ⟨s, ⟨q, (concat_run_inl A₁ A₂ s q).mp hq, hf.1⟩, Str.empty, (NDA.mem_language_empty A₂).mpr hf.2, rfl⟩
    | inr q =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := concat_run_inr_split A₁ A₂ s q hq
      exact ⟨s₁, hs₁, s₂, ⟨q, hs₂, hf⟩, hs⟩
  · intro ⟨s₁, hs₁, s₂, hs₂, hs⟩
    rw [hs]
    cases s₂ with
    | empty =>
      have ⟨q₁, hq₁, hf₁⟩ := hs₁
      exact ⟨Sum.inl q₁, (concat_run_inl A₁ A₂ s₁ q₁).mpr hq₁, hf₁, (NDA.mem_language_empty A₂).mp hs₂⟩
    | append s₂ a =>
      have ⟨q₂, hq₂, hf₂⟩ := hs₂
      exact ⟨Sum.inr q₂, concat_run_inr A₁ A₂ s₁ hs₁ s₂ a q₂ hq₂, hf₂⟩



/-
For an NDA recognizing L, define an NDA which recognizes L*
-/
def NDA.star {α: Type u} (A: NDA α): NDA α := {
  State := Option A.State
  transition := λ q a q' ↦
    match q, q' with
    | none, some q' => q' ∈ A.transition A.initial a
    | some q, some q' => q' ∈ A.transition q a ∨ (q ∈ A.final ∧ q' ∈ A.transition A.initial a)
    | _, none => False
  initial := none
  final := λ q ↦
    match q with
    | none => True
    | some q => q ∈ A.final
}

theorem star_finite {α: Type u} (A: NDA α) (h: Finite A.State): Finite (NDA.star A).State := by
  sorry
  
theorem Language.star_empty {α: Type u} (L: Language α): Str.empty ∈ L.star := by
  exact ⟨Str.empty, rfl⟩

theorem Language.star_append {α: Type u} (L: Language α) (s₁ s₂: Str α) (h₁: s₁ ∈ L.star) (h₂: s₂ ∈ L): s₁ + s₂ ∈ L.star := by
  have ⟨t, ht⟩ := h₁
  exists Str.append t ⟨s₂, h₂⟩
  exact congrArg (λ s ↦ s + s₂) ht

theorem star_run_none {α: Type u} (A: NDA α) (s: Str α) (h: none ∈ (NDA.star A).run s): s = Str.empty := by
  cases s with
  | empty => rfl
  | append s a =>
    have ⟨q, _, ht⟩ := h
    cases q <;> exact False.elim ht

theorem star_run_some_split {α: Type u} (A: NDA α) (s: Str α) (q: A.State) (h: some q ∈ (NDA.star A).run s): ∃ s₁ ∈ A.language.star, ∃ s₂, q ∈ A.run s₂ ∧ s = s₁ + s₂ := by
  induction s generalizing q with
  | empty => cases h
  | append s a ih =>
    have ⟨p, hp, ht⟩ := h
    cases p with
    | none =>
      exists Str.empty, Language.star_empty A.language, Str.singleton a
      constructor
      · rw [NDA.run_singleton]
        exact ht
      · rw [star_run_none A s hp]
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
          exact Language.star_append A.language s₁ s₂ hs₁ ⟨p, hs₂, ht.1⟩
        · exact ⟨Str.singleton a, ⟨A.initial, rfl, ht.2⟩, rfl⟩

theorem star_run_append {α: Type u} (A: NDA α) (s₁: Str α) (h₁: s₁ ∈ (NDA.star A).language) (s₂: Str α) (a: α) (q: A.State) (h₂: q ∈ A.run (Str.append s₂ a)): some q ∈ (NDA.star A).run (s₁ + Str.append s₂ a) := by
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

theorem star_language_append {α: Type u} (A: NDA α) (s₁ s₂: Str α) (h₁: s₁ ∈ (NDA.star A).language) (h₂: s₂ ∈ A.language): s₁ + s₂ ∈ (NDA.star A).language := by
  cases s₂ with
  | empty => exact h₁
  | append s₂ a =>
    have ⟨q, hq, hf⟩ := h₂
    exact ⟨some q, star_run_append A s₁ h₁ s₂ a q hq, hf⟩

theorem star_language_eq {α: Type u} (A: NDA α): (NDA.star A).language = Language.star A.language := by
  apply Set.ext
  intro s
  constructor
  · intro ⟨q, hq, hf⟩
    cases q with
    | none =>
      rw [star_run_none A s hq]
      exact Language.star_empty A.language
    | some q =>
      have ⟨s₁, hs₁, s₂, hs₂, hs⟩ := star_run_some_split A s q hq
      rw [hs]
      exact Language.star_append A.language s₁ s₂ hs₁ ⟨q, hs₂, hf⟩
  · intro ⟨t, ht⟩
    rw [ht]
    clear ht
    induction t with
    | empty => exact (NDA.mem_language_empty (NDA.star A)).mpr trivial
    | append t w ih =>
      exact star_language_append A (Str.flatten (Str.map (λ w ↦ w.val) t)) w.val ih w.property



/-
For any regular language, there is a nondeterministic finite automata recognizing that language.
-/
theorem regular_nda (α: Type u) {L: Language α} (hL: L.regular): ∃ A: NDA.{u, 0} α, (A.finite ∧ A.language = L) := by
  have ⟨R, hR⟩ := hL
  rw [←hR]
  clear hL hR L
  induction R with
  | empty =>
    exists NDA.empty α
    sorry
  | singleton a =>
    exists NDA.singleton a
    sorry
  | union R₁ R₂ ih₁ ih₂ =>
    have ⟨A₁, h₁⟩ := ih₁
    have ⟨A₂, h₂⟩ := ih₂
    exists NDA.union A₁ A₂
    constructor
    -- use finite sum of cardinals
    sorry
    sorry
  | concat R₁ R₂ ih₁ ih₂ =>
    have ⟨A₁, h₁⟩ := ih₁
    have ⟨A₂, h₂⟩ := ih₂
    exists NDA.concat A₁ A₂
    constructor
    sorry
    sorry
  | star R ih =>
    have ⟨A, h⟩ := ih
    exists NDA.star A
    constructor
    exact star_finite A h.1
    sorry



/-
Kleene's theorem
A language is regular if and only if it is accepted by some finite automaton.
-/
theorem Kleene'sTheorem (α: Type u) {L: Language α}: L.regular ↔ ∃ A: Automaton α, (A.finite ∧ A.language = L) := by
  sorry
