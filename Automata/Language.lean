import Automata.String

variable {α: Type u}

/-
A language is a set of strings over an alphabet α.
-/
abbrev Language (α: Type u): Type u :=
 Set (Str α)
 
namespace Language
 
 
 
/-
Union of two languages
-/
def union (L₁ L₂: Language α): Language α :=
  L₁ ∪ L₂

def concat (L₁ L₂: Language α): Language α :=
  λ s ↦ ∃ s₁ ∈ L₁, ∃ s₂ ∈ L₂, s = s₁ + s₂



/-
Kleene star operation on a language
-/
def star (L: Language α): Language α :=
  λ s ↦ ∃ t: Str L, s = Str.flatten (Str.map (λ w ↦ w.val) t)

theorem subset_star (L: Language α): L ⊆ L.star := by
  intro s ls
  sorry
  --exists Str.singleton ⟨s, ls⟩

theorem star_star (L: Language α): L.star.star = L.star := by
  funext s
  simp
  constructor
  · sorry
  · apply Language.subset_star L.star


end Language

theorem Language.star_empty {α: Type u} (L: Language α): Str.empty ∈ L.star := by
  exact ⟨Str.empty, rfl⟩

theorem Language.star_append {α: Type u} (L: Language α) (s₁ s₂: Str α) (h₁: s₁ ∈ L.star) (h₂: s₂ ∈ L): s₁ + s₂ ∈ L.star := by
  have ⟨t, ht⟩ := h₁
  exists Str.append t ⟨s₂, h₂⟩
  exact congrArg (λ s ↦ s + s₂) ht
