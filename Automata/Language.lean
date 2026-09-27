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
  exists Str.singleton ⟨s, ls⟩

theorem star_star (L: Language α): L.star.star = L.star := by
  funext s
  simp
  constructor
  · sorry
  · apply Language.subset_star L.star
