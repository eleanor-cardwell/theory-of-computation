import Algebra.Set

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

/-
Injectivity
-/
def Injective (f: X → Y): Prop :=
  ∀ x x', f x = f x' → x = x'

theorem Injective.id: Injective (@id X) := by
  intro _ _ h
  exact h

theorem Injective.comp {f: X → Y} {g: Y → Z} (hf: Injective f) (hg: Injective g): Injective (g ∘ f) := by
  intro x₁ x₂ h
  simp at h
  have h₁ := hg (f x₁) (f x₂) h
  have h₂ := hf x₁ x₂ h₁
  exact h₂

theorem injective_if_left_inverse {f: X → Y} {g: Y → X} (h₁: g ∘ f = _root_.id): Injective f := by
  intro x₁ x₂ h₂
  have h₃ := congrArg g h₂
  exact (congrFun h₁ x₁).symm.trans (h₃.trans (congrFun h₁ x₂))

theorem Injective.inverse_left {f: X → Y} {g: Y → X} (hf: Injective f) (h: f ∘ g = _root_.id): g ∘ f = _root_.id := by
  funext x
  apply hf
  exact congrFun h (f x)



/-
Surjectivity
-/
def Surjective (f: X → Y): Prop :=
  ∀ y, ∃ x, f x = y

theorem Surjective.id: Surjective (@id X) := by
  intro x
  exists x

theorem Surjective.comp {f: X → Y} {g: Y → Z} (hf: Surjective f) (hg: Surjective g): Surjective (g ∘ f) := by
  intro z
  have ⟨y, hy⟩ := hg z
  have ⟨x, hx⟩ := hf y
  exists x
  rw [Function.comp, hx, hy]

theorem surjective_if_right_inverse {f: X → Y} {g: Y → X} (h: f ∘ g = _root_.id): Surjective f := by
  intro y
  exists g y
  exact congrFun h y

noncomputable def Surjective.inverse {f: X → Y} (h: Surjective f): Y → X :=
  λ y ↦ Classical.choose (h y)

theorem Surjective.inverse_right {f: X → Y} (h: Surjective f): f ∘ Surjective.inverse h = _root_.id := by
  funext y
  exact Classical.choose_spec (h y)

theorem Surjective.inverse_injective {f: X → Y} (h: Surjective f): Injective (Surjective.inverse h) := by
  exact injective_if_left_inverse (Surjective.inverse_right h)



/-
Bijectivity
-/
def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f

theorem Bijective.id: Bijective (@id X) := by
  exact ⟨Injective.id, Surjective.id⟩

theorem Bijective.comp {f: X → Y} {g: Y → Z} (hf: Bijective f) (hg: Bijective g): Bijective (g ∘ f) := by
  have ⟨hf₁, hf₂⟩ := hf
  have ⟨hg₁, hg₂⟩ := hg
  constructor
  · exact Injective.comp hf₁ hg₁
  · exact Surjective.comp hf₂ hg₂
    
noncomputable def Bijective.inverse {f: X → Y} (h: Bijective f): Y → X :=
  Surjective.inverse h.right
    
theorem Bijective.inverse_left {f: X → Y} (h: Bijective f): (Bijective.inverse h) ∘ f = _root_.id := by
  exact Injective.inverse_left h.left (Surjective.inverse_right h.right)
    
theorem Bijective.inverse_right {f: X → Y} (h: Bijective f): f ∘ (Bijective.inverse h) = _root_.id := by
  exact Surjective.inverse_right h.right
  
theorem Bijective.inverse_bijective {f: X → Y} (h: Bijective f): Bijective (Bijective.inverse h) := by
  constructor
  · exact Surjective.inverse_injective h.right
  · exact surjective_if_right_inverse (Bijective.inverse_left h)


  
/-
Finiteness
-/
def Finite (X: Type u): Prop :=
  ∃ n: Nat, ∃ f: X → Fin n, Bijective f

def Set.finite {X: Type u} (S: Set X): Prop :=
  Finite S


theorem fin_finite (n: Nat): Finite (Fin n) := by
  exists n, id
  exact Bijective.id
