import Algebra.Set

variable {X: Type u} {Y: Type v} {Z: Type w}



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
Equinumerous equivalence relation on sets
Two sets are equinumerous if there exists a bijection between them.
-/
def Equinumerous (X Y: Type u): Prop :=
  ∃ f: X → Y, Bijective f
  
theorem equinumerous_reflexive {X: Type u}: Equinumerous X X := by
  exists id
  exact Bijective.id
  
theorem equinumerous_symmetric {X Y: Type u} (h: Equinumerous X Y): Equinumerous Y X := by
  have ⟨f, hf⟩ := h
  exists Bijective.inverse hf
  exact Bijective.inverse_bijective hf
  
theorem equinumerous_transitive {X Y Z: Type u} (h₁: Equinumerous X Y) (h₂: Equinumerous Y Z): Equinumerous X Z := by
  have ⟨f, hf⟩ := h₁
  have ⟨g, hg⟩ := h₂
  exists g ∘ f
  exact Bijective.comp hf hg

def Equinumerous.setoid: Setoid (Type u) where
  r := Equinumerous
  iseqv := by 
    constructor
    · intro _
      exact equinumerous_reflexive
    · intro _ _ h
      exact equinumerous_symmetric h
    · intro _ _ _ h₁ h₂
      exact equinumerous_transitive h₁ h₂



/-
The cardinal numbers are the quotient of the class of sets by the equinumerous
relation
-/
def Cardinal: Type (u + 1) :=
  Quotient Equinumerous.setoid



/-
The cardinality of a given "set" is the equivalence class of that set
-/
def cardinality (X: Type u): Cardinal :=
  Quotient.mk Equinumerous.setoid X

instance: Coe Nat Cardinal := {
  coe := λ n ↦ cardinality (ULift (Fin n))
}



/-
We can define a less than relation on the cardinals by, for cardinals a and b,
a is less than b if there is an injective from a representitive of a to a
representitive of b
-/
def Cardinal.le₀: Type u → Type u → Prop :=
  λ X Y ↦ ∃ f: X → Y, Injective f

theorem Cardinal.le₀_well_defined (X₁ Y₁ X₂ Y₂: Type u) (h₁: Equinumerous X₁ X₂) (h₂: Equinumerous Y₁ Y₂): Cardinal.le₀ X₁ Y₁ = Cardinal.le₀ X₂ Y₂ := by
  have ⟨f, hf⟩ := h₁
  have ⟨g, hg⟩ := h₂
  unfold Cardinal.le₀
  apply propext
  constructor
  · intro h
    have ⟨k, hk⟩ := h
    exists g ∘ k ∘ Bijective.inverse hf
    exact Injective.comp (Injective.comp (Surjective.inverse_injective hf.right) hk) hg.left
  · intro h
    have ⟨k, hk⟩ := h
    exists Bijective.inverse hg ∘ k ∘ f
    exact Injective.comp (Injective.comp hf.left hk) (Surjective.inverse_injective hg.right)

def Cardinal.le (a b: Cardinal): Prop :=
  Quotient.liftOn₂ a b Cardinal.le₀ Cardinal.le₀_well_defined

instance: LE Cardinal.{u} := {
  le := Cardinal.le
}

theorem Cardinal.le_refl (κ: Cardinal): κ ≤ κ := by
  sorry

theorem Cardinal.le_trans {κ μ ν: Cardinal} (h₁: κ ≤ μ) (h₂: μ ≤ ν): κ ≤ ν := by
  sorry

theorem Cardinal.le_antisymm {κ μ: Cardinal} (h₁: κ ≤ μ) (h₂: μ ≤ κ): κ = μ := by
  sorry

theorem Cardinal.le_total (κ μ: Cardinal): κ ≤ μ ∨ μ ≤ κ := by
  sorry

theorem Cardinal.well_ordered (S: Set Cardinal) (h: S.Nonempty): ∃ κ ∈ S, ∀ μ ∈ S, κ ≤ μ := by
  sorry




/-
A cardinal is finite if there exist a natural such that `Fin n` is is in the
same equivalence class as that cardinal
-/
def Cardinal.finite (κ: Cardinal): Prop :=
  ∃ n: Nat, κ = n

def Finite (X: Type u): Prop :=
  (cardinality X).finite
  
  
  
/-
Addition of cardinals
-/
def Cardinal.add₀: Type u → Type u → Cardinal.{u} :=
  λ X Y ↦ cardinality (X ⊕ Y)

theorem Cardinal.add₀_well_defined (X₁ Y₁ X₂ Y₂: Type u) (h₁: Equinumerous X₁ X₂) (h₂: Equinumerous Y₁ Y₂): Cardinal.add₀ X₁ Y₁ = Cardinal.add₀ X₂ Y₂ := by
  sorry

def Cardinal.add (κ μ: Cardinal): Cardinal :=
  Quotient.liftOn₂ κ μ Cardinal.add₀ Cardinal.add₀_well_defined

instance: Add Cardinal := {
  add := Cardinal.add
}



/-
Multiplication of cardinals
-/
def Cardinal.mul₀: Type u → Type u → Cardinal.{u} :=
  λ X Y ↦ cardinality (X × Y)

theorem Cardinal.mul₀_well_defined (X₁ Y₁ X₂ Y₂: Type u) (h₁: Equinumerous X₁ X₂) (h₂: Equinumerous Y₁ Y₂): Cardinal.mul₀ X₁ Y₁ = Cardinal.mul₀ X₂ Y₂ := by
  sorry

def Cardinal.mul (κ μ: Cardinal): Cardinal :=
  Quotient.liftOn₂ κ μ Cardinal.mul₀ Cardinal.mul₀_well_defined

instance: Mul Cardinal := {
  mul := Cardinal.mul
}



/-
Other theorems and definitions
-/
def ℵ₀: Cardinal :=
  cardinality (ULift Nat)
  
theorem cardinality_prod (X Y: Type u): cardinality (X × Y) = cardinality X * cardinality Y :=
  rfl

theorem one_le_cardinality {X: Type u} (h: Nonempty X): (1: Nat) ≤ cardinality X := by
  sorry
