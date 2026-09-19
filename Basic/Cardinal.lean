import Basic.Set

variable {X: Type u} {Y: Type v} {Z: Type w}

def Injective (f: X → Y): Prop :=
  ∀ x x', f x = f x' → x = x'

theorem Injective.id: Injective (@id X) := by
  sorry

theorem Injective.comp {f: X → Y} {g: Y → Z} (hf: Injective f) (hg: Injective g): Injective (g ∘ f) := by
  sorry

def Surjective (f: X → Y): Prop :=
  ∀ y, ∃ x, f x = y

theorem Surjective.id: Surjective (@id X) := by
  sorry

theorem Surjective.comp {f: X → Y} {g: Y → Z} (hf: Surjective f) (hg: Surjective g): Surjective (g ∘ f) := by
  sorry

def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f

theorem Bijective.id: Bijective (@id X) := by
  sorry

theorem Bijective.comp {f: X → Y} {g: Y → Z} (hf: Bijective f) (hg: Bijective g): Bijective (g ∘ f) := by
  sorry


def Equinumerous (X Y: Type u): Prop :=
  ∃ f: X → Y, Bijective f

def Equinumerous.setoid: Setoid (Type u) where
  r := Equinumerous
  iseqv := by sorry

def Cardinal: Type (u + 1) :=
  Quotient Equinumerous.setoid

def cardinality (X: Type u): Cardinal :=
  Quotient.mk Equinumerous.setoid X

def Cardinal.le (a b: Cardinal): Prop :=
  Quotient.liftOn₂ a b (fun X Y => ∃ f: X → Y, Injective f) (by sorry)

instance: LE Cardinal.{u} := {
  le := Cardinal.le
}

instance: Coe Nat Cardinal := {
  coe := fun n => cardinality (ULift (Fin n))
}

def Cardinal.finite (κ: Cardinal): Prop :=
  ∃ n: Nat, κ = n

def ℵ₀: Cardinal :=
  cardinality (ULift Nat)

def Cardinal.add (κ μ: Cardinal): Cardinal :=
  Quotient.liftOn₂ κ μ (fun X Y => cardinality (X ⊕ Y)) (by sorry)

instance: Add Cardinal := {
  add := Cardinal.add
}

def Cardinal.mul (κ μ: Cardinal): Cardinal :=
  Quotient.liftOn₂ κ μ (fun X Y => cardinality (X × Y)) (by sorry)

instance: Mul Cardinal := {
  mul := Cardinal.mul
}

theorem cardinality_prod (X Y: Type u): cardinality (X × Y) = cardinality X * cardinality Y :=
  rfl

theorem one_le_cardinality {X: Type u} (h: Nonempty X): (1: Nat) ≤ cardinality X := by
  sorry

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

def Finite (X: Type u): Prop :=
  (cardinality X).finite
