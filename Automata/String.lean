import Basic.Set
import Basic.Monoid

variable {α: Type u} {β: Type v}

inductive Str (α: Type u) where
| empty: Str α
| append: Str α → α → Str α

notation "ε" => Str.empty

-- allows + notation for adding characters to strings
instance: HAdd (Str α) α (Str α) := {
  hAdd := Str.append
}

def Str.singleton (a: α): Str α :=
 append empty a

instance: Coe α (Str α) := {
  coe := Str.singleton
}

def Str.prepend (a: α) (s: Str α): Str α :=
  match s with
  | empty => a
  | append t h => append (prepend a t) h

instance: HAdd α (Str α) (Str α) := {
  hAdd := Str.prepend
}

def Str.concat (s₁ s₂: Str α): Str α :=
 match s₂ with
 | ε => s₁
 | append t a => append (concat s₁ t) a

--  allows + notation for adding strings
instance: Add (Str α) := {
  add := Str.concat
}

theorem Str.concat_empty_right (s: Str α): s + ε = s := by
  rfl

theorem Str.concat_empty_left (s: Str α): ε + s = s := by
  induction s with
  | empty => rfl
  | append h t ih => calc
    ε + (append h t)
      = append (ε + h) t := by rfl
    _ = append h t       := by rw [ih]

def Str.reverse (s: Str α): Str α :=
  match s with
  | empty => empty
  | append t a => a + (reverse t)

-- allows s⁻¹ to denote reverse of string
instance: Inv (Str α) := ⟨Str.reverse⟩

theorem Str.reverse_empty: (ε: Str α)⁻¹ = ε := by
  rfl

theorem Str.inv_concat (s₁ s₂: Str α): (s₁ + s₂)⁻¹ = s₂⁻¹ + s₁⁻¹ := by
  induction s₂ with
  | empty => calc
    (s₁ + ε)⁻¹
      = s₁⁻¹       := by rw [concat_empty_right]
    _ = ε + s₁⁻¹   := by rw [concat_empty_left]
    _ = ε⁻¹ + s₁⁻¹ := by rw [reverse_empty]
  | append t a ih => calc
    (s₁ + (t + a))⁻¹
      = ((s₁ + t) + a)⁻¹ := by rfl
    _ = a + (s₁ + t)⁻¹   := by rfl
    _ = a + (t⁻¹ + s₁⁻¹) := by rw [ih]
    _ = (a + t⁻¹) + s₁⁻¹ := by sorry
    _ = (t + a)⁻¹ + s₁⁻¹ := by rfl

theorem Str.inv_inv (s: Str α): s⁻¹⁻¹ = s := by
  induction s with
  | empty => rfl
  | append t a ih => calc
    (t + a)⁻¹⁻¹
      = (a + t⁻¹)⁻¹ := by rfl
    _ = (a + t⁻¹)⁻¹ := by rfl
    _ = t + a := by sorry

def Str.length (s: Str α): Nat :=
 match s with
 | empty => 0
 | append t _ => t.length + 1

theorem Str.length_prepend (a: α) (s: Str α): length (a + s) = 1 + length s := by
  sorry


-- length is a monoid homomorphism to ℕ

theorem Str.length_concat (s t: Str α): length (s + t) = length s + length t := by
  sorry

theorem Str.length_reverse (s: Str α): length s⁻¹ = length s := by
  sorry

-- ordering on strings by prefix

def Str.prefix (s t: Str α): Prop :=
  sorry

instance: LE (Str α) := {
  le := Str.prefix
}

-- todo: state prefix is refl/trans/antisymm

-- todo: if s is a prefix of t, then s is shorter than t
-- i.e. s ≤ t implies length(s) ≤ length(t);
-- length is monotone:)

-- flatten a string of strings to one strong, e.g. [[1,2],[3]] => [1,2,3].
def Str.flatten (s: Str (Str α)): Str α :=
  match s with
  | empty => empty
  | append t h => h + flatten t

def Str.map (f: α → β) (s: Str α): Str β :=
  match s with
  | empty => empty
  | append t h => Str.map f t + f h



instance (α: Type u): Monoid (Str α) where
  zero := ε
  assoc := by sorry
  unit_left := Str.concat_empty_left
  unit_right := Str.concat_empty_right
