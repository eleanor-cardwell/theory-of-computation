import Automata.Set

variable {α: Type u} {β: Type v}

inductive Str (α: Type u) where
| empty: Str α
| append: Str α → α → Str α

instance: Bot (Str α) := ⟨Str.empty⟩ -- allows ⊥ notation for empty string

notation "ε" => Str.empty -- alternatively use ε

instance: HAdd (Str α) α (Str α) := ⟨Str.append⟩ -- allows + notation for adding characters to strings

def Str.singleton (a: α): Str α :=
 append empty a

-- maybe define prepend(a, s) = reverse(append(reverse(s), a))?
def Str.prepend (a: α) (s: Str α): Str α :=
 sorry

def Str.concat (s t: Str α): Str α :=
 match s with
 | empty => t
 | append s' a => (concat s' t) + a

instance: Add (Str α) := ⟨Str.concat⟩ --  allows + notation for adding strings

def Str.reverse (s: Str α): Str α :=
  sorry

-- allows s⁻¹ to denote reverse of string
instance: Inv (Str α) := ⟨Str.reverse⟩

def Str.length (s: Str α): Nat :=
 match s with
 | empty => 0
 | append t _ => t.length + 1

theorem Str.length_prepend (a: α) (s: Str α): length (prepend a s) = 1 + length s := by
  sorry

theorem Str.length_concat (s t: Str α): length (s + t) = length s + length t := by
  sorry

theorem Str.length_reverse (s: Str α): length s⁻¹ = length s := by
  sorry

-- TODO: show (s + t).length = s.length + t.length (length is a monoid homomorphism to N)

-- flatten a string of strings to one strong, e.g. [[1,2],[3]] => [1,2,3].
def Str.flatten (s: Str (Str α)): Str α :=
  match s with
  | empty => empty
  | append t h => h + flatten t

def Str.map (f: α → β) (s: Str α): Str β :=
  match s with
  | empty => empty
  | append t h => Str.map f t + f h

abbrev Language (α: Type u): Type u :=
 Set (Str α)

-- instance (α: Type u): CoeSort (Language α) (Type u) where
--  coe L := Subtype L

def Language.star (L: Language α): Language α :=
  sorry
