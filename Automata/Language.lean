import Automata.Set

variable {α: Type u} {τ: Type v}

inductive Str (α: Type u) where
| empty: Str α
| append: α → Str α → Str α

instance: Bot (Str α) := ⟨Str.empty⟩ -- allows ⊥ notation for empty string

notation "ε" => Str.empty -- alternatively use ε

instance: HAdd α (Str α) (Str α) := ⟨Str.append⟩ -- allows + notation for adding characters to strings

def Str.singleton (a: α): Str α :=
 append a empty

def Str.length (s: Str α): Nat :=
 match s with
 | empty => 0
 | append _ t => 1 + t.length

def Str.concat (s t: Str α): Str α :=
 match s with
 | empty => t
 | append a s' => a + (concat s' t)

instance: Add (Str α) := ⟨Str.concat⟩ --  allows + notation for adding strings

-- TODO: show (s + t).length = s.length + t.length (length is a monoid homomorphism to N)

-- flatten a string of strings to one strong, e.g. [[1,2],[3]] => [1,2,3].
def Str.flatten (s: Str (Str α)): Str α :=
  match s with
  | empty => empty
  | append h t => h + flatten t

def Str.map (f: α → τ) (s: Str α): Str τ :=
  match s with
  | empty => empty
  | append h t => f h + Str.map f t

abbrev Language (α: Type u): Type u :=
 Set (Str α)

-- instance (α: Type u): CoeSort (Language α) (Type u) where
--  coe L := Subtype L
