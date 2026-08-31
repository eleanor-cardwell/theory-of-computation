import Automata.Set

variable {σ: Type u} {τ: Type v}

inductive Str (σ: Type u) where
| empty: Str σ
| append: σ → Str σ → Str σ

instance: Bot (Str σ) := ⟨Str.empty⟩ -- allows ⊥ notation for empty string

notation "ε" => Str.empty -- alternatively use ε

instance: HAdd σ (Str σ) (Str σ) := ⟨Str.append⟩ -- allows + notation for adding characters to strings

def Str.singleton (a: σ): Str σ :=
 append a empty

def Str.length (s: Str σ): Nat :=
 match s with
 | empty => 0
 | append _ t => 1 + t.length

def Str.concat (s t: Str σ): Str σ :=
 match s with
 | empty => t
 | append a s' => a + (concat s' t)

instance: Add (Str σ) := ⟨Str.concat⟩ --  allows + notation for adding strings

-- TODO: show (s + t).length = s.length + t.length (length is a monoid homomorphism to N)

-- flatten a string of strings to one strong, e.g. [[1,2],[3]] => [1,2,3].
def Str.flatten (s: Str (Str σ)): Str σ :=
  match s with
  | empty => empty
  | append h t => h + flatten t

def Str.map (f: σ → τ) (s: Str σ): Str τ :=
  match s with
  | empty => empty
  | append h t => f h + Str.map f t

abbrev Language (σ: Type u): Type u :=
 Set (Str σ)

-- instance (σ: Type u): CoeSort (Language σ) (Type u) where
--  coe L := Subtype L
