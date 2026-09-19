import Basic.Set
import Basic.Monoid
import Automata.String

variable {α: Type u} {β: Type v}

abbrev Language (α: Type u): Type u :=
 Set (Str α)

def Language.union (L₁ L₂: Language α): Language α :=
  L₁ ∪ L₂

def Language.star (L: Language α): Language α :=
  sorry
