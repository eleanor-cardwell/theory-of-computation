
import Automata.Language

class Monoid (α: Type u) extends Zero α, Add α where
  assoc (a b c: α): (a + b) + c = a + (b + c)
  unit_left (a: α): 0 + a = a
  unit_right (a: α): a + 0 = a

instance (α: Type u): Monoid (Str α) where
  zero := ⊥
  assoc := by sorry
  unit_left := by sorry
  unit_right := by sorry
