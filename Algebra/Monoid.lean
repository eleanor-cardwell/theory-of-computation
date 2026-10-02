class Monoid (α: Type u) extends Zero α, Add α where
  assoc (a b c: α): (a + b) + c = a + (b + c)
  unit_left (a: α): 0 + a = a
  unit_right (a: α): a + 0 = a
