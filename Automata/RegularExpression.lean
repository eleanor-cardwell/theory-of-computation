import Automata.Language

variable {α: Type u}



/-
A regular expression over an alphabet α is defined inductively as either
· the empty expression;
· the singleton expression for a given symbol;
· the union of two expressions;
· the concatenation of two expressions; or
· the kleene star of an expression.
-/
inductive Regex (α: Type u) where
| empty
| singleton (a: α)
| union:  Regex α → Regex α → Regex α
| concat: Regex α → Regex α → Regex α
| star:   Regex α → Regex α

/-
Given a regular expression over α, we can obtain a language over α by forming
the set of strings the expression "matches".
-/
def Regex.toLanguage (R: Regex α): Language α :=
  match R with
  | Regex.empty => λ _ ↦ False
  | Regex.singleton a => λ s ↦ s = Str.singleton a
  | Regex.union S T => S.toLanguage ∪ T.toLanguage
  | Regex.concat S T => λ r ↦ ∃ s ∈ S.toLanguage, ∃ t ∈ T.toLanguage, r = s + t
  | Regex.star S => λ s ↦ ∃ t: Str S.toLanguage, s = Str.flatten (Str.map (λ x ↦ x.val) t)

/-
We define a regular language to be a language which is the set of strings
matched by a regular expression.
-/
def Language.Regular (L: Language α): Prop :=
  ∃ R: Regex α, R.toLanguage = L

/-
todo:
· show the full language is regular if alphabet is finite
· a ∈ L for all a ∈ Σ ↔ L* = full
-/
