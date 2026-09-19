import Automata.Language

variable {α: Type u}

inductive Regex (α: Type u) where
| empty
| singleton (a: α)
| union:  Regex α → Regex α → Regex α
| concat: Regex α → Regex α → Regex α
| star:   Regex α → Regex α

def Regex.toLanguage (R: Regex α): Language α :=
  match R with
  | Regex.empty => fun _ => False
  | Regex.singleton a => fun s => s = Str.singleton a
  | Regex.union S T => S.toLanguage ∪ T.toLanguage
  | Regex.concat S T => fun r => ∃ s ∈ S.toLanguage, ∃ t ∈ T.toLanguage, r = s + t
  | Regex.star S => fun s => ∃ t: Str S.toLanguage, s = Str.flatten (Str.map (fun x => x.val) t)

def Language.Regular (L: Language α): Prop :=
  ∃ R: Regex α, R.toLanguage = L
