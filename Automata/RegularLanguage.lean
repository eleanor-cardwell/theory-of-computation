import Automata.Language

variable {α: Type u}

inductive RegularExp (α: Type u) where
| empty
| singleton (a: α)
| union:  RegularExp α → RegularExp α → RegularExp α
| concat: RegularExp α → RegularExp α → RegularExp α
| star:   RegularExp α → RegularExp α

def RegularExp.toLanguage (R: RegularExp α): Language α :=
  match R with
  | RegularExp.empty => fun _ => False
  | RegularExp.singleton a => fun s => s = Str.singleton a
  | RegularExp.union A B => A.toLanguage ∪ B.toLanguage
  | RegularExp.concat A B => fun s => ∃ a ∈ A.toLanguage, ∃ b ∈ B.toLanguage, s = a + b
  | RegularExp.star A => fun s => ∃ t: Str A.toLanguage, s = Str.flatten (Str.map (fun x => x.val) t)

def Language.Regular (L: Language α): Prop :=
  ∃ R: RegularExp α, R.toLanguage = L


/-

Theorem: every finite language is regular.

Proof: suppose the language L is finite.
Let n be the maximal length of words in L.

Define an automaton with:
  State := {s ∈ Str α | length(s) ≤ n} ∪ {FAIL}
  transition(a, q) = { if length(q) < n then a + q else FAIL }
  initial := Str.empty
  final := L

-- -/
-- theorem finite_language_regular {α: Type u} (hα: Finite α) (L: Language α) (hL: Finite L): L.Regular := by
--   sorry


-- -- The complement of a regular language is regular.

-- theorem regular_language_compl_regular {α: Type u} {L: Language α} (hL: L.Regular): Language.Regular L.Complement := by
--   obtain ⟨M, hM⟩ := hL
--   exists M.Complement
--   rw [←hM]
--   exact FiniteAutomaton.Complement_language_compl M
