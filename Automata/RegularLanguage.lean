import Automata.Language

variable {σ: Type u}

inductive RegularLanguage (σ: Type u) where
| empty
| singleton (a: σ)
| union:  RegularLanguage σ → RegularLanguage σ → RegularLanguage σ
| concat: RegularLanguage σ → RegularLanguage σ → RegularLanguage σ
| star:   RegularLanguage σ → RegularLanguage σ

def RegularLanguage.toLanguage (R: RegularLanguage σ): Language σ :=
  match R with
  | RegularLanguage.empty => fun _ => False
  | RegularLanguage.singleton a => fun s => s = Str.singleton a
  | RegularLanguage.union A B => A.toLanguage ∪ B.toLanguage
  | RegularLanguage.concat A B => fun s => ∃ a ∈ A.toLanguage, ∃ b ∈ B.toLanguage, s = a + b
  | RegularLanguage.star A => fun s => ∃ t: Str A.toLanguage, s = Str.flatten (Str.map (fun x => x.val) t)

def Language.Regular (L: Language σ): Prop :=
  ∃ R: RegularLanguage σ, R.toLanguage = L


/-

Theorem: every finite language is regular.

Proof: suppose the language L is finite.
Let n be the maximal length of words in L.

Define an automaton with:
  State := {s ∈ Str σ | length(s) ≤ n} ∪ {FAIL}
  transition(a, q) = { if length(q) < n then a + q else FAIL }
  initial := Str.empty
  final := L

-- -/
-- theorem finite_language_regular {σ: Type u} (hσ: Finite σ) (L: Language σ) (hL: Finite L): L.Regular := by
--   sorry


-- -- The complement of a regular language is regular.

-- theorem regular_language_compl_regular {σ: Type u} {L: Language σ} (hL: L.Regular): Language.Regular L.Complement := by
--   obtain ⟨M, hM⟩ := hL
--   exists M.Complement
--   rw [←hM]
--   exact FiniteAutomaton.Complement_language_compl M
