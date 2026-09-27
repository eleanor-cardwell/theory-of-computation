import Automata.Language
import Automata.NDA

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
  | Regex.empty       => Set.empty
  | Regex.singleton a => Set.singleton (Str.singleton a)
  | Regex.union S T   => S.toLanguage ∪ T.toLanguage
  | Regex.concat S T  => Language.concat S.toLanguage T.toLanguage
  | Regex.star S      => Language.star S.toLanguage

/-
We define a regular language to be a language which is the set of strings
matched by a regular expression.
-/
def Language.regular (L: Language α): Prop :=
  ∃ R: Regex α, R.toLanguage = L

/-
todo:
· show the full language is regular if alphabet is finite
· a ∈ L for all a ∈ Σ ↔ L* = full
-/

def NDA.empty (α: Type u): NDA α := {
  State := Fin 1
  transition := λ _ _ ↦ Set.singleton 0
  initial := 0
  final := Set.empty
}

def NDA.singleton (α: Type u) [DecidableEq α] (a₀: α): NDA α := {
  State := Fin 2
  transition := λ q a ↦
    match q with
    | 0 => if a = a₀ then Set.singleton 1 else Set.empty
    | 1 => Set.empty
  initial := 0
  final := Set.singleton 1
}

def NDA.union {α: Type u} (A₁ A₂: NDA α): NDA α := {
  State := A₁.State × A₂.State
  transition := λ q a ↦ Set.prod (A₁.transition q.1 a) (A₂.transition q.2 a)
  initial := (A₁.initial, A₂.initial)
  final := Set.prod A₁.final A₂.final
}

-- todo remove  
open Classical

def NDA.concat {α: Type u} (A₁ A₂: NDA α): NDA α := {
  State := A₁.State ⊕ A₂.State
  transition := λ q a ↦
    match q with
    | Sum.inl q =>
      if (A₁.transition q a ∩ A₁.final).Nonempty then
        Set.inl (A₁.transition q a) ∪ Set.inr (Set.singleton A₂.initial)
      else
        Set.inl (A₁.transition q a)
    | Sum.inr q => Set.inr (A₂.transition q a)
  initial := Sum.inl A₁.initial
  final := Set.inr A₂.final
}

def NDA.star {α: Type u} (A: NDA α): NDA α := {
  State := A.State
  transition := λ q a ↦
    let S := A.transition q a
    if (S ∩ A.final).Nonempty then
      S ∪ Set.singleton A.initial
    else
      S
  initial := A.initial
  final := A.final
}

theorem Kleene.part1 (α: Type u) [DecidableEq α] {L: Language α} (hL: L.regular): ∃ A: NDA.{u, 0} α, (A.finite ∧ A.language = L) := by
  obtain ⟨R, hR⟩ := hL
  subst L
  induction R with
  | empty =>
    exists NDA.empty α
    sorry
  | singleton a =>
    exists NDA.singleton α a
    sorry
  | union R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, h₁⟩ := ih₁
    obtain ⟨A₂, h₂⟩ := ih₂
    exists NDA.union A₁ A₂
    constructor
    -- use finite sum of cardinals
    sorry
    sorry
  | concat R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, h₁⟩ := ih₁
    obtain ⟨A₂, h₂⟩ := ih₂
    exists NDA.concat A₁ A₂
    constructor
    sorry
    sorry
  | star R ih =>
    obtain ⟨A, h⟩ := ih
    exists NDA.star A
    constructor
    exact h.1
    sorry
