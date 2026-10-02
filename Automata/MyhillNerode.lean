import Automata.Automaton
import Automata.Complexity

variable {α: Type u}

/-
Given a language L ⊆ Σ*, for each string s define

  L(s) = {t ∈ Σ* | s + t ∈ L}

Then the Nerode automaton is defined by:
- state set Q = {L(s) | s ∈ Σ*}
- initial state q₀ := L(ε) = L
- transition function δ(L(s), a) = L(s + a)
- final set F = {L(s) | ε ∈ L(s)}
-/
def Postfix (L: Language α) (s: Str α): Language α :=
  λ t ↦ s + t ∈ L

theorem Postfix.empty (L: Language α): Postfix L ε = L := by
  funext _
  unfold Postfix
  rw [Str.concat_empty_left]
  rfl

noncomputable def Nerode (L: Language α): Automaton α := {
  State := Set.range (Postfix L)
  transition := λ q a ↦ Set.range_map (Postfix L) (λ s ↦ s + a) q
  initial := Set.range_mem (Postfix L) ε
  final := λ q ↦ ε ∈ q.val
}

theorem Nerode.run_eq (L: Language α) (s: Str α): (Nerode L).run s = Set.range_mem (Postfix L) s := by
  induction s with
  | empty => rfl
  | append t a ih =>
    unfold Automaton.run
    rw [ih]
    unfold Nerode; simp
    apply Set.range_map_mem

theorem Nerode.language_eq (L: Language α): (Nerode L).language = L := by
  funext
  unfold Automaton.language
  rw [Nerode.run_eq]
  rfl



/-
TODO
· A language L is regular iff. the range of L (which sends a string to its 
  extension language) is finite
· The complexity of the Nerode automaton is equal to the complexity of the 
  minimal DFA recognizing the language
· The minimal DFA is unique up to isomorphism (need automaton homomorphisms?)
-/
