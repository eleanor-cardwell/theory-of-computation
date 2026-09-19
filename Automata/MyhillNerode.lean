import Automata.Automaton

variable {α: Type u}

/-

# Nerode automata

Given a language L ⊆ Σ*, for each string s define

L(s) = {t ∈ Σ* | s + t ∈ L}

Then define an automata with state set

Q = {L(s) | s ∈ Σ*}

Define the initial state

q₀ := L(ε) = L

and the transition function δ: Q x Σ → Q

δ(L(s), a) = L(s + a)

δ(S, a) = {t | a + t ∈ S}

-/

/-

Σ = {x}

L = {ε, xx, xxxx, ...}

L(ε) = L
L(x) = {t | x + t ∈ L}
     = {x, xxx, xxxxx, ...}
L(xx) = {ε, xx, xxxx, ... } = L

Q = {L(ε), L(x)}

-/

def PostfixLanguage (L: Language α) (s: Str α): Language α :=
  fun t => s + t ∈ L

theorem PostfixLanguage.empty (L: Language α): PostfixLanguage L ε = L := by
  funext _
  unfold PostfixLanguage
  rw [Str.concat_empty_left]
  rfl
  
noncomputable def NerodeAutomata (L: Language α): Automaton α := {
  State := Set.range (PostfixLanguage L)
  transition := λ ⟨_, hS⟩ a ↦
    let s := Classical.choose hS
    ⟨PostfixLanguage L (s + a), by exists (s + a)⟩
  initial := ⟨L, by exists ε; exact PostfixLanguage.empty L⟩
  final := λ ⟨S, _⟩ ↦ ε ∈ S
}
/-

((NerodeAutomata L).run (t.append h))
= A.transition (A.run t) h
= A.transition (PostfixLanguage L t) h
= PostfixLanguage L (t + h)



= PostfixLanguage L (t.append h)

-/
theorem NerodeAutomata.run_eq (L: Language α) (s: Str α): (NerodeAutomata L).run s = ⟨PostfixLanguage L s, by exists s⟩ := by
  apply Subtype.ext
  simp
  induction s with
  | empty => 
    rw [PostfixLanguage.empty]
    rfl
  | append t h ih => 
    calc
      ((NerodeAutomata L).run (t.append h)).val
        = ((NerodeAutomata L).transition ((NerodeAutomata L).run t) h).val := by rfl
      _ = PostfixLanguage L (t.append h) := by sorry

theorem NerodeAutomata.sound (L: Language α): (NerodeAutomata L).language = L := by
  funext s
  simp
  calc
    s ∈ (NerodeAutomata L).language 
    _ ↔ ε ∈ ((NerodeAutomata L).run s).val := by rfl
    _ ↔ ε ∈ PostfixLanguage L s := by rw [NerodeAutomata.run_eq]
    _ ↔ s + ε ∈ L := by rfl
    _ ↔ s ∈ L := by rw [Str.concat_empty_right]
