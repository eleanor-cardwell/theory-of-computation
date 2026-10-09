import Automata.Kleene

/-
For a language L and a natural number p, define a string s ∈ L to be 
"decomposable" if it satisfies the following property:

s can be written as the concatenation of three strings, xyz, where
· |y| ≥ 1;
· |xy| ≤ p; and
· for all n ≥ 0, xy^nz ∈ L. 
-/
def decomposable {α: Type} (L: Language α) (s: Str α) (p: Nat): Prop :=
  ∃ x y z: Str α, (s = x + y + z) 
    ∧ (y.length ≥ 1) 
    ∧ ((x + y).length ≤ p) 
    ∧ (∀ n: Nat, x + y^n + z ∈ L)



/-
The pumping lemma for regular languages states that for a given regular language
L, there exists a positive natural number p such that any string s ∈ L of
length at least p is "decomposable".

Proof:

Let L be a regular language. Then there exists some deterministic finite
automata M recognizing L.

Take the complexity of M to be our pumping length, p. (Note p ≥ 1 since we can
always take the initial state to show nonempty)

Let s ∈ L with |s| ≥ p. 

Notice that M has p states, one of which is the initial state. So, after
consuming p characters from s, the machine will have transitioned through p + 1
states. Thus s will always have at least 1 repeated state in the path it traces
through the machine (via pigeonhole principle). Let q_r be said state.

Consider the sequence of characters read between the first instance of q_r
and the second instance of q_r. Take this to be our y string, and any previous
characters to be our x, and any later characters to be our z.

· Do we have |y| ≥ 1?
Yes: The state q_r is reached twice, so at least 1 character must be read to
transition to it the second time.

· Do we have |xy| ≤ p? 
Yes: this follows from the fact that both instances of q_r must occur within
reading p characters.

· Do we have xy^nz ∈ L for all n ≥ 0? 
Yes: Reading x takes the machine to q_r. Then, reading y takes the machine back
to q_r: this can be repeated 0 times (the machine is already in q_r), or any
number of times, and it will always loop back to q_r. Then, z takes the 
machine to the same final state as

-/

def Str.symbol_at {α: Type} (s: Str α): Fin s.length → α := by
  match s with
  | empty => 
    intro n
    have h₁ := @length_empty α
    have h₂ := Fin.pos n
    contradiction
  | append t a => 
    intro ⟨n, hn⟩
    by_cases h: n < t.length
    · exact Str.symbol_at t ⟨n, h⟩
    · exact a

def Automaton.state_sequence {α: Type} (M: Automaton α) (s: Str α): Fin (s.length + 1) → M.State := by
  match s with
  | Str.empty => 
    intro _
    exact M.initial
  | Str.append t a =>
    intro ⟨n, hn⟩
    by_cases h: n = s.length
    · exact M.transition (M.run t) a
    · have hn₂: n < t.length + 1 := by sorry
      exact M.transition (state_sequence M t ⟨n, hn₂⟩) a

def Str.from_to {α: Type} (s: Str α) {n m: Fin (s.length)}: Str α := by
  sorry

theorem pigeonhole_principle (n: Nat) (f: Fin (n + 1) → Fin n): ∃ n₁ n₂, n₁ ≠ n₂ ∧ f n₁ = f n₂ := by
  sorry
  
theorem pigeonhole_principle₂ {n m: Nat} (h: n > m) (f: Fin n → Fin m): ∃ n₁ n₂, n₁ ≠ n₂ ∧ f n₁ = f n₂ := by
  sorry

theorem pumping_lemma {α: Type} {L: Language α} (h: Language.regular L): ∃ p ≥ 1, ∀ s ∈ L, s.length ≥ p → decomposable L s p := by
  have ⟨M, hM₁, hM₂⟩ := Kleene'sTheorem.mp h
  let ⟨p, f, hf⟩ := Automaton.size hM₁
  exists p
  constructor
  · exact Fin.pos (f M.initial)
  · intro s hs₁ hs₂
    have F := Automaton.state_sequence M s
    have h₁: s.length + 1 > p := by exact Nat.lt_succ_of_le hs₂
    have ⟨n₁, n₂, hn₁, hn₂⟩ := pigeonhole_principle₂ h₁ (f ∘ F)
    have h₂: F n₁ = F n₂ := by sorry -- bijection
    let q := F n₁
    let x: Str α := sorry
    let y: Str α := sorry
    let z: Str α := sorry
    exists x
    exists y
    exists z
    repeat' constructor
    · sorry
    · sorry
    · sorry
    · sorry
 
