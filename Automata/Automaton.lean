import Automata.Set
import Automata.Language

variable {σ: Type u}

structure Automaton (σ: Type u) where
  State: Type v
  finite: Finite State
  transition: σ → State → State
  initial: State
  final: Set State

def Automaton.Run (A: Automaton σ) (S: Str σ): A.State :=
  match S with
  | Str.empty       => A.initial
  | Str.append s S' => A.transition s (A.Run S')

-- allows to write `A S` to mean `A.Run S`

instance: CoeFun (Automaton σ) (fun A => Str σ → A.State) := ⟨Automaton.Run⟩

def Automaton.Language (A: Automaton σ): Language σ :=
  λ S ↦ A.Run S ∈ A.final

theorem language_empty_if {A: Automaton σ} (h: A.final = ⊥): A.Language = ⊥ := by
  funext
  unfold Automaton.Language
  rw [h]
  rfl

theorem language_full_if {A: Automaton σ} (h: A.final = ⊤): A.Language = ⊤ := by
  funext
  unfold Automaton.Language
  rw [h]
  rfl

-- TODO: define the trivial automata with 1 state and which always/never accept respectively.
-- (why? idk)

def Automaton.Complement (A: Automaton σ): Automaton σ := {
  State := A.State
  finite := A.finite
  transition := A.transition
  initial := A.initial
  final := Set.Complement A.final
}

instance: Compl (Automaton σ) := ⟨Automaton.Complement⟩

theorem Automaton.Complement_run (M: Automaton σ): Mᶜ.Run = M.Run := by
  ext s
  induction s with
  | empty => rfl
  | append h t ih => calc
    Mᶜ.Run (h + t)
      = Mᶜ.transition h (Mᶜ t) := by rfl
    _ = Mᶜ.transition h (M t)  := by rw [ih]
    _ = M.transition h (M t)   := by rfl
    _ = M (h + t) := by rfl


theorem Automaton.Complement_language_compl (A: Automaton σ): Aᶜ.Language = (A.Language)ᶜ := by
  funext s
  simp
  calc
    s ∈ (Aᶜ).Language
    _ ↔ Aᶜ s ∈ Aᶜ.final := by rfl
    _ ↔ A s ∈ Aᶜ.final  := by rw [A.Complement_run]
    _ ↔ A s ∉ A.final   := by rfl
    _ ↔ s ∉ A.Language  := by rfl
