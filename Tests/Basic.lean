import Mathlib.Tactic

example (P Q :Prop): P ∨ Q → Q ∨ P := by
  intro h
  --intro g
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq


example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  -- direct
  intro h nq p
  exact nq (h p)


example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  -- logical equivalences
  intro h nq
  have nhq := by
    exact not_or_of_imp h
  rcases nhq with hnp | hq
  . exact hnp
  . exfalso
    contradiction
