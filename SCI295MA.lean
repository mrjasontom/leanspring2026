import SCI295MA.Basic
import Mathlib.Data.Nat.Basic

--note: reflexivity is the axiom that 1 = 1, or 0 = 0, true by defition
theorem one_is_succ_zero (n : ℕ) : (1 : ℕ) = Nat.succ (0 : ℕ) := by {
  rfl
}

theorem inductive_step_for_add_zero (n : ℕ) : (n + 0 = n) → ((n+1) + 0 = (n+1)) := by {

}

theorem add_zero (n : Nat) : n + 0 = n := by {
  induction n with
  | zero =>
    -- Base case: 0 + 0 = 0
    rfl
  | succ n ih =>
    -- Inductive step: (n + 1) + 0 = (n + 1)
    -- ih is the inductive hypothesis: n + 0 = n
    simp [Nat.add_succ, ih]
}

theorem transitivity (a b c : ℕ) : (a=b) ∧ (b=c) → (a=c) := by {
  intro h
  rcases h with ⟨ hl,hr ⟩
  rw [hl]
  rw [hr]
}
