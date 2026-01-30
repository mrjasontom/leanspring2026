import SCI295MA.Basic
import Mathlib.Data.Nat.Basic
theorem zeroPlusNisN (n : ℕ) : 0 + n =  n := by {
  exact Nat.zero_add n
}

theorem transitivity (a b c : ℕ) : (a=b) ∧ (b=c) → (a=c) := by {
  intro h
  rcases h with ⟨ hl,hr ⟩
  rw [hl]
  rw [hr]
}
