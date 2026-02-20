import SCI295MA.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

--note: reflexivity is the axiom that 1 = 1, or 0 = 0, true by defition
theorem one_is_succ_zero (n : ℕ) : (1 : ℕ) = Nat.succ (0 : ℕ) := by {
  rfl
}

theorem inductive_step_for_add_zero (n : ℕ) : (n + 0 = n) → ((n+1) + 0 = (n+1)) := by {
  exact fun a ↦ (fun {m k n} ↦ Nat.add_left_inj.mpr) rfl
}

theorem add_zero (n : Nat) : n + 0 = n := by {
  induction n with
  | zero =>
    -- Base case: 0 + 0 = 0
    rfl
  | succ n ih =>
    -- Inductive step: (n + 1) + 0 = (n + 1)
    -- ih is the inductive hypothesis: n + 0 = n
    exact inductive_step_for_add_zero n ih
}

theorem transitivity (a b c : ℕ) : (a=b) ∧ (b=c) → (a=c) := by {
  intro h
  rcases h with ⟨ hl,hr ⟩
  rw [hl]
  rw [hr]
}

theorem subtraction_not_associative321 : (3 - 2) - 1 ≠ 3 - (2 - 1) := by {
  simp --automatic tactic
}

theorem addition_is_associative (a b c : ℕ) : (a + b) + c = a + (b + c) := by {
  exact Nat.add_assoc a b c
}

theorem addition_is_commutative (a b c : ℕ) : a + b + c = b + a + c := by {
  refine Nat.add_left_inj.mpr ?_
  exact Nat.add_comm a b
}

lemma mult_by_zero_makes_comm (a b c : ℕ) : c = 0 → a*b*c = b*a*c := by {
  intro hzero
  linarith
}

theorem multiplication_is_commutative3 (a b c : ℕ) : a*b*c = b*a*c := by {
  by_cases h : c = 0

}

-- Define the new inductive type "Drum"
inductive Drum where
  | kick  : Drum
  | snare : Drum
  | hat : Drum
  deriving Repr -- This allows us to print/inspect the type

-- Define a song as a List of Drum
def mySong1 : List Drum :=
  [Drum.hat, Drum.kick, Drum.hat, Drum.snare,
   Drum.hat, Drum.kick, Drum.snare, Drum.snare]

--make another type for Diggeridoo and laser and other

--make another song as a List
