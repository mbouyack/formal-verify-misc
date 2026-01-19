import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.NormNum.Basic

def triangle (n : ℕ) : ℕ := (n * (n + 1)) / 2

@[simp] theorem triangle_zero : triangle 0 = 0 := rfl

-- Show that the formula given above for triangle numbers
-- matches the usual definition (sum of the first 'n' natural numbers)
theorem triangle_def (n : ℕ) : triangle n = ∑ i ∈ Finset.range (n + 1), i := by
  symm
  unfold triangle
  induction n
  case zero => rfl
  case succ n ih =>
    rw [Finset.sum_range_succ]
    -- Use the induction hypothesis
    rw [ih]
    have heven : 2 ∣ n * (n + 1) :=
      Nat.two_dvd_mul_add_one n
    have heven' : 2 ∣ (n + 1) * (n + 2) :=
      Nat.two_dvd_mul_add_one (n + 1)
    -- Multiply both sides by two
    apply (@Nat.mul_right_inj 2 _ _ (by norm_num)).mp
    rw [mul_add]
    -- Cancel multiplication with division on the left-hand side
    rw [Nat.mul_div_cancel' heven]
    rw [← add_mul]
    rw [mul_comm]
    rw [add_assoc]
    rw [one_add_one_eq_two]
    -- Cancel multiplication with division on the right-hand side
    rw [Nat.mul_div_cancel' heven']

-- Triangle number 'n+1' is equal to triangle number 'n', plus 'n+1'
theorem triangle_recurrence (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
  rw [triangle_def]
  rw [Finset.sum_range_succ]
  rw [← triangle_def]
