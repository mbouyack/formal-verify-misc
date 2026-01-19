import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum.Basic
import FormalVerifyMisc.Common

def solve_slow (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  (if 3 ∣ n ∨ 5 ∣ n then n else 0) + solve_slow (n - 1)

-- Let 'f' be the sum of natural numbers up to 'n' divisible by 'k'
def f (n k : ℕ) : Nat := k * (triangle (n / k))
def solve_fast (n : ℕ) : Nat := f n 3 + f n 5 - f n 15

#eval solve_slow 999
#eval solve_fast 999

-- Define the set of positive integers up to 'n' divisible by 'k'
def S (n k : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun a ↦ a ≠ 0 ∧ k ∣ a)

-- Define the set of positive integers up to 'n' divisible by 3 or 5
def T (n : Nat) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun a ↦ a ≠ 0 ∧ (3 ∣ a ∨ 5 ∣ a))

-- Prove the sum of the elements of S
lemma sum_S_eq_f (n k : Nat) : ∑ a ∈ S n k, a = f n k := by
  unfold S f
  rw [Finset.sum_filter]
  induction n
  case zero => simp
  case succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    split_ifs with hn
    · rw [Nat.succ_div_of_dvd hn.2]
      rw [triangle_recurrence]
      rw [mul_add]
      rw [← Nat.succ_div_of_dvd hn.2]
      rw [Nat.mul_div_cancel' hn.2]
    · push_neg at hn
      have kndiv : ¬k ∣ (n + 1) := hn (Nat.add_one_ne_zero n)
      rw [Nat.succ_div_of_not_dvd kndiv]
      simp

lemma T_eq_union (n : ℕ) : T n = (S n 3 ∪ S n 5) := by
  unfold S T
  ext a
  constructor
  · simp
    intro alt anz advd
    rcases advd with lhs | rhs
    · exact Or.inl ⟨alt, anz, lhs⟩
    · exact Or.inr ⟨alt, anz, rhs⟩
  · simp
    intro h
    rcases h with ⟨alt, anz, lhs⟩ | ⟨alt, anz, rhs⟩
    · exact ⟨alt, anz, Or.inl lhs⟩
    · exact ⟨alt, anz, Or.inr rhs⟩

lemma S3_inter_S5_eq_S15 (n : ℕ) : S n 3 ∩ S n 5 = S n 15 := by
  unfold S
  ext a
  constructor
  · simp
    intro alt anz dvd3 _ _ dvd5
    use alt, anz
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl dvd3 dvd5
  · simp
    intro alt anz dvd15
    constructor
    · exact ⟨alt, anz, dvd_trans (by norm_num) dvd15⟩
    · exact ⟨alt, anz, dvd_trans (by norm_num) dvd15⟩

-- Prove that the sum of the elements in 'T' is the same as the "slow" solution
theorem T_sum_eq_slow (n : ℕ) : ∑ a ∈ T n, a = solve_slow n := by
  unfold T
  induction n
  case zero =>
    unfold solve_slow
    simp
  case succ n ih =>
    rw [Finset.sum_filter] at *
    rw [Finset.sum_range_succ]
    rw [ih]
    nth_rw 2 [solve_slow]
    rw [add_comm]; simp

-- Prove that the sum of the elements in 'T' is the same as the "fast" solution
theorem T_sum_eq_fast (n : ℕ) : ∑ a ∈ T n, a = solve_fast n := by
  unfold solve_fast; symm
  apply Nat.sub_eq_of_eq_add
  rw [T_eq_union]
  repeat rw [← sum_S_eq_f _ _]
  rw [← S3_inter_S5_eq_S15]
  rw [Finset.sum_union_inter]
