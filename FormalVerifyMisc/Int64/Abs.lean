import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.Basic
import FormalVerifyMisc.Int64.Basic

-- Int64.abs is not defined in a useful way and there seem to be no
-- relevant theorems. Intsead define a more useful version
def int64_abs (a : Int64) : Int64 :=
  if a < 0 then -a else a

-- The absolute value of -2^63 is still -2^63
theorem int64_abs_minval : int64_abs Int64.minValue = Int64.minValue := rfl

-- The absolute value operator can be moved across the 'toInt' conversion
-- as long as the value isn't -2^63
theorem int64_toInt_abs (a : Int64) (hlb : Int64.minValue < a) :
  (int64_abs a).toInt = |a.toInt| := by
  unfold int64_abs
  split_ifs with h
  · replace h := Int64.lt_iff_toInt_lt.mp h; simp at h
    rw [abs_of_neg h]
    exact int64_toInt_neg a hlb
  · replace h := Int64.le_iff_toInt_le.mp (Int64.not_lt.mp h); simp at h
    rw [abs_of_nonneg h]

@[simp] theorem int64_abs_zero : int64_abs 0 = 0 := rfl

-- The absolute value returns a non-negative integer (with one exception)
theorem int64_abs_nonneg (a : Int64) (hlb : Int64.minValue < a) :
  0 ≤ int64_abs a := by
  apply Int64.le_iff_toInt_le.mpr; simp
  rw [int64_toInt_abs a hlb]
  exact abs_nonneg a.toInt

-- The absolute value of a non-negative integer is that integer itself
theorem int64_abs_of_nonneg (a : Int64) (hnn : 0 ≤ a) : int64_abs a = a := by
  unfold int64_abs
  rw [if_neg (Int64.not_lt.mpr hnn)]

-- The absolute value of a non-positive integer is the negation of that integer
theorem int64_abs_of_nonpos (a : Int64) (hnp : a ≤ 0) : int64_abs a = -a := by
  unfold int64_abs
  by_cases h : a = 0
  · subst h
    rw [if_neg (by simp)]
    rfl
  push_neg at h
  rw [if_pos (Int64.lt_of_le_of_ne hnp h)]

-- The absolute value of the negation is equal to the absolute value
@[simp] theorem int64_abs_neg (a : Int64) : int64_abs (-a) = int64_abs a := by
  by_cases h : 0 ≤ a
  · rw [int64_abs_of_nonneg a h]
    rw [int64_abs_of_nonpos (-a) ((Int64.neg_nonpos_iff a).mpr (Or.inr h))]
    simp
  have hnp := Int64.le_of_lt (Int64.not_le.mp h)
  rw [int64_abs_of_nonpos a hnp]
  by_cases hmv : Int64.minValue = a
  · subst hmv; rfl
  have hlb : Int64.minValue < a := Int64.lt_of_le_of_ne (Int64.minValue_le a) hmv
  exact int64_abs_of_nonneg (-a) (int64_neg_nonneg_of_nonpos a hlb hnp)

-- The absolute value is equal to either the integer itself, or its negation
theorem int64_abs_eq_self_or_neg (a : Int64) : int64_abs a = a ∨ int64_abs a = -a := by
  by_cases h : 0 ≤ a
  · exact Or.inl (int64_abs_of_nonneg a h)
  · exact Or.inr (int64_abs_of_nonpos a (Int64.le_of_lt (Int64.not_le.mp h)))

theorem int64_abs_eq_abs_iff (a b : Int64) :
  int64_abs a = int64_abs b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    rcases int64_abs_eq_self_or_neg a with ha₀ | ha₁
    · rw [ha₀] at h
      rcases int64_abs_eq_self_or_neg b with hb₀ | hb₁
      · left
        rwa [hb₀] at h
      · right
        rwa [hb₁] at h
    · rw [ha₁] at h
      apply Int64.neg_inj.mpr at h
      simp at h
      rcases int64_abs_eq_self_or_neg b with hb₀ | hb₁
      · right
        rwa [hb₀] at h
      · left
        rw [hb₁] at h
        simp at h
        assumption
  · rintro (h₀ | h₁)
    · subst h₀; rfl
    · subst h₁
      exact int64_abs_neg b

-- If |a| < |b| then a % b = a
-- Note that if either a or b is -2^63 this may not hold
theorem int64_mod_of_abs_lt (a b : Int64) (hlt : int64_abs a < int64_abs b)
  (hlba : Int64.minValue < a) (hlbb : Int64.minValue < b) : a % b = a := by
  apply Int64.lt_iff_toInt_lt.mp at hlt
  rw [int64_toInt_abs a hlba, int64_toInt_abs b hlbb] at hlt
  apply Int64.toInt_inj.mp; simp
  by_cases hann : 0 ≤ a.toInt
  · rw [abs_of_nonneg hann] at hlt
    by_cases hbnn : 0 ≤ b.toInt
    · rw [abs_of_nonneg hbnn] at hlt
      exact Int.tmod_eq_of_lt hann hlt
    · push_neg at hbnn
      rw [← Int.tmod_neg a.toInt b.toInt]
      rw [abs_eq_neg_self.mpr (Int.le_of_lt hbnn)] at hlt
      exact Int.tmod_eq_of_lt hann hlt
  · push_neg at hann
    apply Int.neg_inj.mp
    rw [← Int.neg_tmod]
    rw [abs_eq_neg_self.mpr (Int.le_of_lt hann)] at hlt
    by_cases hbnn : 0 ≤ b.toInt
    · rw [abs_of_nonneg hbnn] at hlt
      exact Int.tmod_eq_of_lt (le_of_lt (neg_pos_of_neg hann)) hlt
    · push_neg at hbnn
      rw [← Int.tmod_neg]
      rw [abs_eq_neg_self.mpr (Int.le_of_lt hbnn)] at hlt
      exact Int.tmod_eq_of_lt (le_of_lt (neg_pos_of_neg hann)) hlt
