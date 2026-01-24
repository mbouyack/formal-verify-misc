import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.Basic
import FormalVerifyMisc.Int32.Basic

-- Int32.abs is not defined in a useful way and there seem to be no
-- relevant theorems. Intsead define a more useful version
def int32_abs (a : Int32) : Int32 :=
  if a < 0 then -a else a

-- The absolute value of -2^31 is still -2^31
@[simp] theorem int32_abs_minval : int32_abs Int32.minValue = Int32.minValue := rfl

-- The absolute value operator can be moved across the 'toInt' conversion
-- as long as the value isn't -2^31
theorem int32_toInt_abs (a : Int32) (hlb : Int32.minValue < a) :
  (int32_abs a).toInt = |a.toInt| := by
  unfold int32_abs
  split_ifs with h
  · replace h := Int32.lt_iff_toInt_lt.mp h; simp at h
    rw [abs_of_neg h]
    exact int32_toInt_neg a hlb
  · replace h := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp h); simp at h
    rw [abs_of_nonneg h]

theorem int32_toInt_abs_lt (a : Int32) : (int32_abs a).toInt < 2^31 := by
  by_cases hmv : a = Int32.minValue
  · subst hmv; simp
  rename' hmv => hnmv; push_neg at hnmv
  rw [int32_toInt_abs _ (int32_minval_lt_of_ne_minval _ hnmv.symm)]
  apply abs_lt.mpr
  constructor
  · apply lt_of_le_of_ne (int32_minval_le_toInt a)
    contrapose! hnmv
    apply Int32.toInt_inj.mp
    exact hnmv.symm
  · exact int32_toInt_lt_maxval a

@[simp] theorem int32_abs_zero : int32_abs 0 = 0 := rfl

theorem int32_zero_of_abs_zero
  (a : Int32) (hz : int32_abs a = 0) : a = 0 := by
  unfold int32_abs at hz
  split_ifs at hz with h
  · apply Int32.neg_inj.mp
    rw [hz]; rfl
  · assumption

-- The absolute value returns a non-negative integer (with one exception)
theorem int32_abs_nonneg (a : Int32) (hlb : Int32.minValue < a) :
  0 ≤ int32_abs a := by
  apply Int32.le_iff_toInt_le.mpr; simp
  rw [int32_toInt_abs a hlb]
  exact abs_nonneg a.toInt

theorem int32_abs_pos_of_ne_zero
  (a : Int32) (hlb : Int32.minValue < a) (hnz : a ≠ 0) : 0 < int32_abs a := by
  apply Int32.lt_of_le_of_ne (int32_abs_nonneg a hlb)
  contrapose! hnz
  exact int32_zero_of_abs_zero _ hnz.symm

-- The absolute value of a non-negative integer is that integer itself
theorem int32_abs_of_nonneg (a : Int32) (hnn : 0 ≤ a) : int32_abs a = a := by
  unfold int32_abs
  rw [if_neg (Int32.not_lt.mpr hnn)]

-- The absolute value of a non-positive integer is the negation of that integer
theorem int32_abs_of_nonpos (a : Int32) (hnp : a ≤ 0) : int32_abs a = -a := by
  unfold int32_abs
  by_cases h : a = 0
  · subst h
    rw [if_neg (by simp)]
    rfl
  push_neg at h
  rw [if_pos (Int32.lt_of_le_of_ne hnp h)]

-- An integer multiplied by its sign gives its absolute value
theorem int32_mul_sign_eq_abs (a : Int32) : a * int32_sign a = int32_abs a := by
  by_cases hneg : a < 0
  · rw [int32_abs_of_nonpos a (Int32.le_of_lt hneg)]
    rw [int32_sign_of_neg a hneg]
    rw [Int32.mul_neg]; simp
  by_cases hz : a = 0
  · subst hz; simp
  rename' hz => hnz; push_neg at hnz
  have hnn := Int32.not_lt.mp hneg
  rw [int32_abs_of_nonneg _ hnn]
  rw [int32_sign_of_pos a (Int32.lt_of_le_of_ne hnn hnz.symm)]
  simp

-- The absolute value of the negation is equal to the absolute value
@[simp] theorem int32_abs_neg (a : Int32) : int32_abs (-a) = int32_abs a := by
  by_cases h : 0 ≤ a
  · rw [int32_abs_of_nonneg a h]
    rw [int32_abs_of_nonpos (-a) ((Int32.neg_nonpos_iff a).mpr (Or.inr h))]
    simp
  have hnp := Int32.le_of_lt (Int32.not_le.mp h)
  rw [int32_abs_of_nonpos a hnp]
  by_cases hmv : Int32.minValue = a
  · subst hmv; rfl
  have hlb : Int32.minValue < a := Int32.lt_of_le_of_ne (Int32.minValue_le a) hmv
  exact int32_abs_of_nonneg (-a) (int32_neg_nonneg_of_nonpos a hlb hnp)

-- The absolute value is equal to either the integer itself, or its negation
theorem int32_abs_eq_self_or_neg (a : Int32) : int32_abs a = a ∨ int32_abs a = -a := by
  by_cases h : 0 ≤ a
  · exact Or.inl (int32_abs_of_nonneg a h)
  · exact Or.inr (int32_abs_of_nonpos a (Int32.le_of_lt (Int32.not_le.mp h)))

theorem int32_abs_eq_abs_iff (a b : Int32) :
  int32_abs a = int32_abs b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    rcases int32_abs_eq_self_or_neg a with ha₀ | ha₁
    · rw [ha₀] at h
      rcases int32_abs_eq_self_or_neg b with hb₀ | hb₁
      · left
        rwa [hb₀] at h
      · right
        rwa [hb₁] at h
    · rw [ha₁] at h
      apply Int32.neg_inj.mpr at h
      simp at h
      rcases int32_abs_eq_self_or_neg b with hb₀ | hb₁
      · right
        rwa [hb₀] at h
      · left
        rw [hb₁] at h
        simp at h
        assumption
  · rintro (h₀ | h₁)
    · subst h₀; rfl
    · subst h₁
      exact int32_abs_neg b

-- If |a| < |b| then a % b = a
-- Note that if either a or b is -2^31 this may not hold
theorem int32_mod_of_abs_lt (a b : Int32) (hlt : int32_abs a < int32_abs b)
  (hlba : Int32.minValue < a) (hlbb : Int32.minValue < b) : a % b = a := by
  apply Int32.lt_iff_toInt_lt.mp at hlt
  rw [int32_toInt_abs a hlba, int32_toInt_abs b hlbb] at hlt
  apply Int32.toInt_inj.mp; simp
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
