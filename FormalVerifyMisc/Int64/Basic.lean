import Mathlib.Tactic
import Mathlib.Data.Int.Basic

-- Prevent '2^63' from having to be written as '2 ^ 63'
set_option linter.style.commandStart false

def int64_sign (a : Int64) : Int64 :=
  if a < 0 then -1 else
  if 0 < a then 1 else 0

theorem int64_sign_of_neg (a : Int64) (hneg : a < 0) : int64_sign a = -1 := by
  unfold int64_sign
  rw [if_pos hneg]

theorem int64_sign_of_zero : int64_sign 0 = 0 := rfl

theorem int64_sign_of_pos (a : Int64) (hneg : 0 < a) : int64_sign a = 1 := by
  unfold int64_sign
  rw [if_pos hneg, if_neg]
  exact Int64.lt_asymm hneg

theorem int64_toInt_sign (a : Int64) :
  (int64_sign a).toInt = Int.sign a.toInt := by
  unfold int64_sign
  split_ifs with h₀ h₁
  · have hneg := Int64.toInt_zero ▸ (Int64.lt_iff_toInt_lt.mp h₀)
    rw [Int.sign_eq_neg_one_of_neg hneg]; rfl
  · have hpos := Int64.toInt_zero ▸ (Int64.lt_iff_toInt_lt.mp h₁)
    rw [Int.sign_eq_one_of_pos hpos]; rfl
  rw [Int64.le_antisymm (Int64.not_lt.mp h₁) (Int64.not_lt.mp h₀)]
  rfl

theorem int64_toInt_pos_of_pos {a : Int64} (hpos : 0 < a) :
  0 < a.toInt := Int64.lt_iff_toInt_lt.mp hpos

def in_bounds_64 (n : Int) : Prop := -2^63 ≤ n ∧ n < 2^63

theorem in_bounds_64_of_abs_lt (n : Int) (h : |n| < 2^63) :
  in_bounds_64 n := by
  by_cases hpos : 0 < n
  · use le_of_lt (lt_trans (by norm_num) hpos)
    exact (abs_of_pos hpos) ▸ h
  rename' hpos => hneg; push_neg at hneg
  use le_of_lt (neg_lt.mp ((abs_of_nonpos hneg) ▸ h))
  exact lt_of_le_of_lt hneg (by norm_num)

-- Proves the conditions for moving addition across the 'toInt' conversion
theorem int64_toInt_add_of_bounds
  (a b : Int64) (hb : in_bounds_64 (a.toInt + b.toInt)) :
  (a + b).toInt = a.toInt + b.toInt := by
  rw [Int64.toInt_add, Int.bmod_eq_of_le hb.1 hb.2]

-- Proves the conditions for moving subtraction across the 'toInt' conversion
theorem int64_toInt_sub_of_bounds
  (a b : Int64) (hb : in_bounds_64 (a.toInt - b.toInt)) :
  (a - b).toInt = a.toInt - b.toInt := by
  rw [Int64.toInt_sub, Int.bmod_eq_of_le hb.1 hb.2]

-- Proves the conditions for moving multiplication across the 'toInt' conversion
theorem int64_toInt_mul_of_bounds
  (a b : Int64) (hb : in_bounds_64 (a.toInt * b.toInt)) :
  (a * b).toInt = a.toInt * b.toInt := by
  rw [Int64.toInt_mul, Int.bmod_eq_of_le hb.1 hb.2]

-- Proves the conditions for moving division across the 'toInt' conversion
-- Note that division on Int64 corresponds to Int.tdiv, not the standard
-- '/' operator. The difference is that 'tdiv' always rounds toward zero.
theorem int64_toInt_div (a b : Int64) (h : Int64.minValue < a ∨ b ≠ -1) :
  (a / b).toInt = a.toInt.tdiv b.toInt :=
  Or.elim h
    (fun lhs ↦ Int64.toInt_div_of_ne_left a b (Int64.ne_of_lt lhs).symm)
    (fun rhs ↦ Int64.toInt_div_of_ne_right a b rhs)

-- If an Int64 does not meet the requirement to be "well-behaved",
-- it must be equal to Int64.minValue
theorem int64_eq_minval (a : Int64) (h : ¬Int64.minValue < a) : a = Int64.minValue :=
  Int64.le_antisymm (Int64.not_lt.mp h) (Int64.minValue_le a)

-- If an Int64 is not equal to Int64.minValue it is well-behaved
theorem int64_minval_lt_of_ne_minval (a : Int64) (h : Int64.minValue ≠ a) : Int64.minValue < a :=
  Int64.lt_of_le_of_ne (Int64.minValue_le a) h

-- In the 64-bit integers, -(-2^63) = -2^63
@[simp] theorem int64_neg_minval : -Int64.minValue = Int64.minValue := rfl

-- If a 64-bit integer is "well-behaved", so is its negation
theorem int64_minval_lt_neg (a : Int64) (hlb : Int64.minValue < a) : Int64.minValue < -a := by
  contrapose! hlb; simp
  apply Int64.neg_inj.mp
  rw [Int64.le_antisymm (Int64.not_lt.mp hlb) (Int64.minValue_le _)]
  rw [int64_neg_minval]

-- Int64.toInt returns a value less than 2^63
theorem int64_toInt_lt_maxval (a : Int64) : a.toInt < 2^63 :=
  Int.lt_add_one_of_le (Int64.le_iff_toInt_le.mp (Int64.le_maxValue a))

-- Int64.toInt returns a value not less than -2^63
theorem int64_minval_le_toInt (a : Int64) : -2^63 ≤ a.toInt :=
  Int64.le_iff_toInt_le.mp (Int64.minValue_le a)

-- An Int64 cast to to integer is 'in bounds'
theorem int64_in_bounds_toInt (a : Int64) :
  in_bounds_64 a.toInt :=
  ⟨int64_minval_le_toInt a, int64_toInt_lt_maxval a⟩

theorem int64_toInt_zero_iff {a : Int64} : a = 0 ↔ a.toInt = 0 := ⟨
  fun h ↦ Int64.toInt_inj.mpr h,
  fun h ↦ Int64.toInt_inj.mp (Int64.toInt_zero ▸ h)⟩

theorem int64_toInt_ne_zero_of_ne_zero {a : Int64} (hnz : a ≠ 0) : a.toInt ≠ 0 :=
  fun h ↦ hnz (Int64.toInt_inj.mp (Eq.trans h (Int64.toInt_zero.symm)))

-- Negation can be moved across the 'toInt' conversion as long as
-- the value isn't -2^63
theorem int64_toInt_neg (a : Int64) (hlb : Int64.minValue < a) :
  (-a).toInt = -a.toInt := by
  simp
  apply Int.bmod_eq_of_le
  · simp
    apply Int.le_trans (Int64.le_iff_toInt_le.mp (Int64.le_maxValue a))
    unfold Int64.maxValue; simp
  · simp
    apply Int.neg_lt_neg_iff.mp; simp
    replace hlt := Int64.lt_iff_toInt_lt.mp hlb; simp at hlt
    assumption

-- The negation of a non-positive Int64 is non-negative (given it is not -2^63)
theorem int64_neg_nonneg_of_nonpos
  (a : Int64) (hlb : Int64.minValue < a) (hnp : a ≤ 0) : 0 ≤ -a := by
  apply Int64.le_iff_toInt_le.mpr
  rw [int64_toInt_neg a hlb, Int64.toInt_zero]
  exact Int.neg_nonneg_of_nonpos (Int64.le_iff_toInt_le.mp hnp)
