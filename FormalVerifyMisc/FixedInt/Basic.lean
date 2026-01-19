import Mathlib.Tactic
import Mathlib.Data.Int.Basic

-- Proves the conditions for moving addition across the 'toInt' conversion
theorem int32_toInt_add_of_lt_of_ge (a b : Int32)
  (hlb : -2 ^ 31 ≤ a.toInt + b.toInt) (hub : a.toInt + b.toInt < 2 ^ 31) :
  (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add, Int.bmod_eq_of_le]
  · apply Int.le_trans (Int.neg_le_neg _) hlb; simp
  · apply Int.le_trans hub; simp

-- Proves the conditions for moving multiplication across the 'toInt' conversion
theorem int32_toInt_mul_of_lt_of_ge (a b : Int32)
  (hlb : -2 ^ 31 ≤ a.toInt * b.toInt) (hub : a.toInt * b.toInt < 2 ^ 31) :
  (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul, Int.bmod_eq_of_le]
  · apply Int.le_trans (Int.neg_le_neg _) hlb; simp
  · apply Int.le_trans hub; simp

-- If an Int32 does not meet the requirement to be "well-behaved",
-- it must be equal to Int32.minValue
theorem int32_eq_minval (a : Int32) (h : ¬Int32.minValue < a) : a = Int32.minValue :=
  Int32.le_antisymm (Int32.not_lt.mp h) (Int32.minValue_le a)

-- If an Int32 is not equal to Int32.minValue it is well-behaved
theorem int32_minval_lt_of_ne_minval (a : Int32) (h : Int32.minValue ≠ a) : Int32.minValue < a :=
  Int32.lt_of_le_of_ne (Int32.minValue_le a) h

-- In the 32-bit integers, -(-2^31) = -2^31
@[simp] theorem int32_neg_minval : -Int32.minValue = Int32.minValue := rfl

-- If a 32-bit integer is "well-behaved", so is its negation
theorem int32_minval_lt_neg (a : Int32) (hlb : Int32.minValue < a) : Int32.minValue < -a := by
  contrapose! hlb; simp
  apply Int32.neg_inj.mp
  rw [Int32.le_antisymm (Int32.not_lt.mp hlb) (Int32.minValue_le _)]
  rw [int32_neg_minval]

-- Int32.toInt returns a value less than 2^31
theorem int32_toInt_lt_maxval (a : Int32) : a.toInt < 2^31 :=
  Int.lt_add_one_of_le (Int32.le_iff_toInt_le.mp (Int32.le_maxValue a))

-- Int32.toInt returns a value not less than -2^31
theorem int32_minval_le_toInt (a : Int32) : -2^31 ≤ a.toInt :=
  Int32.le_iff_toInt_le.mp (Int32.minValue_le a)

-- Negation can be moved across the 'toInt' conversion as long as
-- the value isn't -2^31
theorem int32_toInt_neg (a : Int32) (hlb : Int32.minValue < a) :
  (-a).toInt = -a.toInt := by
  simp
  apply Int.bmod_eq_of_le
  · simp
    apply Int.le_trans (Int32.le_iff_toInt_le.mp (Int32.le_maxValue a))
    unfold Int32.maxValue; simp
  · simp
    apply Int.neg_lt_neg_iff.mp; simp
    replace hlt := Int32.lt_iff_toInt_lt.mp hlb; simp at hlt
    assumption

-- The negation of a non-positive Int32 is non-negative (given it is not -2^31)
theorem int32_neg_nonneg_of_nonpos
  (a : Int32) (hlb : Int32.minValue < a) (hnp : a ≤ 0) : 0 ≤ -a := by
  apply Int32.le_iff_toInt_le.mpr
  rw [int32_toInt_neg a hlb, Int32.toInt_zero]
  exact Int.neg_nonneg_of_nonpos (Int32.le_iff_toInt_le.mp hnp)
