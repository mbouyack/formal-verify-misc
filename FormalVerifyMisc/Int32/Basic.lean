import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

-- Prevent '2^31' from having to be written as '2 ^ 31'
set_option linter.style.commandStart false
set_option linter.flexible false

def int32_sign (a : Int32) : Int32 :=
  if a < 0 then -1 else
  if 0 < a then 1 else 0

theorem int32_sign_of_neg (a : Int32) (hneg : a < 0) : int32_sign a = -1 := by
  unfold int32_sign
  rw [if_pos hneg]

theorem int32_sign_of_zero : int32_sign 0 = 0 := rfl

theorem int32_sign_of_pos (a : Int32) (hneg : 0 < a) : int32_sign a = 1 := by
  unfold int32_sign
  rw [if_pos hneg, if_neg]
  exact Int32.lt_asymm hneg

theorem int32_toInt_sign (a : Int32) :
  (int32_sign a).toInt = Int.sign a.toInt := by
  unfold int32_sign
  split_ifs with h₀ h₁
  · have hneg := Int32.toInt_zero ▸ (Int32.lt_iff_toInt_lt.mp h₀)
    rw [Int.sign_eq_neg_one_of_neg hneg]; rfl
  · have hpos := Int32.toInt_zero ▸ (Int32.lt_iff_toInt_lt.mp h₁)
    rw [Int.sign_eq_one_of_pos hpos]; rfl
  rw [Int32.le_antisymm (Int32.not_lt.mp h₁) (Int32.not_lt.mp h₀)]
  rfl

theorem int32_toInt_pos_of_pos {a : Int32} (hpos : 0 < a) :
  0 < a.toInt := Int32.lt_iff_toInt_lt.mp hpos

def in_bounds_32 (n : Int) : Prop := -2^31 ≤ n ∧ n < 2^31

theorem in_bounds_32_of_abs_lt (n : Int) (h : |n| < 2^31) :
  in_bounds_32 n := by
  by_cases hpos : 0 < n
  · use le_of_lt (lt_trans (by norm_num) hpos)
    exact (abs_of_pos hpos) ▸ h
  rename' hpos => hneg; push_neg at hneg
  use le_of_lt (neg_lt.mp ((abs_of_nonpos hneg) ▸ h))
  exact lt_of_le_of_lt hneg (by norm_num)

-- Proves the conditions for moving "+1" across the 'toInt' conversion
theorem int32_toInt_succ (a : Int32) (halt : a < Int32.maxValue) :
  (a + 1).toInt = a.toInt + 1 := by
  rw [Int32.toInt_add]
  apply Int.bmod_eq_of_le <;> simp
  · apply Int.le_add_of_sub_right_le
    apply le_trans _ (Int32.le_toInt a); simp
  · apply Int.add_lt_of_lt_sub_right
    exact Int32.lt_iff_toInt_lt.mp halt

-- Alternate version of int32_toInt_succ
theorem int32_toInt_succ' (a : Int32) (halt : a.toInt < 2^31 - 1) :
  (a + 1).toInt = a.toInt + 1 := by
  rw [← Int32.toInt_maxValue, ← Int32.lt_iff_toInt_lt] at halt
  exact int32_toInt_succ a halt

-- Proves the conditions for moving addition across the 'toInt' conversion
theorem int32_toInt_add_of_bounds
  (a b : Int32) (hb : in_bounds_32 (a.toInt + b.toInt)) :
  (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add, Int.bmod_eq_of_le hb.1 hb.2]

-- Addition can be moved across the 'toInt' conversion if the
-- sum of the bounds is in-bounds
theorem int32_toInt_add_of_add_bounds
  {a b : Int32} {alb aub blb bub : Int}
  (lea : alb ≤ a.toInt) (alt : a.toInt < aub)
  (leb : blb ≤ b.toInt) (blt : b.toInt < bub)
  (hlb : -2^31 ≤ alb + blb) (hub : aub + bub ≤ 2^31) :
  (a + b).toInt = a.toInt + b.toInt := by
  apply int32_toInt_add_of_bounds
  constructor
  · exact le_trans hlb (Int.add_le_add lea leb)
  · exact lt_of_lt_of_le (Int.add_lt_add alt blt) hub

-- Proves the conditions for moving subtraction across the 'toInt' conversion
theorem int32_toInt_sub_of_bounds
  (a b : Int32) (hb : in_bounds_32 (a.toInt - b.toInt)) :
  (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub, Int.bmod_eq_of_le hb.1 hb.2]

-- Proves the conditions for moving multiplication across the 'toInt' conversion
theorem int32_toInt_mul_of_bounds
  (a b : Int32) (hb : in_bounds_32 (a.toInt * b.toInt)) :
  (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul, Int.bmod_eq_of_le hb.1 hb.2]

-- Proves the conditions for moving division across the 'toInt' conversion
-- Note that division on Int32 corresponds to Int.tdiv, not the standard
-- '/' operator. The difference is that 'tdiv' always rounds toward zero.
theorem int32_toInt_div (a b : Int32) (h : Int32.minValue < a ∨ b ≠ -1) :
  (a / b).toInt = a.toInt.tdiv b.toInt :=
  Or.elim h
    (fun lhs ↦ Int32.toInt_div_of_ne_left a b (Int32.ne_of_lt lhs).symm)
    (fun rhs ↦ Int32.toInt_div_of_ne_right a b rhs)

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

-- An Int32 cast to to integer is 'in bounds'
theorem int32_in_bounds_toInt (a : Int32) :
  in_bounds_32 a.toInt :=
  ⟨int32_minval_le_toInt a, int32_toInt_lt_maxval a⟩

theorem int32_toInt_zero_iff {a : Int32} : a = 0 ↔ a.toInt = 0 := ⟨
  fun h ↦ Int32.toInt_inj.mpr h,
  fun h ↦ Int32.toInt_inj.mp (Int32.toInt_zero ▸ h)⟩

theorem int32_toInt_ne_zero_of_ne_zero {a : Int32} (hnz : a ≠ 0) : a.toInt ≠ 0 :=
  fun h ↦ hnz (Int32.toInt_inj.mp (Eq.trans h (Int32.toInt_zero.symm)))

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
