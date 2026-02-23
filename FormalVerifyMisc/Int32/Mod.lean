import FormalVerifyMisc.Int32.Basic

set_option linter.flexible false

-- Any "well-behaved" 32-bit integer mod -2^31 is equal to itself
theorem int32_mod_minval (a : Int32) (hlb : Int32.minValue < a) : a % Int32.minValue = a := by
  apply Int32.toInt_inj.mp; simp
  by_cases hnn : 0 ≤ a.toInt
  · exact Int.tmod_eq_of_lt hnn (int32_toInt_lt_maxval a)
  push_neg at hnn; rename' hnn => hneg
  nth_rw 1 [← Int.neg_neg a.toInt, Int.neg_tmod]
  rw [Int.tmod_eq_of_lt (le_of_lt (Int.neg_pos.mpr hneg))]
  · simp
  · exact Int.neg_lt_of_neg_lt (Int32.lt_iff_toInt_lt.mp hlb)

-- In Int32, the result of '%' is always "well-behaved" if the dividend is well-behaved
theorem int32_minval_lt_mod (a b : Int32) (hlb : Int32.minValue < a) : Int32.minValue < a % b := by
  apply Int32.lt_iff_toInt_lt.mpr; simp
  by_cases hbneg : b.toInt < 0
  · have := Int.lt_tmod_of_pos a.toInt (Int.neg_pos.mpr hbneg)
    simp at this
    exact Int.lt_of_le_of_lt (int32_minval_le_toInt b) this
  by_cases hnz : b.toInt = 0
  · rw [hnz]; simp
    exact Int32.lt_iff_toInt_lt.mp hlb
  push_neg at hnz
  have hbpos := lt_of_le_of_ne (Int.not_lt.mp hbneg) hnz.symm
  apply lt_of_le_of_lt (Int.neg_le_neg_iff.mpr _) (Int.lt_tmod_of_pos a.toInt hbpos)
  exact le_of_lt (int32_toInt_lt_maxval b)

-- In Int32, the result of '%' is always "well-behaved" if the divisor is non-zero
theorem int32_minval_lt_mod' (a b : Int32) (h : b ≠ 0) : Int32.minValue < a % b := by
  apply Int32.lt_iff_toInt_lt.mpr
  rw [Int32.toInt_mod]
  by_cases hbneg : b.toInt < 0
  · have := Int.lt_tmod_of_pos a.toInt (Int.neg_pos.mpr hbneg)
    simp at this
    exact Int.lt_of_le_of_lt (int32_minval_le_toInt b) this
  have hbpos := lt_of_le_of_ne (Int.not_lt.mp hbneg) (int32_toInt_ne_zero_of_ne_zero h).symm
  apply Int.lt_of_le_of_lt _ (Int.lt_tmod_of_pos a.toInt hbpos)
  apply Int.le_neg_of_le_neg (le_of_lt _)
  exact int32_toInt_lt_maxval _

@[simp] theorem int32_mod_neg (a b : Int32) : a % (-b) = a % b := by
  apply Int32.toInt_inj.mp
  by_cases hmv : Int32.minValue = b
  · subst hmv; simp
  rw [Int32.toInt_mod, Int32.toInt_mod]
  rw [int32_toInt_neg b (int32_minval_lt_of_ne_minval b hmv)]
  exact Int.tmod_neg _ _

-- Note that unlike 'mod_neg' (above) this result depends on 'a' being "well-behaved"
theorem int32_neg_mod (a b : Int32) (hlba : Int32.minValue < a) : (-a) % b = -(a % b) := by
  apply Int32.toInt_inj.mp
  by_cases hmvb : Int32.minValue = b
  · subst hmvb
    by_cases hmva : Int32.minValue = a
    · subst hmva; rfl
    have hlba := int32_minval_lt_of_ne_minval a hmva
    have hlbna := int32_minval_lt_neg a hlba
    rw [int32_mod_minval (-a) hlbna]
    rw [int32_mod_minval a hlba]
  have hlbb := int32_minval_lt_of_ne_minval b hmvb
  rw [int32_toInt_neg (a % b) (int32_minval_lt_mod a b hlba)]
  rw [Int32.toInt_mod, Int32.toInt_mod]
  rw [int32_toInt_neg a hlba, Int.neg_tmod]

-- I'm surprised this result doesn't already exist
-- Gemini seems to think 'tmod_le_self' *does* exist,
-- but I haven't been able to find it
theorem int_tmod_le_self (m n : Int) (hmpos : 0 ≤ m) : m.tmod n ≤ m := by
  by_cases h₀ : m < n
  · rw [Int.tmod_eq_of_lt hmpos h₀]
  by_cases h₁ : m < -n
  · rw [← Int.tmod_neg]
    rw [Int.tmod_eq_of_lt hmpos h₁]
  by_cases hz : n = 0
  · subst hz; simp
  rename' hz => hnz; push_neg at hnz
  apply le_of_lt
  by_cases hnpos : 0 < n
  · exact Int.lt_of_lt_of_le (Int.tmod_lt_of_pos m hnpos) (not_lt.mp h₀)
  replace hnpos := Int.neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hnpos) hnz)
  apply Int.lt_of_lt_of_le _ (not_lt.mp h₁)
  rw [← Int.tmod_neg]
  exact Int.tmod_lt_of_pos m hnpos

lemma mul_tdiv_in_bounds_32_of_in_bounds_32
  (m n : Int) (hmib : in_bounds_32 m) :
  in_bounds_32 (n * (m.tdiv n)) := by
  obtain ⟨lbm, ubm⟩ := hmib
  have hrw : n * (m.tdiv n) = m - m.tmod n := by
    apply eq_sub_of_add_eq
    exact Int.mul_tdiv_add_tmod _ _
  rw [hrw]; clear hrw
  -- Handle the case where m = -2^31 so the remaining cases are symmetric
  by_cases hmmv : m = -2^31
  · subst hmmv
    constructor <;> simp
    · apply Int.tmod_nonneg; simp
    · exact lt_of_le_of_lt (int_tmod_le_self _ n (by norm_num)) (by norm_num)
  push_neg at hmmv
  replace lbm := lt_of_le_of_ne lbm hmmv.symm; clear hmmv
  apply in_bounds_32_of_abs_lt
  -- Without loss of generality, m is non-negative
  wlog h : 0 ≤ m
  · rw [← Int.add_neg_eq_sub, ← Int.neg_tmod, ← abs_neg]
    rw [Int.neg_add, Int.add_neg_eq_sub]
    apply this (-m) n (neg_lt.mp lbm) (neg_lt_neg ubm)
    exact neg_nonneg_of_nonpos (le_of_not_ge h)
  apply abs_sub_lt_of_nonneg_of_lt h ubm (Int.tmod_nonneg _ h) (lt_of_le_of_lt _ ubm)
  exact int_tmod_le_self _ _ h

-- Prove when the defining equation for '%' holds for Int32
theorem int32_mul_div_add_mod
  (a b : Int32) (h : Int32.minValue < a ∨ b ≠ -1) : b * (a / b) + (a % b) = a := by
  have := Int.mul_tdiv_add_tmod a.toInt b.toInt
  have h₀ : in_bounds_32 (b.toInt * (a / b).toInt) := by
    rw [int32_toInt_div a b h]
    apply mul_tdiv_in_bounds_32_of_in_bounds_32
    exact int32_in_bounds_toInt _
  have h₁ : in_bounds_32 ((b * (a / b)).toInt + (a % b).toInt) := by
    rw [int32_toInt_mul_of_bounds _ _ h₀]
    rw [int32_toInt_div a b h, Int32.toInt_mod]
    rw [this]
    exact int32_in_bounds_toInt _
  apply Int32.toInt_inj.mp
  rw [int32_toInt_add_of_bounds _ _ h₁]
  rw [int32_toInt_mul_of_bounds _ _ h₀]
  rwa [Int32.toInt_mod, int32_toInt_div _ _ h]
