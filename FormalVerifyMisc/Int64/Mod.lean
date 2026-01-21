import FormalVerifyMisc.Int64.Basic

-- Any "well-behaved" 64-bit integer mod -2^63 is equal to itself
theorem int64_mod_minval (a : Int64) (hlb : Int64.minValue < a) : a % Int64.minValue = a := by
  apply Int64.toInt_inj.mp; simp
  by_cases hnn : 0 ≤ a.toInt
  · exact Int.tmod_eq_of_lt hnn (int64_toInt_lt_maxval a)
  push_neg at hnn; rename' hnn => hneg
  nth_rw 1 [← Int.neg_neg a.toInt, Int.neg_tmod]
  rw [Int.tmod_eq_of_lt (le_of_lt (Int.neg_pos.mpr hneg))]
  · simp
  · exact Int.neg_lt_of_neg_lt (Int64.lt_iff_toInt_lt.mp hlb)

-- In Int64, the result of '%' is always "well-behaved" if the dividend is well-behaved
-- TODO: Consider proving an alternate version of this theorem with b ≠ 0
-- instead of Int64.minValue < a
theorem int64_minval_lt_mod (a b : Int64) (hlb : Int64.minValue < a) : Int64.minValue < a % b := by
  apply Int64.lt_iff_toInt_lt.mpr; simp
  by_cases hbneg : b.toInt < 0
  · have := Int.lt_tmod_of_pos a.toInt (Int.neg_pos.mpr hbneg)
    simp at this
    exact Int.lt_of_le_of_lt (int64_minval_le_toInt b) this
  by_cases hnz : b.toInt = 0
  · rw [hnz]; simp
    exact Int64.lt_iff_toInt_lt.mp hlb
  push_neg at hnz
  have hbpos := lt_of_le_of_ne (Int.not_lt.mp hbneg) hnz.symm
  apply lt_of_le_of_lt (Int.neg_le_neg_iff.mpr _) (Int.lt_tmod_of_pos a.toInt hbpos)
  exact le_of_lt (int64_toInt_lt_maxval b)

@[simp] theorem int64_mod_neg (a b : Int64) : a % (-b) = a % b := by
  apply Int64.toInt_inj.mp
  by_cases hmv : Int64.minValue = b
  · subst hmv; simp
  rw [Int64.toInt_mod, Int64.toInt_mod]
  rw [int64_toInt_neg b (int64_minval_lt_of_ne_minval b hmv)]
  exact Int.tmod_neg _ _

-- Note that unlike 'mod_neg' (above) this result depends on 'a' being "well-behaved"
theorem int64_neg_mod (a b : Int64) (hlba : Int64.minValue < a) : (-a) % b = -(a % b) := by
  apply Int64.toInt_inj.mp
  by_cases hmvb : Int64.minValue = b
  · subst hmvb
    by_cases hmva : Int64.minValue = a
    · subst hmva; rfl
    have hlba := int64_minval_lt_of_ne_minval a hmva
    have hlbna := int64_minval_lt_neg a hlba
    rw [int64_mod_minval (-a) hlbna]
    rw [int64_mod_minval a hlba]
  have hlbb := int64_minval_lt_of_ne_minval b hmvb
  rw [int64_toInt_neg (a % b) (int64_minval_lt_mod a b hlba)]
  rw [Int64.toInt_mod, Int64.toInt_mod]
  rw [int64_toInt_neg a hlba, Int.neg_tmod]

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

lemma mul_tdiv_in_bounds_64_of_in_bounds_64
  (m n : Int) (hmib : in_bounds_64 m) :
  in_bounds_64 (n * (m.tdiv n)) := by
  obtain ⟨lbm, ubm⟩ := hmib
  have hrw : n * (m.tdiv n) = m - m.tmod n := by
    apply eq_sub_of_add_eq
    exact Int.mul_tdiv_add_tmod _ _
  rw [hrw]; clear hrw
  -- Handle the case where m = -2^63 so the remaining cases are symmetric
  by_cases hmmv : m = -2^63
  · subst hmmv
    constructor <;> simp
    · apply Int.tmod_nonneg; simp
    · exact lt_of_le_of_lt (int_tmod_le_self _ n (by norm_num)) (by norm_num)
  push_neg at hmmv
  replace lbm := lt_of_le_of_ne lbm hmmv.symm; clear hmmv
  apply in_bounds_64_of_abs_lt
  -- Without loss of generality, m is non-negative
  wlog h : 0 ≤ m
  · rw [← Int.add_neg_eq_sub, ← Int.neg_tmod, ← abs_neg]
    rw [Int.neg_add, Int.add_neg_eq_sub]
    apply this (-m) n (neg_lt.mp lbm) (neg_lt_neg ubm)
    exact neg_nonneg_of_nonpos (le_of_not_ge h)
  apply abs_sub_lt_of_nonneg_of_lt h ubm (Int.tmod_nonneg _ h) (lt_of_le_of_lt _ ubm)
  exact int_tmod_le_self _ _ h

-- Prove when the defining equation for '%' holds for Int64
theorem int64_mul_div_add_mod
  (a b : Int64) (h : Int64.minValue < a ∨ b ≠ -1) : b * (a / b) + (a % b) = a := by
  have := Int.mul_tdiv_add_tmod a.toInt b.toInt
  have h₀ : in_bounds_64 (b.toInt * (a / b).toInt) := by
    rw [int64_toInt_div a b h]
    apply mul_tdiv_in_bounds_64_of_in_bounds_64
    exact int64_in_bounds_toInt _
  have h₁ : in_bounds_64 ((b * (a / b)).toInt + (a % b).toInt) := by
    rw [int64_toInt_mul_of_bounds _ _ h₀]
    rw [int64_toInt_div a b h, Int64.toInt_mod]
    rw [this]
    exact int64_in_bounds_toInt _
  apply Int64.toInt_inj.mp
  rw [int64_toInt_add_of_bounds _ _ h₁]
  rw [int64_toInt_mul_of_bounds _ _ h₀]
  rwa [Int64.toInt_mod, int64_toInt_div _ _ h]
