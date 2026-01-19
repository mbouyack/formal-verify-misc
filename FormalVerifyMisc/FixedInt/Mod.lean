import FormalVerifyMisc.FixedInt.Basic

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

-- In Int32, the resul of '%' is always "well-behaved" if the dividends is well-behaved
-- TODO: Consider proving an alternate version of this theorem with b ≠ 0
-- instead of Int32.minValue < a
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
