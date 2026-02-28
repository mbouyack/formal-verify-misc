import FormalVerifyMisc.Int32.Abs
import FormalVerifyMisc.CodeChef.Template.Primes

namespace CodeChef

/- The purpose of this file is to verify the factorization code
   from the template I use on codechef.com -/

lemma int32_toInt_natAbs_lt_iff {i : Int32} (inn : 0 ≤ i) (s : ℕ) :
  i.toInt < s ↔ i.toInt.natAbs < s := by
  rw [← Int.ofNat_lt]
  rw [Int.ofNat_natAbs_of_nonneg]
  exact Int32.le_iff_toInt_le.mp inn

lemma int32_toInt_succ_of_lt_primes_size {i : Int32} (ilt : i.toInt < primes.size) :
  (i + 1).toInt = i.toInt + 1 := by
  have ilt' : i.toInt < 2^31 - 1 := by
    apply lt_trans ilt
    apply lt_trans (Int.ofNat_lt_ofNat_of_lt primes_size_lt_sieve_size)
    unfold SIEVE_SIZE; simp
  rw [int32_toInt_succ' _ ilt']

lemma int32_succ_toInt_natAbs_of_lt_primes_size
  (i : Int32) (inn : 0 ≤ i) (ilt : i.toInt < primes.size) :
  (i + 1).toInt.natAbs = i.toInt.natAbs + 1 := by
  have inn' : 0 ≤ i.toInt := Int32.le_iff_toInt_le.mp inn
  rw [int32_toInt_succ_of_lt_primes_size ilt]
  rw [Int.natAbs_add_of_nonneg inn' Int.one_nonneg]
  simp

-- This result is required to show we don't overrun the primes
-- array in implementing 'divisor_search' (below)
lemma int32_succ_toInt_natAbs_lt_of_divlt (n i p : Int32)
  (ltn : 1 < n) (inn : 0 ≤ i) (ilt : i.toInt.natAbs < primes.size)
  (hpi : p = primes[i.toInt.natAbs]) (divlt : ¬int32_abs n / p < p) :
  (i + 1).toInt.natAbs < primes.size := by
  have inn' : 0 ≤ i.toInt := Int32.le_iff_toInt_le.mp inn
  have ilt' : i.toInt < primes.size := (int32_toInt_natAbs_lt_iff inn _).mpr ilt
  rw [int32_succ_toInt_natAbs_of_lt_primes_size i inn ilt']
  apply lt_of_le_of_ne (Nat.add_one_le_of_lt ilt)
  -- Proof by contradiction: if ¬(i + 1) < primes.size, then i + 1 = primes.size
  -- and p = 999983. This contradicts 'divlt' because any 32-bit integer divided
  -- by 999983 will be less than 999983.
  contrapose! divlt
  rename' divlt => ipsp
  apply Int.ofNat_inj.mpr at ipsp
  rw [Int.natCast_add, Nat.cast_one, Int.ofNat_natAbs_of_nonneg inn'] at ipsp
  rw [← Int.sub_left_inj 1, Int.add_sub_cancel] at ipsp
  have pspos : 0 < primes.size := Nat.zero_lt_of_lt ilt
  have hp : p = 999983 := by
    rw [hpi]
    have leps : 1 ≤ primes.size := Nat.add_one_le_of_lt pspos
    rw [← Int.ofNat_one, ← Int.ofNat_sub leps] at ipsp
    rw [getElem_congr_idx (congrArg Int.natAbs ipsp)]
    simp only [Int.natAbs_natCast]
    rw [← Array.back_eq_getElem pspos]
    exact primes_back
  apply Int32.lt_iff_toInt_lt.mpr
  rw [hp, int32_toInt_div _ _ (Or.inr (by simp))]
  simp only [Int32.reduceToInt]
  rw [← @Int.mul_lt_mul_left 999983 _ _ (by simp)]
  let nmod := (int32_abs n).toInt.tmod 999983
  rw [← Int.add_lt_add_iff_right nmod]
  rw [Int.mul_tdiv_add_tmod]
  apply lt_trans (int32_toInt_lt_maxval (int32_abs n))
  have nmodnn : 0 ≤ nmod := by
    unfold nmod
    apply Int.tmod_nonneg
    rw [← Int32.toInt_zero]
    apply Int32.le_iff_toInt_le.mp
    apply int32_abs_nonneg
    apply Int32.lt_trans _ ltn
    unfold Int32.minValue; simp
  apply (Int.add_zero _) ▸ (Int.add_le_add _ nmodnn)
  simp

-- Prove termination for 'divisor_search_impl' (below)
lemma divisor_search_term (i : Int32) (inn : 0 ≤ i) (ilt : i.toInt < primes.size) :
  SIEVE_SIZE - (i + 1).toInt.natAbs < SIEVE_SIZE - i.toInt.natAbs := by
  have inn' : 0 ≤ i.toInt := Int32.le_iff_toInt_le.mp inn
  have ilt' : i.toInt.natAbs < primes.size := (int32_toInt_natAbs_lt_iff inn _).mp ilt
  have ilt'' := lt_trans ilt' primes_size_lt_sieve_size
  rw [int32_succ_toInt_natAbs_of_lt_primes_size i inn ilt]
  rw [Nat.sub_add_eq]
  exact Nat.sub_lt (Nat.sub_pos_of_lt ilt'') (by simp)

-- Prove that i+1 is also non-negative if i < primes.size
lemma int32_succ_nonneg_of_lt_primes_size (i : Int32)
  (inn : 0 ≤ i) (iltps : i.toInt < primes.size) : 0 ≤ i + 1 := by
  apply Int32.le_trans inn
  apply Int32.le_iff_toInt_le.mpr
  rw [int32_toInt_succ_of_lt_primes_size iltps]
  convert Int.add_le_add_left Int.one_nonneg i.toInt; simp

-- Find the smallest positive divisor of n by performing a linear search.
-- Begin the search at 'primes[i]', assuming that no smaller prime is a divisor.
--
-- Note that originally the algorithm checked if p * p ≤ n, but to determine
-- that 2^31 - 1 is its own smallest divisor it would need to verify that
-- 46349 * 46349 > 2^31 - 1, but this cannot be done in 32-bit arithmetic.
def divisor_search_impl (n i : Int32)
  (ltn : 1 < n) (inn : 0 ≤ i) (ilt : i.toInt.natAbs < primes.size) : Int32 :=
  (fun (ilt' : i.toInt < primes.size) ↦
    if divlt : int32_abs n / primes[i.toInt.natAbs] <
      (primes[i.toInt.natAbs]) then n else
    if n % ((primes[i.toInt.natAbs])) = 0 then ((primes[i.toInt.natAbs])) else
    divisor_search_impl n (i + 1) ltn
      (int32_succ_nonneg_of_lt_primes_size i inn ilt')
      (int32_succ_toInt_natAbs_lt_of_divlt
        n i primes[i.toInt.natAbs] ltn inn ilt rfl divlt
      )
  ) ((int32_toInt_natAbs_lt_iff inn _).mpr ilt)
termination_by SIEVE_SIZE - i.toInt.natAbs
decreasing_by
  exact divisor_search_term i inn ilt'

-- Entry point for divisor_search_impl
def divisor_search (n : Int32) (ltn : 1 < n) : Int32 :=
  divisor_search_impl n 0 ltn (Int32.le_refl _) (by
    simp only [Int32.reduceToInt, Int.natAbs_zero]
    exact primes_size_pos
  )

-- Find the smallest positive divisor of 'n'
-- If n is "small" we can look up the answer in 'divs' otherwise
-- search for the result using 'divisor_search'
def smallest_divisor (n : Int32) : Int32 :=
  if nnemv : n = Int32.minValue then 2 else
  if lenabs : int32_abs n < 2 then n else
  if nabslt : int32_abs n < SIEVE_SIZE_32 then divs[n.toInt.natAbs]'(by
    push_neg at nnemv
    have ltn := Int32.lt_of_le_of_ne (Int32.minValue_le n) nnemv.symm
    apply Int32.lt_iff_toInt_lt.mp at nabslt
    rw [int32_toInt_abs _ ltn, Int.abs_eq_natAbs, sieve_size_32_toInt] at nabslt
    rw [divs_size]
    exact Int.lt_of_ofNat_lt_ofNat nabslt
  ) else divisor_search (int32_abs n) (by
    rw [Int32.not_lt] at lenabs
    exact lenabs
  )

end CodeChef
