import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Ring.Abs
import FormalVerifyMisc.Int32.Abs
import FormalVerifyMisc.Int32.Mod
import FormalVerifyMisc.CodeChef.Template.Primes
import FormalVerifyMisc.Loops

/- The purpose of this file is to verify the factorization code
   from the template I use on codechef.com -/

namespace CodeChef

-- Allow conversion between two different ways of stating the upper bound on 'i'
lemma int32_toInt_natAbs_lt_iff {i : Int32} (inn : 0 ≤ i) (s : ℕ) :
  i.toInt < s ↔ i.toInt.natAbs < s := by
  rw [← Int.ofNat_lt]
  rw [Int.ofNat_natAbs_of_nonneg]
  exact Int32.le_iff_toInt_le.mp inn

-- When converting between Int32 and Nat, this bound is often useful
theorem int32_lt_maxValue_of_lt_primes_size
  {i : ℕ} (ilt : i < primes.size) : i < 2 ^ 31 :=
  lt_trans (lt_trans ilt primes_size_lt_sieve_size) (by decide)

def div_search_fail (n : Int32) : Int32 → Bool :=
  fun i ↦ if hneg : i < 0 then true else
    if hlei : primes.size ≤ i.toInt then true else decide (
      let p := primes[i.toInt.natAbs]'(by
        rw [← int32_toInt_natAbs_lt_iff (Int32.not_lt.mp hneg)]
        exact Int.not_le.mp hlei
      )
      int32_abs n / p < p
    )

def div_search_success (n : Int32) : Int32 → Bool :=
  fun i ↦ if hneg : i < 0 then false else
    if hlei : primes.size ≤ i.toInt then false else decide (
      n % (primes[i.toInt.natAbs]'(by
        rw [← int32_toInt_natAbs_lt_iff (Int32.not_lt.mp hneg)]
        exact Int.not_le.mp hlei
      )) = 0
    )

-- If the ith element of 'primes' divides n, then 'i' satisfies 'div_search_success'
theorem div_search_success_sat_of_primes_mem_dvd (n : Int32) :
  ∀ (i : Int32), (inn : 0 ≤ i) → (ilt : i.toInt < primes.size) →
  (primes[i.toInt.natAbs]'(by
    rwa [← int32_toInt_natAbs_lt_iff inn])
  ).toInt ∣ n.toInt → div_search_success n i := by
  intro i inn ilt hdvd
  unfold div_search_success
  rw [dif_neg (Int32.not_lt.mpr inn)]
  rw [dif_neg (Int.not_le.mpr ilt)]
  rw [decide_eq_true_eq]
  rw [← Int32.toInt_inj, Int32.toInt_mod, Int32.toInt_zero]
  exact Int.tmod_eq_zero_of_dvd hdvd

-- 'div_search_fail' is satisfied for n = 0
theorem div_search_fail_sat_of_eq_zero (i : Int32) :
  div_search_fail 0 i := by
  unfold div_search_fail
  simp only [int32_abs_zero, Int32.zero_div, dite_eq_left_iff, Int32.not_lt, not_le,
    decide_eq_true_eq]
  exact fun _ _ ↦ primes_pos _ (Array.getElem_mem _)

-- 'div_search_fail' is always true when n = Int32.minValue
lemma div_search_fail_int32_min_value :
  ∀ (i : Int32), (inn : 0 ≤ i) → (ilt : i.toInt < primes.size) →
  div_search_fail Int32.minValue i = true := by
  intro i lei ile
  have ilt : i.toInt.natAbs < primes.size :=
    (int32_toInt_natAbs_lt_iff lei _).mp ile
  have pimem : primes[i.toInt.natAbs] ∈ primes := Array.getElem_mem _
  have pipos : 0 < primes[i.toInt.natAbs] :=
    primes_pos _ pimem
  have pitipos : 0 < primes[i.toInt.natAbs].toInt :=
    Int32.lt_iff_toInt_lt.mp pipos
  have pine : primes[i.toInt.natAbs] ≠ -1 :=
    (Int32.ne_of_lt (Int32.lt_trans (by decide) pipos)).symm
  have pile : primes[i.toInt.natAbs].toInt ≤ 999983 :=
    Int32.le_iff_toInt_le.mp (primes_le _ pimem)
  unfold div_search_fail
  have hmvti : (int32_abs 2147483648).toInt = -2147483648 := rfl
  split_ifs with h₀ h₁
  · rfl
  · rfl
  · simp only [int32_abs_neg, decide_eq_true_eq]
    apply Int32.lt_trans (Int32.lt_iff_toInt_lt.mpr _) pipos
    rw [int32_toInt_div _ _ (Or.inr pine), hmvti]
    simp only [Int.reduceNeg, Int.neg_tdiv, Int32.reduceToInt, Int.neg_neg_iff_pos]
    rw [Int.tdiv_eq_ediv_of_nonneg (by decide)]
    -- TODO: Is there a missing theorem here?
    -- Given 0 < a, 0 < b, b < a we should be able to conclude 0 < a / b
    apply (Int.mul_lt_mul_left pitipos).mp
    rw [mul_zero]
    apply Int.lt_of_add_lt_add_right
    rw [Int.mul_ediv_add_emod, zero_add]
    exact lt_trans (lt_of_lt_of_le (Int.emod_lt_of_pos _ pitipos) pile) (by decide)

-- If the ith element of 'primes', squared, is greater than n,
-- then 'i' satisfies 'div_search_fail'
theorem div_search_fail_sat_of_lt_prime_mem_pow_two (n : Int32) :
  ∀ (i : Int32), (inn : 0 ≤ i) → (ilt : i.toInt < primes.size) →
  |n.toInt| < (primes[i.toInt.natAbs]'(by
    rwa [← int32_toInt_natAbs_lt_iff inn])
  ).toInt ^ 2 → div_search_fail n i := by
  intro i inn ilt nabslt
  have ilt' : i.toInt.natAbs < primes.size := by
    rwa [← int32_toInt_natAbs_lt_iff inn]
  by_cases nmv : n = Int32.minValue
  · subst nmv
    exact div_search_fail_int32_min_value _ inn ilt
  rename' nmv => nne; push_neg at nne
  have ltn' : Int32.minValue < n :=
    Int32.lt_of_le_of_ne (Int32.minValue_le _) nne.symm
  let p := primes[i.toInt.natAbs]
  unfold div_search_fail
  rw [dif_neg (Int32.not_lt.mpr inn)]
  rw [dif_neg (Int.not_le.mpr ilt)]
  rw [decide_eq_true_eq]
  apply Int32.lt_iff_toInt_lt.mpr
  have ppos : 0 < p := primes_pos _ (Array.getElem_mem ilt')
  have pnn : 0 ≤ p := Int32.le_of_lt ppos
  have pne : p ≠ -1 := by
    apply (Int32.ne_of_lt _).symm
    exact Int32.lt_trans (by decide) ppos
  rw [int32_toInt_div _ _ (Or.inr pne), int32_toInt_abs n ltn']
  change _ < p.toInt
  change _ < p.toInt ^ 2 at nabslt
  apply Int.lt_of_mul_lt_mul_left _ (Int32.toInt_zero ▸ (Int32.le_iff_toInt_le.mp pnn))
  apply Int.lt_of_add_lt_add_right
  rw [Int.mul_tdiv_add_tmod, ← pow_two]
  apply lt_of_lt_of_le nabslt (Int.le_add_of_nonneg_right (Int.tmod_nonneg _ _))
  exact abs_nonneg _

theorem nonneg_of_div_search_success_sat {n i : Int32} (h : div_search_success n i) : 0 ≤ i := by
  unfold div_search_success at h
  split_ifs at h
  apply Int32.not_lt.mp
  assumption

theorem lt_primes_size_of_div_search_success_sat
  {n i : Int32} (h : div_search_success n i) : i.toInt < primes.size := by
  unfold div_search_success at h
  split_ifs at h
  apply Int.not_le.mp
  assumption

theorem dvd_of_div_search_success_sat
  {n i : Int32} (h : div_search_success n i) :
  have ilt : i.toInt.natAbs < primes.size := by
    rw [← int32_toInt_natAbs_lt_iff]
    · exact lt_primes_size_of_div_search_success_sat h
    · exact nonneg_of_div_search_success_sat h
  let p : Int32 := primes[i.toInt.natAbs]
  n % p = 0 := by
  unfold div_search_success at h
  split_ifs at h
  simp only [decide_eq_true_eq] at h
  exact h

def div_search_start : Int32 := 0
def div_search_finish : Int32 := Int32.ofNat (primes.size - 1)

-- Casting 'div_search_finish' to Int gives primes.size - 1
theorem div_search_finish_toInt :
  div_search_finish.toInt = Nat.cast (primes.size - 1) := by
  apply Int32.toInt_ofNat_of_lt (Nat.sub_one_lt_of_le primes_size_pos _)
  exact le_of_lt (lt_trans primes_size_lt_sieve_size (by decide))

theorem div_search_finish_toInt_natAbs :
  div_search_finish.toInt.natAbs = primes.size - 1 := by
  rw [div_search_finish_toInt, Int.natAbs_natCast]

-- Prove that the search parameter 'i' can be used to index into "primes"
lemma lt_primes_size_iff_le_search_finish {i : Int32} (lei : div_search_start ≤ i) :
  i.toInt.natAbs < primes.size ↔ i ≤ div_search_finish := by
  rw [← int32_toInt_natAbs_lt_iff lei, Int32.le_iff_toInt_le]
  rw [div_search_finish_toInt]
  have hrw := Int.ofNat_sub (Nat.add_one_le_of_lt primes_size_pos)
  simp only [zero_add, Nat.cast_one] at hrw
  rw [hrw]
  exact ⟨Int.le_sub_one_of_lt, Int.lt_of_le_sub_one⟩

-- This can be proven with 'native_decide' but we're trying to avoid that
theorem div_search_start_le_finish :
  div_search_start ≤ div_search_finish := by
  apply Int32.le_iff_toInt_le.mpr
  rw [div_search_finish_toInt]
  exact Int.ofNat_le_ofNat_of_le (Nat.le_sub_one_of_lt primes_size_pos)

-- Using 'div_search_finish' to index into 'primes' gives
-- the last prime less than one million
theorem primes_div_search_finish :
  primes[div_search_finish.toInt.natAbs]'(by
    rw [div_search_finish_toInt_natAbs]
    exact Nat.sub_one_lt_of_lt primes_size_pos
  ) = 999983 := by
  rw [← primes_back, Array.back_eq_getElem]; congr
  exact div_search_finish_toInt_natAbs

-- Prove the failure condition will eventually be met
theorem exists_search_failure_sat (n : Int32) :
  ∃ a, div_search_start ≤ a ∧ a ≤ div_search_finish ∧
  div_search_fail n a = true := by
  by_cases hmin : n = Int32.minValue
  · subst hmin
    use div_search_start, Int32.le_refl _, div_search_start_le_finish
    apply div_search_fail_int32_min_value 0 (Int32.le_refl _)
    exact Int.ofNat_lt_ofNat_of_lt primes_size_pos
  rename' hmin => nne; push_neg at nne
  have ltn := Int32.lt_of_le_of_ne (Int32.minValue_le _) nne.symm
  use div_search_finish, div_search_start_le_finish, Int32.le_refl _
  apply div_search_fail_sat_of_lt_prime_mem_pow_two _
  · rw [← int32_toInt_abs n ltn, primes_div_search_finish]
    exact lt_trans (int32_toInt_abs_lt n) (by decide)
  · exact div_search_start_le_finish
  · rw [div_search_finish_toInt]
    apply Int.ofNat_lt_ofNat_of_lt
    exact Nat.sub_lt primes_size_pos (by decide)

-- Find the index which satisfies 'div_search_success'
-- or "none" if the search is unsuccessful
def divisor_index_opt (n : Int32) : Option Int32 :=
  do_search_opt (div_search_success n) (exists_search_failure_sat n)

-- If the search is successful, the result is greater than or equal to 'div_search_start'
theorem divisor_index_opt_ge_of_ne_none (n : Int32)
  (nenone : divisor_index_opt n ≠ none) :
  div_search_start ≤ (divisor_index_opt n).get (Option.isSome_iff_ne_none.mpr nenone) := by
  exact search_opt_ge_of_ne_none _ _ nenone

-- If the search is successful, the result is greater than or equal to 'div_search_start'
theorem divisor_index_opt_le_of_ne_none (n : Int32)
  (nenone : divisor_index_opt n ≠ none) :
  (divisor_index_opt n).get (Option.isSome_iff_ne_none.mpr nenone) ≤ div_search_finish := by
  exact search_opt_le_of_ne_none _ _ nenone

theorem div_search_success_of_mod2_eq_zero {n : Int32} (hmod : n % 2 = 0) :
  div_search_success n div_search_start = true := by
  unfold div_search_success div_search_start
  rw [dif_neg (Int32.not_lt.mpr (Int32.le_refl 0))]
  have npsle : ¬primes.size ≤ Int32.toInt 0 :=
    Int.not_le.mpr (Int.ofNat_lt_ofNat_of_lt primes_size_pos)
  rw [dif_neg npsle]
  simp only [Int32.reduceToInt, Int.natAbs_zero, decide_eq_true_eq]
  rwa [primes_getElem_zero_eq_two]

theorem divisor_index_ne_none_of_mod2_eq_zero {n : Int32} (hmod : n % 2 = 0) :
  divisor_index_opt n ≠ none := by
  apply do_search_opt_ne_none
  use div_search_start, Int32.le_refl _, div_search_start_le_finish
  apply And.intro _ (fun b ⟨leb, nleb⟩ ↦ False.elim (nleb leb))
  exact div_search_success_of_mod2_eq_zero hmod

-- Prove that the search succeeds for n = Int32.minValue
theorem divisor_index_ne_none_of_minValue :
  divisor_index_opt Int32.minValue ≠ none := by
  apply divisor_index_ne_none_of_mod2_eq_zero
  rfl

-- Prove that the search succeeds for n = 0
theorem divisor_index_ne_none_of_zero :
  divisor_index_opt 0 ≠ none := by
  apply divisor_index_ne_none_of_mod2_eq_zero
  rfl

lemma le_div_self_of_le_div_self {a b n : Int}
  (apos : 0 < a) (aleb : a ≤ b) (h : b ≤ n / b) : a ≤ n / a := by
  have bpos : 0 < b := lt_of_lt_of_le apos aleb
  have := Int.add_le_add_right ((Int.mul_le_mul_left bpos).mpr h) (n % b)
  rw [Int.mul_ediv_add_emod] at this
  apply Int.le_of_mul_le_mul_left _ apos
  apply Int.le_of_add_le_add_right
  rw [Int.mul_ediv_add_emod]
  apply le_trans _ this
  rcases Int.exists_add_of_le aleb with ⟨c, hc⟩
  subst hc
  by_cases cz : c = 0
  · subst cz
    simp
  push_neg at cz
  rw [mul_add, add_mul, add_mul]
  rw [add_assoc, add_assoc]
  apply Int.add_le_add_left _ (a * a)
  apply le_of_lt
  apply lt_of_lt_of_le (Int.emod_lt_of_pos _ apos)
  have cnn : (0 : ℤ) ≤ c := Int.natCast_nonneg c
  have cpos := lt_of_le_of_ne cnn (Int.natCast_ne_zero.mpr cz).symm
  apply le_trans _ (Int.le_add_of_nonneg_right _)
  · nth_rw 1 [← one_mul a]
    rw [Int.mul_le_mul_right apos]
    exact Int.add_one_le_of_lt cpos
  · apply Int.add_nonneg
    · apply Int.add_nonneg
      · exact Int.mul_nonneg (le_of_lt apos) cnn
      · exact Int.mul_nonneg cnn cnn
    · apply Int.emod_nonneg; symm
      apply ne_of_lt
      rw [← zero_add 0]
      apply Int.add_lt_add apos cpos

-- For primes above a certain size, the divisor search will fail
theorem divisor_index_none_of_prime_of_gt (n : Int32)
  (hprime : Nat.Prime n.toInt.natAbs)
  (ltn : 999983 < n.toInt.natAbs) :
  divisor_index_opt n = none := by
  apply search_opt_none_of_fail_first
  intro a ⟨ale, lea, ha⟩
  have hdvd := dvd_of_div_search_success_sat ha; dsimp at hdvd
  rw [int32_mod_eq_zero_iff_toInt_dvd] at hdvd
  have ltps := (lt_primes_size_iff_le_search_finish ale).mpr lea
  have psplt : primes.size - 1 < primes.size :=
    Nat.sub_lt primes_size_pos (by decide)
  let p := primes[a.toInt.natAbs]
  have pprime : Nat.Prime p.toInt.natAbs := by
    rcases prime_of_mem_primes p (Array.getElem_mem _) with ⟨p', hp', hp'prime⟩
    rwa [hp', Int.natAbs_natCast]
  have hdvd' : p.toInt.natAbs ∣ n.toInt.natAbs := (Int.natAbs_dvd_natAbs.mpr hdvd)
  rcases Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd' with lhs | rhs
  · absurd pprime
    rw [lhs]
    norm_num
  · absurd ltn; push_neg
    rw [← rhs]
    have hback : primes.back.toInt.natAbs = 999983 :=
      congrArg Int.natAbs (Int32.toInt_inj.mpr primes_back)
    rw [Array.back_eq_getElem] at hback
    rw [← hback]
    have hgenn {i : ℕ} (ilt : i < primes.size) : 0 ≤ primes[i].toInt :=
      Int32.le_iff_toInt_le.mp (Int32.le_of_lt (primes_pos _ (Array.getElem_mem _)))
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.ofNat_natAbs_of_nonneg (hgenn ltps)]
    rw [Int.ofNat_natAbs_of_nonneg (hgenn psplt)]
    exact Int32.le_iff_toInt_le.mp (primes_nondecreasing _ _ (Nat.le_sub_one_of_lt ltps) psplt)

-- If the absolute value of a 32-bit integer is not prime and is not zero or one
-- then the divisor search will succeed
theorem divisor_index_ne_none_of_not_prime (n : Int32)
  (hnprime : ¬Nat.Prime n.toInt.natAbs)
  (hltabs : 1 < n.toInt.natAbs) :
  divisor_index_opt n ≠ none := by
  -- Handle the case where n = -2^31
  by_cases nlemv : n ≤ Int32.minValue
  · have hn : n = Int32.minValue := Int32.le_antisymm nlemv (Int32.minValue_le _)
    subst hn
    exact divisor_index_ne_none_of_minValue
  rename' nlemv => ltn
  apply Int32.not_le.mp at ltn
  apply do_search_opt_ne_none
  rcases mem_primes_dvd_le_sqrt_exists_of_not_prime _ hnprime hltabs with ⟨p, pmem, pdvd, ple⟩
  rcases Array.getElem_of_mem pmem with ⟨i, ilt, hpi⟩
  let a : Int32 := Int32.ofNat i
  have ati : a.toInt = i := by
    unfold a
    apply Int32.toInt_ofNat_of_lt
    exact int32_lt_maxValue_of_lt_primes_size ilt
  have lea : div_search_start ≤ a := by
    unfold div_search_start
    apply Int32.le_iff_toInt_le.mpr
    rw [ati]
    exact Int.natCast_nonneg _
  have alt : a.toInt < primes.size := by
    rw [ati]
    exact Int.ofNat_lt_ofNat_of_lt ilt
  -- TODO: Shorten the proof of "ale" using "alt"
  have ale : a ≤ div_search_finish := by
    unfold div_search_finish
    apply Int32.le_iff_toInt_le.mpr
    rw [ati]
    convert Int.ofNat_le_ofNat_of_le (Nat.le_sub_one_of_lt ilt)
    apply Int32.toInt_ofNat_of_lt (Nat.sub_one_lt_of_le primes_size_pos _)
    exact le_of_lt (lt_trans primes_size_lt_sieve_size (by decide))
  have hsat : div_search_success n a = true := by
    apply div_search_success_sat_of_primes_mem_dvd n a lea alt
    rw [← hpi] at pdvd
    convert pdvd
    rw [ati, Int.natAbs_natCast]
  use a, lea, ale, hsat
  intro b ⟨leb, blta⟩
  apply Int32.not_le.mp at blta
  have bnltz : ¬b < 0 := by
    unfold div_search_start at leb
    exact Int32.not_lt.mpr leb
  have psnle : ¬primes.size ≤ b.toInt := by
    apply Int.not_le.mpr
    exact lt_trans (Int32.lt_iff_toInt_lt.mp blta) alt
  unfold div_search_fail
  rw [dif_neg bnltz, dif_neg psnle]
  simp only [decide_eq_false_iff_not, Int32.not_lt, ge_iff_le]
  apply Int32.le_iff_toInt_le.mpr
  have btinalt : b.toInt.natAbs < primes.size := by
    rw [← int32_toInt_natAbs_lt_iff (Int32.not_lt.mp bnltz)]
    exact Int.not_le.mp psnle
  have pbpos : 0 < primes[b.toInt.natAbs] := by
    exact primes_pos _ (Array.getElem_mem _)
  have pbne : primes[b.toInt.natAbs] ≠ -1 := by
    symm
    apply Int32.ne_of_lt
    exact Int32.lt_trans (by decide) pbpos
  rw [Int32.toInt_div_of_ne_right _ _ pbne, int32_toInt_abs _ ltn]
  rw [Int.tdiv_eq_ediv_of_nonneg (abs_nonneg n.toInt)]
  apply le_div_self_of_le_div_self (Int32.lt_iff_toInt_lt.mp pbpos) _ ple
  rw [← hpi]
  apply Int32.le_iff_toInt_le.mp (primes_nondecreasing _ _ _ ilt)
  apply Int.le_of_ofNat_le_ofNat
  rw [Int.ofNat_natAbs_of_nonneg (Int32.le_iff_toInt_le.mp leb)]
  exact le_of_le_of_eq (le_of_lt (Int32.lt_iff_toInt_lt.mp blta)) ati

def divisor_index_of_ne_none (n : Int32)
  (nenone : divisor_index_opt n ≠ none) : ℕ :=
  ((divisor_index_opt n).get (Option.isSome_iff_ne_none.mpr nenone)).toInt.natAbs

theorem divisor_index_lt_of_ne_none (n : Int32)
  (nenone : divisor_index_opt n ≠ none) :
  divisor_index_of_ne_none n nenone < primes.size := by
  apply (lt_primes_size_iff_le_search_finish _).mpr
  · exact divisor_index_opt_le_of_ne_none n nenone
  · exact divisor_index_opt_ge_of_ne_none n nenone

-- Dereference 'primes' with the result of a success search to get the actual divisor
def divisor_of_search_ne_none (n : Int32)
  (nenone : divisor_index_opt n ≠ none) : Int32 :=
  primes[divisor_index_of_ne_none n nenone]'(
    divisor_index_lt_of_ne_none n nenone
  )

-- If 'divisor_index' successfully found a divisor of 'n', return that
-- Otherwise, 'n' must be prime and is its own smallest divisor
def divisor_search (n : Int32) : Int32 :=
  if h : divisor_index_opt n = none then int32_abs n else
  divisor_of_search_ne_none n h

-- Prove that the search returns '2' as the smallest divisor of zero greater than one
theorem divisor_search_zero : divisor_search 0 = 2 := by
  unfold divisor_search
  have nenone := divisor_index_ne_none_of_zero
  rw [dif_neg nenone]
  unfold divisor_of_search_ne_none
  convert primes_getElem_zero_eq_two
  unfold divisor_index_of_ne_none
  rw [Int.natAbs_eq_zero, ← Int32.toInt_zero]
  apply Int32.toInt_inj.mpr
  apply Int32.le_antisymm _ (divisor_index_opt_ge_of_ne_none _ nenone)
  apply search_opt_first_of_ne_none _ _ nenone _ (Int32.le_refl _)
  exact Or.inl (div_search_success_of_mod2_eq_zero (by decide))

theorem divisor_search_gt_of_gt (n : Int32) (hgt : 1 < n.toInt.natAbs) :
  1 < divisor_search n := by
  unfold divisor_search
  apply Int32.lt_iff_toInt_lt.mpr
  split_ifs with h
  · have nnemv : n ≠ Int32.minValue := by
      contrapose! h; subst h
      exact divisor_index_ne_none_of_minValue
    rw [int32_toInt_abs _ (int32_minval_lt_of_ne_minval _ nnemv.symm)]
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_lt_ofNat_of_lt hgt
  · apply Int.lt_of_add_one_le
    simp only [Int32.reduceToInt, Int.reduceAdd]
    change Int32.toInt (2 : Int32) ≤ _
    apply Int32.le_iff_toInt_le.mp
    rw [← primes_getElem_zero_eq_two]
    apply primes_nondecreasing _ _ (Nat.zero_le _)

-- If the search is successful, the divisor is in-fact a divisor
theorem divisor_search_dvd (n : Int32) :
  (divisor_search n).toInt ∣ n.toInt := by
  rw [← int32_mod_eq_zero_iff_toInt_dvd]
  unfold divisor_search divisor_of_search_ne_none
  by_cases h : divisor_index_opt n = none
  · rw [dif_pos h]
    rcases int32_abs_eq_self_or_neg n with lhs | rhs
    · rw [lhs]
      exact Int32.mod_self
    · rw [rhs]
      rw [int32_mod_neg _ _]
      exact Int32.mod_self
  rw [dif_neg h]
  apply dvd_of_div_search_success_sat
  exact search_opt_sat_of_ne_none (div_search_success n) (exists_search_failure_sat n) h

-- TODO: Consider finding a home for this elsewhere so it can be reused
theorem int32_minValue_lt_of_prime (n : Int32)
  (hprime : Nat.Prime n.toInt.natAbs) :
  Int32.minValue < n := by
  contrapose! hprime
  have neq : n.toInt.natAbs = 2147483648 := by
    rw [Int32.le_antisymm (Int32.not_lt.mp hprime) (Int32.minValue_le _)]
    rfl
  rw [neq]
  norm_num

-- Prove that the divisor search finds the smallest divisor for prime 32-bit integers
theorem divisor_search_first_of_prime (n : Int32)
  (hprime : Nat.Prime n.toInt.natAbs) :
  ∀ a : Int32, 1 < a → a.toInt ∣ n.toInt → divisor_search n ≤ a := by
  intro a lta advd
  have atinn : 0 ≤ a.toInt := by
    apply le_of_lt
    exact lt_trans (by decide) (Int32.lt_iff_toInt_lt.mp lta)
  have advd' := Int.natAbs_dvd_natAbs.mpr advd
  have lta' : 1 < a.toInt.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt (by decide) (Int32.lt_iff_toInt_lt.mp lta)
  have ane : ¬a.toInt.natAbs = 1 := (ne_of_lt lta').symm
  have han := Or.resolve_left (Nat.Prime.eq_one_or_self_of_dvd hprime _ advd') ane
  unfold divisor_search
  by_cases hnone : divisor_index_opt n = none
  · rw [dif_pos hnone]
    by_contra alt
    apply Int32.not_le.mp at alt
    absurd Int.natAbs_lt_natAbs_of_nonneg_of_lt atinn (Int32.lt_iff_toInt_lt.mp alt)
    apply Nat.not_lt.mpr (Nat.le_of_eq _)
    rw [int32_toInt_abs _ (int32_minValue_lt_of_prime _ hprime)]
    rw [Int.natAbs_abs]
    exact han.symm
  rename' hnone => nenone; push_neg at nenone
  rw [dif_neg nenone]
  -- We've proven that if 'n' was too large the search would fail
  -- Since the search search succeeded that would be a contradiction
  -- and we can prove an upper bound on 'n'.
  have nle : n.toInt.natAbs ≤ 999983 := by
    contrapose! nenone
    exact divisor_index_none_of_prime_of_gt n hprime nenone
  -- Get the index of 'n' in "primes"
  rcases mem_primes_of_prime_of_lt _ hprime (lt_of_le_of_lt nle (by decide)) with ⟨p, pmem, hp⟩
  rcases Array.getElem_of_mem pmem with ⟨i, ilt, hi⟩
  have hap : a = p := by
    apply Int32.toInt_inj.mp
    rw [hp, ← Int.ofNat_natAbs_of_nonneg atinn, han]
  rw [hap, ← hi]
  unfold divisor_of_search_ne_none
  apply primes_nondecreasing _ _ _ ilt
  let i' : Int32 := Int32.ofNat i
  have i'ti : i'.toInt = i := by
    unfold i'
    rw [Int32.toInt_ofNat_of_lt (int32_lt_maxValue_of_lt_primes_size ilt)]
  have i'nn : 0 ≤ i' := by
    apply Int32.le_iff_toInt_le.mpr
    rw [i'ti]
    exact Nat.cast_nonneg i
  have i'lt : i'.toInt < primes.size := by
    rw [i'ti]
    exact Int.ofNat_lt_ofNat_of_lt ilt
  have i'sat : div_search_success n i' = true := by
    apply div_search_success_sat_of_primes_mem_dvd _ _ i'nn i'lt
    convert advd
    rw [hap, ← hi]; congr
    rw [i'ti, Int.natAbs_natCast]
  have := search_opt_first_of_ne_none _ _ nenone i' i'nn (Or.inl i'sat)
  rw [Int32.le_iff_toInt_le, i'ti] at this
  apply Int.le_of_ofNat_le_ofNat
  unfold divisor_index_of_ne_none
  rwa [Int.ofNat_natAbs_of_nonneg]
  exact Int32.le_iff_toInt_le.mp (divisor_index_opt_ge_of_ne_none _ nenone)

lemma one_lt_of_ne_zero_of_ne_one {a : ℕ} (ane0 : a ≠ 0) (ane1 : a ≠ 1) : 1 < a :=
  lt_of_le_of_ne (Nat.add_one_le_of_lt (Nat.pos_of_ne_zero ane0)) ane1.symm

-- The smallest divisor greater than 1 is prime
-- TODO: Is the really not already proven in Mathlib?
theorem prime_of_dvd_of_le {p n : ℕ}
  (hdvd : p ∣ n) (hgt : 1 < p)
  (hfirst : ∀ m, 1 < m → m ∣ n → p ≤ m) : Nat.Prime p := by
  by_contra! h
  have ppos : 0 < p := Nat.pos_of_ne_zero (Nat.ne_zero_of_lt hgt)
  have lep : 2 ≤ p := Nat.add_one_le_of_lt hgt
  rcases Nat.exists_dvd_of_not_prime lep h with ⟨m, mdvdp, mne1, mnep⟩
  have mnz : m ≠ 0 := by
    contrapose! lep
    subst lep
    rw [Nat.zero_dvd.mp mdvdp]
    decide
  have mpos := lt_of_le_of_ne (Nat.zero_le _) mnz.symm
  have ltm : 1 < m :=
    one_lt_of_ne_zero_of_ne_one mnz mne1
  have mdvdn : m ∣ n := dvd_trans mdvdp hdvd
  absurd Nat.le_of_dvd ppos mdvdp; push_neg
  exact lt_of_le_of_ne (hfirst m ltm mdvdn) mnep.symm

-- The smallest divisor is less than or equal to its cofactor
theorem le_div_self_of_dvd_of_le {p n : ℕ}
  (hdvd : p ∣ n) (hgt : 1 < p) (hlt : p < n)
  (hfirst : ∀ m, 1 < m → m ∣ n → p ≤ m) : p ≤ n / p := by
  have ppos : 0 < p := Nat.pos_of_ne_zero (Nat.ne_zero_of_lt hgt)
  apply hfirst (n / p) _ (Nat.div_dvd_of_dvd hdvd)
  rwa [← Nat.mul_lt_mul_left ppos, mul_one, Nat.mul_div_cancel' hdvd]

-- The smallest divisor of 'n', if n < SIEVE_SIZE ^ 2,
-- corresponds to an element of "primes"
theorem primes_mem_of_dvd_of_le {p n : ℕ}
  (hdvd : p ∣ n) (hgt : 1 < p) (hlt : p < n) (nlt : n < SIEVE_SIZE ^ 2)
  (hfirst : ∀ m, 1 < m → m ∣ n → p ≤ m) :
  ∃ p' ∈ primes, p'.toInt = p := by
  have pprime := prime_of_dvd_of_le hdvd hgt hfirst
  apply mem_primes_of_prime_of_lt p pprime
  by_contra! lep
  have ppos : 0 < p := Nat.pos_of_ne_zero (Nat.ne_zero_of_lt hgt)
  absurd le_div_self_of_dvd_of_le hdvd hgt hlt hfirst; push_neg
  rw [← Nat.mul_lt_mul_left ppos, Nat.mul_div_cancel' hdvd]
  apply lt_of_lt_of_le nlt
  rw [Nat.pow_two]
  exact Nat.mul_le_mul lep lep

-- The divisor search does in-fact find the smallest divisor of 'n' greater than 1
theorem divisor_search_first (n : Int32) :
  ∀ a : Int32, 1 < a → a.toInt ∣ n.toInt → divisor_search n ≤ a := by
  intro a' lta' a'dvd
  have a'tinn : 0 ≤ a'.toInt := by
    apply le_of_lt
    exact lt_trans (by decide) (Int32.lt_iff_toInt_lt.mp lta')
  -- Handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    rw [divisor_search_zero]
    apply Int32.le_iff_toInt_le.mpr
    convert Int.add_one_le_of_lt (Int32.lt_iff_toInt_lt.mp lta')
  rename' nz => nnz; push_neg at nnz
  -- Show the absolute value of n is not 1
  have nne1 : n.toInt.natAbs ≠ 1 := by
    contrapose! lta'
    rename' lta' => n1
    apply Int32.not_lt.mpr (Int32.le_of_eq (Int32.toInt_inj.mp _))
    simp only [Int32.reduceToInt]
    apply Int.ofNat_inj.mpr at n1
    by_cases nnp : n.toInt ≤ 0
    · rw [Int.ofNat_natAbs_of_nonpos nnp, Nat.cast_one] at n1
      rw [← Int.dvd_neg, n1] at a'dvd
      exact Int.eq_one_of_dvd_one a'tinn a'dvd
    push_neg at nnp
    have nnn : 0 ≤ n.toInt := le_of_lt nnp
    rw [Int.ofNat_natAbs_of_nonneg nnn, Nat.cast_one] at n1
    rw [n1] at a'dvd
    exact Int.eq_one_of_dvd_one a'tinn a'dvd
  -- Prove the absolute value of n is greater than 1
  have npos : 0 < n.toInt.natAbs := by
    apply Nat.pos_of_ne_zero
    contrapose! nnz
    rwa [← Int32.toInt_inj, Int32.toInt_zero, ← Int.natAbs_eq_zero]
  have ltabs : 1 < n.toInt.natAbs := by
    apply Nat.lt_of_le_of_ne (Nat.add_one_le_of_lt npos) nne1.symm
  have dvdex : ∃ m, 1 < m ∧ m ∣ n.toInt.natAbs := by
    use n.toInt.natAbs
  -- Let 'p' be the smallest divisor of n.toInt.natAbs greater than 1
  let p : ℕ := Nat.find dvdex
  have psat : 1 < p ∧ p ∣ n.toInt.natAbs := Nat.find_spec dvdex
  have pfirst : ∀ m, 1 < m → m ∣ n.toInt.natAbs → p ≤ m :=
    fun m h h' ↦ Nat.find_le (And.intro h h')
  have pprime := prime_of_dvd_of_le psat.2 psat.1 pfirst
  have ppos : 0 < p := lt_trans (by decide) psat.1
  -- Next, use a prior result to show that the absolute value of 'n' is prime
  by_cases hprime : Nat.Prime n.toInt.natAbs
  · exact divisor_search_first_of_prime _ hprime _ lta' a'dvd
  have plt : p < n.toInt.natAbs := by
    apply Nat.lt_of_le_of_ne (Nat.le_of_dvd npos psat.2)
    contrapose! hprime
    rwa [← hprime]
  have nlt : n.toInt.natAbs < SIEVE_SIZE ^ 2 := by
    apply lt_of_le_of_lt (int32_natAbs_toInt_le _)
    decide
  -- 'p' corresponds to an element in "primes"
  have exmem := primes_mem_of_dvd_of_le psat.2 psat.1 plt nlt pfirst
  -- Now we can prove that p * p is not greater than the absolute value of 'n'
  --have ledvd : p ≤ n.toInt.natAbs / p :=
  --  le_div_self_of_dvd_of_le psat.2 psat.1 plt pfirst
  rcases exmem with ⟨p', p'mem, hp'p⟩
  rcases Array.getElem_of_mem p'mem with ⟨i, ilt, hip'⟩
  -- Now that we have the index of p in "primes", get the corresponding Int32
  -- and prove its bounds
  let i' : Int32 := Int32.ofNat i
  have i'ti : i'.toInt = i :=
    Int32.toInt_ofNat_of_lt (int32_lt_maxValue_of_lt_primes_size ilt)
  have lei' : div_search_start ≤ i' := by
    apply Int32.le_iff_toInt_le.mpr
    rw [i'ti]
    exact Int.natCast_nonneg _
  have i'tilt : i'.toInt < primes.size :=
    i'ti ▸ Int.ofNat_lt_ofNat_of_lt ilt
  have nenone : divisor_index_opt n ≠ none :=
    divisor_index_ne_none_of_not_prime _ hprime ltabs
  -- Now that we've identified i and p, we can actually start the proof!
  unfold divisor_search
  rw [dif_neg nenone]
  -- Prove a some useful facts about a'
  let a : ℕ := a'.toInt.natAbs
  have acast : a = a'.toInt := by
    unfold a
    rw [Int.ofNat_natAbs_of_nonneg a'tinn]
  have ane1 : a ≠ 1 := by
    intro h
    rw [← Int.ofNat_inj, acast] at h
    absurd Int32.lt_iff_toInt_lt.mp lta'
    rw [h]; decide
  have lta : 1 < a := by
      unfold a
      apply Int.lt_of_ofNat_lt_ofNat
      rw [Int.ofNat_natAbs_of_nonneg a'tinn]
      exact Int32.lt_iff_toInt_lt.mp lta'
  have advd : a ∣ n.toInt.natAbs :=
    Int.natAbs_dvd_natAbs.mpr a'dvd
  let q' := divisor_of_search_ne_none n nenone
  change q' ≤ a'
  have q'nn : 0 ≤ q' :=
    primes_nonneg _ (Array.getElem_mem _)
  let q := q'.toInt.natAbs
  have q'ti : q'.toInt = q := by
    unfold q
    rw [Int.ofNat_natAbs_of_nonneg]
    exact Int32.le_iff_toInt_le.mp (primes_nonneg' _ _)
  have ltq : 1 < q := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← q'ti]
    unfold q' divisor_of_search_ne_none
    apply Int.lt_of_add_one_le
    rw [Nat.cast_one, one_add_one_eq_two]
    exact Int32.le_iff_toInt_le.mp (primes_ge _ _)
  apply Int32.le_iff_toInt_le.mpr
  rw [← Int.ofNat_natAbs_of_nonneg a'tinn]
  convert Int.ofNat_le_ofNat_of_le (pfirst a lta advd)
  apply le_antisymm
  · rw [← hp'p, ← hip']
    apply Int32.le_iff_toInt_le.mp
    unfold q' divisor_of_search_ne_none
    apply primes_nondecreasing
    apply Int.le_of_ofNat_le_ofNat
    rw [← i'ti]
    have hnn := Int32.le_iff_toInt_le.mp (divisor_index_opt_ge_of_ne_none _ nenone)
    unfold divisor_index_of_ne_none
    rw [Int.ofNat_natAbs_of_nonneg hnn]
    apply Int32.le_iff_toInt_le.mp
    apply search_opt_first_of_ne_none _ _ nenone i' lei' (Or.inl _)
    apply div_search_success_sat_of_primes_mem_dvd _ _ lei' i'tilt
    apply Int.natAbs_dvd_natAbs.mp
    convert psat.2
    apply Int.ofNat_inj.mp
    rw [← hp'p, ← hip']
    rw [Int.ofNat_natAbs_of_nonneg (Int32.le_iff_toInt_le.mp (primes_nonneg' _ _))]
    congr
    rw [i'ti, Int.natAbs_natCast]
  · rw [q'ti]
    apply Int.ofNat_le_ofNat_of_le
    apply pfirst q ltq _
    rw [← Int.ofNat_dvd, ← q'ti, Int.dvd_natAbs]
    rw [← int32_mod_eq_zero_iff_toInt_dvd]
    apply dvd_of_div_search_success_sat
    exact search_opt_sat_of_ne_none _ _ nenone

-- Find the smallest positive divisor of 'n'
-- If n is "small" we can look up the answer in 'divs' otherwise
-- search for the result using 'divisor_search'
def smallest_divisor (n : Int32) : Int32 :=
  if nnemv : n = Int32.minValue then 2 else
  if lenabs : int32_abs n < 2 then int32_abs n else
  if nabslt : int32_abs n < SIEVE_SIZE_32 then divs[n.toInt.natAbs]'(by
    push_neg at nnemv
    have ltn := Int32.lt_of_le_of_ne (Int32.minValue_le n) nnemv.symm
    apply Int32.lt_iff_toInt_lt.mp at nabslt
    rw [int32_toInt_abs _ ltn, Int.abs_eq_natAbs, sieve_size_32_toInt] at nabslt
    rw [divs_size]
    exact Int.lt_of_ofNat_lt_ofNat nabslt
  ) else divisor_search n

theorem smallest_divisor_zero :
  smallest_divisor 0 = 0 := by
  unfold smallest_divisor
  rw [dif_neg (by decide), dif_pos (by decide)]
  rfl

theorem smallest_divisor_minValue :
  smallest_divisor Int32.minValue = 2 := by
  unfold smallest_divisor
  rw [dif_pos rfl]

theorem smallest_divisor_nonneg (n : Int32) :
  0 ≤ smallest_divisor n := by
  unfold smallest_divisor
  by_cases nnemv : n = Int32.minValue
  · rw [dif_pos nnemv]; decide
  push_neg at nnemv
  have mvltn : Int32.minValue < n :=
    int32_minval_lt_of_ne_minval _ nnemv.symm
  rw [dif_neg nnemv]
  by_cases lenabs : int32_abs n < 2
  · rw [dif_pos lenabs]
    exact int32_abs_nonneg _ mvltn
  rw [dif_neg lenabs]
  apply Int32.not_lt.mp at lenabs
  have ltn : 1 < n.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat (Int.lt_of_add_one_le _)
    apply Int32.le_iff_toInt_le.mp at lenabs
    rw [int32_toInt_abs _ mvltn, Int.abs_eq_natAbs _] at lenabs
    exact lenabs
  apply Int32.le_of_lt
  by_cases nabslt : int32_abs n < SIEVE_SIZE_32
  · rw [dif_pos nabslt]
    exact Int32.lt_trans Int32.zero_lt_one (divs_gt_one _ ltn _)
  rw [dif_neg nabslt]
  exact Int32.lt_trans Int32.zero_lt_one (divisor_search_gt_of_gt _ ltn)

theorem smallest_divisor_dvd (n : Int32) :
  (smallest_divisor n).toInt ∣ n.toInt := by
  unfold smallest_divisor
  by_cases nnemv : n = Int32.minValue
  · rw [dif_pos nnemv]
    subst nnemv; decide
  push_neg at nnemv
  have mvltn : Int32.minValue < n :=
    int32_minval_lt_of_ne_minval _ nnemv.symm
  rw [dif_neg nnemv]
  by_cases lenabs : int32_abs n < 2
  · rw [dif_pos lenabs, int32_toInt_abs _ mvltn]
    exact abs_dvd_self _
  rw [dif_neg lenabs]
  apply Int32.not_lt.mp at lenabs
  have ltn : 1 < n.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat (Int.lt_of_add_one_le _)
    apply Int32.le_iff_toInt_le.mp at lenabs
    rw [int32_toInt_abs _ mvltn, Int.abs_eq_natAbs _] at lenabs
    exact lenabs
  by_cases nabslt : int32_abs n < SIEVE_SIZE_32
  · rw [dif_pos nabslt, ← Int.dvd_natAbs]
    exact (divs_getElem_dvd_and_le _ _ ltn).1
  rw [dif_neg nabslt]
  exact divisor_search_dvd _

theorem smallest_divisor_le (n : Int32) :
  ∀ (a : Int32), 1 < a → a.toInt ∣ n.toInt → smallest_divisor n ≤ a := by
  intro a lta advd
  unfold smallest_divisor
  have ltati := Int32.lt_iff_toInt_lt.mp lta
  simp only [Int32.reduceToInt] at ltati
  apply Int32.le_iff_toInt_le.mpr
  by_cases nnemv : n = Int32.minValue
  · rw [dif_pos nnemv]
    simp only [Int32.reduceToInt]
    rw [← one_add_one_eq_two]
    apply Int.add_one_le_of_lt ltati
  rw [dif_neg nnemv]
  push_neg at nnemv
  have mvltn : Int32.minValue < n :=
    int32_minval_lt_of_ne_minval _ nnemv.symm
  by_cases lenabs : int32_abs n < 2
  · have htia := int32_toInt_abs _ mvltn
    rw [dif_pos lenabs, htia]
    apply Int32.lt_iff_toInt_lt.mp at lenabs
    rw [htia] at lenabs
    simp only [Int32.reduceToInt] at lenabs
    rw [← one_add_one_eq_two] at lenabs
    exact le_of_lt (Int.lt_of_le_of_lt (Int.le_of_lt_add_one lenabs) ltati)
  rw [dif_neg lenabs]
  apply Int32.not_lt.mp at lenabs
  have ati : a.toInt = a.toInt.natAbs := by
    symm
    apply Int.ofNat_natAbs_of_nonneg (Int.le_of_lt _)
    exact lt_trans (by decide) ltati
  have lta' : 1 < a.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← ati]
    exact ltati
  have ltn : 1 < n.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat (Int.lt_of_add_one_le _)
    apply Int32.le_iff_toInt_le.mp at lenabs
    rw [int32_toInt_abs _ mvltn, Int.abs_eq_natAbs _] at lenabs
    exact lenabs
  by_cases nabslt : int32_abs n < SIEVE_SIZE_32
  · rw [dif_pos nabslt, ati]
    exact (divs_getElem_dvd_and_le _ _ ltn).2 _ lta' (Int.natAbs_dvd_natAbs.mpr advd)
  rw [dif_neg nabslt]
  apply Int32.le_iff_toInt_le.mp
  exact divisor_search_first _ _ lta advd

theorem smallest_divisor_le' (n : Int32) :
  ∀ a, 1 < a → a ∣ n.toInt.natAbs → (smallest_divisor n).toInt ≤ a := by
  intro a lta advd
  by_cases nnz : n = 0
  · subst nnz
    rw [smallest_divisor_zero]
    exact Int.natCast_nonneg _
  push_neg at nnz
  have npos : 0 < n.toInt.natAbs := by
    apply Int.natAbs_pos.mpr
    contrapose! nnz
    exact Int32.toInt_inj.mp nnz
  by_cases nnemv : n = Int32.minValue
  · subst nnemv
    rw [smallest_divisor_minValue]
    simp only [Int32.reduceToInt, Nat.ofNat_le_cast]
    exact Nat.add_one_le_of_lt lta
  push_neg at nnemv
  have mvltn : Int32.minValue < n :=
    int32_minval_lt_of_ne_minval _ nnemv.symm
  let a' : Int32 := Int32.ofNat a
  have ha : a'.toInt = a := by
    apply Int32.toInt_ofNat_of_lt (lt_of_le_of_lt _ (int32_natAbs_toInt_lt _ mvltn))
    exact Nat.le_of_dvd npos advd
  rw [← ha]
  have lta' : 1 < a' := by
    apply Int32.lt_iff_toInt_lt.mpr
    rw [ha]
    exact Int.ofNat_lt_ofNat_of_lt lta
  apply Int32.le_iff_toInt_le.mp
  apply smallest_divisor_le _ _ lta'
  rw [ha]
  exact Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr advd)

-- Lower bound on the smallest divisor
-- Note that this only applies if 'n' is not 1, 0, or -1
theorem smallest_divisor_gt (n : Int32) (hgt : 1 < n.toInt.natAbs) : 1 < smallest_divisor n := by
  unfold smallest_divisor
  by_cases nnemv : n = Int32.minValue
  · rw [dif_pos nnemv]; decide
  push_neg at nnemv
  rw [dif_neg nnemv]
  have lenabs : ¬int32_abs n < 2 := by
    contrapose! hgt
    apply Int.le_of_ofNat_le_ofNat
    rw [← Int.abs_eq_natAbs, Nat.cast_one]
    rw [← int32_toInt_abs _ (int32_minval_lt_of_ne_minval _ nnemv.symm)]
    exact Int.le_of_lt_add_one (Int32.lt_iff_toInt_lt.mp hgt)
  rw [dif_neg lenabs]
  apply Int32.not_lt.mp at lenabs
  by_cases nabslt : int32_abs n < SIEVE_SIZE_32
  · rw [dif_pos nabslt]
    apply divs_gt_one _ hgt
  rw [dif_neg nabslt]
  exact divisor_search_gt_of_gt _ hgt

-- If a number is not prime and is greater than one,
-- its smallest divisor is properly less than its absolute value
theorem smallest_divisor_lt_of_not_prime (n : Int32)
  (hgt : 1 < n.toInt.natAbs) (hnprime : ¬Nat.Prime n.toInt.natAbs) :
  (smallest_divisor n).toInt < n.toInt.natAbs := by
  let d := smallest_divisor n
  have dtinn : 0 ≤ d.toInt :=
    Int32.le_iff_toInt_le.mp (smallest_divisor_nonneg _)
  have hdvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
  have npos : (0 : ℤ) < n.toInt.natAbs :=
    lt_trans zero_lt_one (Int.ofNat_lt_ofNat_of_lt hgt)
  apply lt_of_le_of_ne (Int.le_of_dvd npos (Int.dvd_natAbs.mpr hdvd))
  by_contra! h
  rcases Nat.exists_prime_and_dvd (Nat.ne_of_lt hgt).symm with ⟨p, pprime, pdvd⟩
  --let p' : Int32 := Int32.ofNat p
  have pnen : p ≠ n.toInt.natAbs := by
    contrapose! hnprime
    rwa [← hnprime]
  have plt : p < n.toInt.natAbs := by
    apply lt_of_le_of_ne _ pnen
    apply Nat.le_of_dvd _ pdvd
    exact Int.lt_of_ofNat_lt_ofNat npos
  absurd plt; push_neg
  apply Int.le_of_ofNat_le_ofNat
  -- Zero and one are not prime, so p is at least two
  have pgt : 1 < p := by
    contrapose! pprime
    by_cases pz : p = 0
    · subst pz; norm_num
    rename' pz => pnz; push_neg at pnz
    have lep : 1 ≤ p := Nat.add_one_le_of_lt (lt_of_le_of_ne (Nat.zero_le _) pnz.symm)
    rw [Nat.le_antisymm pprime lep]
    norm_num
  rw [← h]
  exact smallest_divisor_le' n p pgt pdvd

-- If 'n' is not prime, its smallest divisor is in "primes"
theorem smallest_divisor_mem_primes (n : Int32)
  (hgt : 1 < n.toInt.natAbs) (hnprime : ¬Nat.Prime n.toInt.natAbs) :
  smallest_divisor n ∈ primes := by
  let d := smallest_divisor n
  have dtinn : 0 ≤ d.toInt :=
    Int32.le_iff_toInt_le.mp (smallest_divisor_nonneg n)
  let hdvd : d.toInt.natAbs ∣ n.toInt.natAbs :=
    Int.natAbs_dvd_natAbs.mpr (smallest_divisor_dvd n)
  have hd : d.toInt.natAbs = d.toInt :=
    Int.ofNat_natAbs_of_nonneg dtinn
  let ltp : 1 < d :=
    smallest_divisor_gt _ hgt
  have ltp' : 1 < d.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat (lt_of_lt_of_eq _ hd.symm)
    exact Int32.lt_iff_toInt_lt.mp ltp
  have plt : d.toInt.natAbs < n.toInt.natAbs := by
    apply Int.lt_of_ofNat_lt_ofNat (lt_of_eq_of_lt hd _)
    exact smallest_divisor_lt_of_not_prime _ hgt hnprime
  by_cases nnemv : n = Int32.minValue
  · subst nnemv
    rw [smallest_divisor_minValue, ← primes_getElem_zero_eq_two]
    exact Array.getElem_mem primes_size_pos
  push_neg at nnemv
  have mvltn : Int32.minValue < n :=
    int32_minval_lt_of_ne_minval _ nnemv.symm
  have nlt : n.toInt.natAbs < SIEVE_SIZE ^ 2 := by
    exact lt_trans (int32_natAbs_toInt_lt n mvltn) (by decide)
  have hfirst : ∀ m, 1 < m → m ∣ n.toInt.natAbs → d.toInt.natAbs ≤ m := by
    intro m ltm mdvd
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.ofNat_natAbs_of_nonneg dtinn]
    exact smallest_divisor_le' n m ltm mdvd
  rcases primes_mem_of_dvd_of_le hdvd ltp' plt nlt hfirst with ⟨p, pmem, hp⟩
  rw [hd] at hp
  rw [Int32.toInt_inj.mp hp] at pmem
  exact pmem

-- The value returned by 'smallest_divisor' corresponds to a prime
theorem smallest_divisor_prime (n : Int32) (hgt : 1 < n.toInt.natAbs) :
  ∃ p, Nat.Prime p ∧ (smallest_divisor n).toInt = p := by
  let d := smallest_divisor n
  have dtinn : 0 ≤ d.toInt := Int32.le_iff_toInt_le.mp (smallest_divisor_nonneg n)
  have hdti : d.toInt = d.toInt.natAbs := (Int.ofNat_natAbs_of_nonneg dtinn).symm
  have ddvd : d.toInt.natAbs ∣ n.toInt.natAbs := by
    apply Int.ofNat_dvd.mp
    rw [Int.natAbs_dvd, Int.dvd_natAbs]
    exact smallest_divisor_dvd n
  have dne1 : d.toInt.natAbs ≠ 1 := by
    symm
    apply ne_of_lt (Int.lt_of_ofNat_lt_ofNat _)
    rw [← hdti, Int.ofNat_one, ← Int32.toInt_one]
    exact Int32.lt_iff_toInt_lt.mp (smallest_divisor_gt _ hgt)
  by_cases hprime : Nat.Prime n.toInt.natAbs
  · use n.toInt.natAbs, hprime
    contrapose! hprime
    apply (Nat.not_prime_iff_exists_dvd_ne (Nat.add_one_le_of_lt hgt)).mpr
    use d.toInt.natAbs, ddvd, dne1
    contrapose! hprime
    apply Int.natCast_inj.mpr at hprime
    rwa [hdti]
  have dmem : d ∈ primes := smallest_divisor_mem_primes _ hgt hprime
  rcases prime_of_mem_primes _ dmem with ⟨p, hp, pprime⟩
  use p, pprime

structure PrimePower where
  p : Int32
  x : Int32
  prime : ∃ q, Nat.Prime q ∧ p.toInt = q
  xpos : 0 < x

theorem prime_power_prime_pos (pp : PrimePower) : 0 < pp.p := by
  rcases pp.prime with ⟨q, qprime, hq⟩
  apply Int32.lt_iff_toInt_lt.mpr
  rw [hq]
  apply lt_of_le_of_ne (Int.natCast_nonneg _)
  contrapose! qprime
  rw [← Int.ofNat_inj.mp qprime]
  norm_num

def prime_power_singleton (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) : PrimePower where
  p := p
  x := 1
  prime := hprime
  xpos := by decide

@[simp] theorem prime_power_singleton_prime (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) :
  (prime_power_singleton p hprime).p = p := rfl

def prime_power_inc (P : PrimePower) (hmv : P.x ≠ Int32.maxValue) : PrimePower where
  p := P.p
  x := P.x + 1
  prime := P.prime
  xpos := by
    apply Int32.lt_trans P.xpos (Int32.lt_iff_toInt_lt.mpr _)
    convert Int.lt_add_one_of_le (Int.le_refl _)
    exact int32_toInt_succ _ (Int32.lt_of_le_of_ne (Int32.le_maxValue _) hmv)

@[simp] theorem prime_power_inc_prime (P : PrimePower) (hmv : P.x ≠ Int32.maxValue) :
  (prime_power_inc P hmv).p = P.p := rfl

-- Uh... why doesn't this already exist?
lemma array_back_congr {α : Type} {A B : Array α} (h : A = B) (hnil : A ≠ #[]) :
  A.back (Array.size_pos_iff.mpr hnil) = B.back (h ▸ (Array.size_pos_iff.mpr hnil)) := by congr

-- Same with this!
lemma array_back_push {α : Type} (A : Array α) (x : α) :
  (A.push x).back = x := by
  have spos : 0 < (A.push x).size := by
    rw [Array.size_push]
    exact Nat.add_one_pos _
  rw [Array.back_eq_getElem spos]
  convert Array.getElem_push_eq
  rw [Array.size_push, Nat.add_one_sub_one _]

@[ext] structure Factorization where
  A : Array PrimePower
  pinc : ∀ i, (islt : i + 1 < A.size) → A[i].p < A[i+1].p

def fac_one : Factorization where
  A := #[]
  pinc := by
    intro i islt
    absurd islt; push_neg
    rw [Array.size_empty]
    exact le_of_lt (Nat.add_one_pos _)

@[simp] theorem fac_one_array : fac_one.A = #[] := rfl

theorem fac_empty_iff {F : Factorization} : F = fac_one ↔ F.A = #[] :=
  ⟨fun h ↦ fac_one_array ▸ (F.ext_iff.mp h), fun h ↦ F.ext (Eq.trans h fac_one_array.symm)⟩

def fac_singleton (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) : Factorization where
  A := Array.singleton (prime_power_singleton p hprime)
  pinc := by
    intro i islt
    absurd islt; push_neg
    simp

theorem fac_singleton_ne_one (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) : fac_singleton p hprime ≠ fac_one := by
  unfold fac_singleton
  intro h
  absurd Array.size_eq_zero_iff.mpr (fac_empty_iff.mp h)
  simp

def fac_back (F : Factorization) (hnil : F.A ≠ #[]) : PrimePower :=
  F.A.back (Array.size_pos_iff.mpr hnil)

@[simp] theorem fac_back_eq_back (F : Factorization) (hnil : F.A ≠ #[]) :
  fac_back F hnil = F.A.back (Array.size_pos_iff.mpr hnil) := rfl

theorem fac_back_congr {F₁ F₂ : Factorization} (h : F₁ = F₂) (hnil : F₁.A ≠ #[]) :
  fac_back F₁ hnil = fac_back F₂ (h ▸ hnil) := by
  rw [fac_back_eq_back, fac_back_eq_back]
  exact array_back_congr (Factorization.ext_iff.mp h) hnil

@[simp] theorem fac_back_singleton (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) :
  (fac_back (fac_singleton p hprime) (
    fun h ↦ fac_singleton_ne_one p hprime (fac_empty_iff.mpr h)
  )) = prime_power_singleton p hprime := by
  unfold fac_singleton
  rw [fac_back_eq_back]
  simp

theorem fac_back_eq_getElem (F : Factorization) (hnil : F.A ≠ #[]) :
  fac_back F hnil = F.A[F.A.size - 1]'(
    Nat.sub_lt (Array.size_pos_iff.mpr hnil) (by decide)
  ) := by
  unfold fac_back
  rw [Array.back_eq_getElem]

def fac_pop (F : Factorization) : Factorization where
  A := F.A.pop
  pinc := by
    intro i islt
    rw [Array.getElem_pop, Array.getElem_pop]
    apply F.pinc

@[simp] theorem fac_pop_array (F : Factorization) :
  (fac_pop F).A = F.A.pop := rfl

@[simp] theorem fac_pop_size (F : Factorization) :
  (fac_pop F).A.size = F.A.size - 1 := by
  unfold fac_pop; dsimp
  exact Array.size_pop

@[simp] theorem fac_pop_singleton (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) :
  fac_pop (fac_singleton p hprime) = fac_one := by
  unfold fac_singleton
  apply fac_empty_iff.mpr
  simp

@[simp] theorem fac_pop_getElem (F : Factorization) :
  ∀ i, (ilt : i < (fac_pop F).A.size) → (fac_pop F).A[i]'ilt = F.A[i]'(by
    rw [fac_pop_size] at ilt
    exact lt_of_lt_of_le ilt (Nat.sub_le _ _)
) := fun _ _ ↦ Array.getElem_pop _

def fac_push (F : Factorization) (pp : PrimePower)
  (hgt : (hnil : F.A ≠ #[]) → (fac_back F hnil).p < pp.p) : Factorization where
  A := F.A.push pp
  pinc := by
    intro i islt
    rw [Array.size_push, Nat.add_one_lt_add_one_iff] at islt
    rw [Array.getElem_push_lt islt]
    by_cases hnil : F.A = #[]
    · rw [hnil] at islt
      simp at islt
    push_neg at hnil
    by_cases islt' : i + 1 < F.A.size
    · rw [Array.getElem_push_lt]
      exact F.pinc i islt'
    rename' islt' => leis; push_neg at leis
    have iseq : i + 1 = F.A.size :=
      le_antisymm (Nat.add_one_le_of_lt islt) leis
    convert hgt hnil
    · rw [fac_back_eq_getElem]; congr
      rw [← iseq, Nat.add_one_sub_one]
    · convert Array.getElem_push_eq

theorem fac_pop_push (F : Factorization) (pp : PrimePower)
  (hgt : (hnil : F.A ≠ #[]) → (fac_back F hnil).p < pp.p) :
  fac_pop (fac_push F pp hgt) = F := by
  apply Factorization.ext
  exact Array.pop_push

@[simp] theorem fac_push_ne_one (F : Factorization) (pp : PrimePower)
  (hgt : (hnil : F.A ≠ #[]) → (fac_back F hnil).p < pp.p) :
  fac_push F pp hgt ≠ fac_one :=
  fun h ↦ False.elim (Array.push_ne_empty (fac_empty_iff.mp h))

@[simp] theorem fac_push_array_ne_empty (F : Factorization) (pp : PrimePower)
  (hgt : (hnil : F.A ≠ #[]) → (fac_back F hnil).p < pp.p) :
  (fac_push F pp hgt).A ≠ #[] :=
  fun h ↦ False.elim ((fac_push_ne_one F pp hgt) (fac_empty_iff.mpr h))

theorem fac_push_back (F : Factorization) (pp : PrimePower)
  (hgt : (hnil : F.A ≠ #[]) → (fac_back F hnil).p < pp.p) :
  fac_back (fac_push F pp hgt) (
    fun h ↦ False.elim ((fac_push_ne_one F pp hgt) (fac_empty_iff.mpr h))
  ) = pp := by
  unfold fac_push
  rw [fac_back_eq_back, array_back_push]

def fac_appendable (F : Factorization) (p : Int32) : Prop :=
  (hnil : F.A ≠ #[]) → p = (fac_back F hnil).p → (fac_back F hnil).x ≠ Int32.maxValue

def fac_append (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hinc : (hnil : F.A ≠ #[]) → (fac_back F hnil).p ≤ p) : Factorization :=
  if hsz : F.A.size = 0 then fac_singleton p hprime else
    have hnil : F.A ≠ #[] := by
      contrapose! hsz
      rw [hsz]; simp
    if heq : p = (fac_back F hnil).p then
      let pp : PrimePower := fac_back F hnil
      fac_push (fac_pop F) (prime_power_inc pp (happ hnil heq)) (by
        intro hnil'; unfold pp
        push_neg at hsz
        rw [fac_back_eq_getElem, prime_power_inc_prime]
        rw [fac_back_eq_getElem, fac_pop_getElem]
        have hlt : F.A.size - 2 + 1 < F.A.size := by
          have := Array.size_pos_iff.mpr hnil'
          rw [fac_pop_size] at this
          omega
        convert F.pinc (F.A.size - 2) hlt using 3
        · rw [fac_pop_size]; rfl
        · omega
      )
    else
      fac_push F (prime_power_singleton p hprime) (by
        intro _
        rw [prime_power_singleton_prime]
        push_neg at heq
        exact Int32.lt_of_le_of_ne (hinc hnil) heq.symm
      )

theorem fac_append_of_size_eq_zero (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q)
  (happ : fac_appendable F p) (hsz : F.A.size = 0) :
  fac_append F p hprime happ
    (fun h ↦ False.elim (h (Array.size_eq_zero_iff.mp hsz))) = fac_singleton p hprime := by
  unfold fac_append; dsimp
  rw [dif_pos hsz]

theorem fac_append_of_back_power_eq (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hnil : F.A ≠ #[]) (heqp : (fac_back F hnil).p = p) :
  fac_append F p hprime happ (fun _ ↦ (Int32.le_of_eq heqp)) =
  fac_push (fac_pop F) (prime_power_inc (fac_back F hnil) (happ hnil heqp.symm)) (by
    -- TODO: This is duplicated from the definition of 'fac_append'
    -- Can we avoid doing that?
    intro hnil'
    rw [fac_back_eq_getElem, prime_power_inc_prime]
    rw [fac_back_eq_getElem, fac_pop_getElem]
    have hlt : F.A.size - 2 + 1 < F.A.size := by
      have := Array.size_pos_iff.mpr hnil'
      rw [fac_pop_size] at this
      omega
    convert F.pinc (F.A.size - 2) hlt using 3
    · rw [fac_pop_size]; rfl
    · omega
  ) := by
  unfold fac_append; dsimp
  rw [dif_neg (ne_of_lt (Array.size_pos_iff.mpr hnil)).symm]
  rw [fac_back_eq_back] at heqp
  rw [dif_pos heqp.symm]

theorem fac_append_of_back_power_lt (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hnil : F.A ≠ #[]) (hltp : (fac_back F hnil).p < p) :
  fac_append F p hprime happ (fun _ ↦ Int32.le_of_lt hltp) =
  fac_push F (prime_power_singleton p hprime) (
    fun _ ↦ Int32.lt_of_lt_of_le hltp (Int32.le_of_eq (prime_power_singleton_prime p hprime))
  ) := by
  unfold fac_append; dsimp
  rw [dif_neg (ne_of_lt (Array.size_pos_iff.mpr hnil)).symm]
  rw [fac_back_eq_back] at hltp
  rw [dif_neg (Int32.ne_of_lt hltp).symm]

theorem fac_append_ne_one (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hinc : (hnil : F.A ≠ #[]) → (fac_back F hnil).p ≤ p) :
  fac_append F p hprime happ hinc ≠ fac_one := by
  unfold fac_append
  by_cases hsz : F.A.size = 0
  · rw [dif_pos hsz]
    exact fac_singleton_ne_one _ hprime
  rw [dif_neg hsz]
  rename' hsz => hsnz; push_neg at hsnz
  have hnil : F.A ≠ #[] :=
    fun h ↦ hsnz (Array.size_eq_zero_iff.mpr h)
  by_cases heq : p = (fac_back F hnil).p
  · rw [dif_pos heq]
    exact fac_push_ne_one _ _ _
  rw [dif_neg heq]
  rename' heq => hne; push_neg at hne
  exact fac_push_ne_one _ _ _

theorem fac_append_array_ne_nil (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hinc : (hnil : F.A ≠ #[]) → (fac_back F hnil).p ≤ p) :
  (fac_append F p hprime happ hinc).A ≠ #[] := by
  intro h
  apply fac_append_ne_one
  exact fac_empty_iff.mpr h

theorem fac_append_back_power (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hinc : (hnil : F.A ≠ #[]) → (fac_back F hnil).p ≤ p) :
  (fac_back (fac_append F p hprime happ hinc) (
    fun h ↦ (fac_append_ne_one F p hprime happ hinc) (fac_empty_iff.mpr h)
  )).p = p := by
  have happnil : (fac_append F p hprime happ hinc).A ≠ #[] := by
    apply fac_append_array_ne_nil
  by_cases hsz : F.A.size = 0
  · rw [fac_back_congr (fac_append_of_size_eq_zero F p hprime happ hsz) happnil]
    rw [fac_back_singleton]; rfl
  rename' hsz => hsnz; push_neg at hsnz
  have hnil : F.A ≠ #[] :=
    fun h ↦ hsnz (Array.size_eq_zero_iff.mpr h)
  by_cases heq : p = (fac_back F hnil).p
  · symm at heq
    have := fac_append_of_back_power_eq F p hprime happ hnil heq
    rw [fac_back_congr this happnil, fac_push_back]
    rwa [prime_power_inc_prime]
  rename' heq => hne; push_neg at hne
  have ltp := Int32.lt_of_le_of_ne (hinc hnil) hne.symm
  have := fac_append_of_back_power_lt F p hprime happ hnil ltp
  rw [fac_back_congr this happnil, fac_push_back]
  exact prime_power_singleton_prime p hprime

-- Calculate the natural number corresponding to a prime power
def prime_power_to_nat (P : PrimePower) : ℕ :=
  P.p.toInt.natAbs ^ P.x.toInt.natAbs

theorem prime_power_to_nat_pos (P : PrimePower) :
  0 < prime_power_to_nat P := by
  apply Nat.pow_pos
  rcases P.prime with ⟨q, hprime, hq⟩
  rw [hq, Int.natAbs_natCast]
  contrapose! hprime
  rw [Nat.le_zero.mp hprime]
  norm_num

theorem prime_power_to_nat_singleton (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) :
  prime_power_to_nat (prime_power_singleton p hprime) = p.toInt := by
  unfold prime_power_to_nat prime_power_singleton; dsimp
  have ptinn : 0 ≤ p.toInt := by
    rcases hprime with ⟨q, qprime, hq⟩
    rw [hq]
    exact Int.ofNat_le_ofNat_of_le (Nat.zero_le _)
  rw [Int.pow_one, Int.ofNat_natAbs_of_nonneg ptinn]

theorem prime_power_to_nat_inc (pp : PrimePower) (hnmv : pp.x ≠ Int32.maxValue) :
  prime_power_to_nat (prime_power_inc pp hnmv) =
  prime_power_to_nat pp * pp.p.toInt := by
  have ptinn : 0 ≤ pp.p.toInt :=
    le_of_lt (Int32.lt_iff_toInt_lt.mp (prime_power_prime_pos pp))
  have xtinn : 0 ≤ pp.x.toInt :=
    le_of_lt (Int32.lt_iff_toInt_lt.mp pp.xpos)
  rw [← Int.ofNat_natAbs_of_nonneg ptinn]
  unfold prime_power_to_nat prime_power_inc; dsimp
  have xlt : pp.x < Int32.maxValue :=
    Int32.lt_of_le_of_ne (Int32.le_maxValue _) hnmv
  rw [← Int.pow_succ, int32_toInt_succ _ xlt]
  rw [Int.natAbs_add_of_nonneg xtinn zero_le_one]
  rfl

theorem prime_power_to_nat_gt_maxval {P : PrimePower} (h : P.x = Int32.maxValue) :
  2 ^ 31 < prime_power_to_nat P := by
  rcases P.prime with ⟨q, hprime, hq⟩
  have pge : 2 ≤ P.p := by
    apply Int32.le_iff_toInt_le.mpr
    simp only [Int32.reduceToInt]
    rw [hq]
    apply Int.ofNat_le_ofNat_of_le
    contrapose! hprime
    interval_cases q <;> norm_num
  have ptinn : 0 ≤ P.p.toInt := by
    rw [← Int32.toInt_zero]
    apply Int32.le_iff_toInt_le.mp
    exact Int32.le_trans (by decide) pge
  have pge' : 2 ≤ P.p.toInt.natAbs := by
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.ofNat_natAbs_of_nonneg ptinn]
    exact Int32.le_iff_toInt_le.mp pge
  have xnz : P.x.toInt.natAbs ≠ 0 := by
    rw [h]; decide
  apply Nat.lt_of_lt_of_le _ ((Nat.pow_le_pow_iff_left xnz).mpr pge')
  apply Nat.pow_lt_pow_of_lt (by decide)
  rw [h]; decide

-- Calculate the natural number corresponding to a factorization
def fac_to_nat (F : Factorization) : ℕ :=
  (Array.map prime_power_to_nat F.A).foldl (· * ·) 1

@[simp] theorem fac_to_nat_one : fac_to_nat fac_one = 1 := by
  unfold fac_to_nat fac_one
  rw [Array.map_empty, Array.foldl_empty]

theorem fac_to_nat_recurrence (F : Factorization) (hnil : F.A ≠ #[]) :
  fac_to_nat F = fac_to_nat (fac_pop F) * prime_power_to_nat (fac_back F hnil) := by
  unfold fac_to_nat
  have snez : F.A.size ≠ 0 := by
    contrapose! hnil
    exact Array.eq_empty_of_size_eq_zero hnil
  rcases Array.eq_push_of_size_ne_zero snez with ⟨B, pp, hB⟩
  rw [fac_pop_array, hB, Array.map_push, Array.foldl_push, Array.pop_push, fac_back_eq_back]
  rw [array_back_congr hB hnil, array_back_push]

theorem fac_to_nat_singleton {p : Int32}
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) :
  fac_to_nat (fac_singleton p hprime) = p.toInt := by
  have hnil : (fac_singleton p hprime).A ≠ #[] :=
    fun h ↦ fac_singleton_ne_one p hprime (fac_empty_iff.mpr h)
  rw [fac_to_nat_recurrence _ hnil, fac_pop_singleton, fac_to_nat_one, one_mul]
  rw [fac_back_singleton]
  exact prime_power_to_nat_singleton p hprime

theorem fac_to_nat_append (F : Factorization) (p : Int32)
  (hprime : ∃ q, Nat.Prime q ∧ p.toInt = q) (happ : fac_appendable F p)
  (hinc : (hnil : F.A ≠ #[]) → (fac_back F hnil).p ≤ p) :
  fac_to_nat (fac_append F p hprime happ hinc) = (fac_to_nat F) * p.toInt := by
  unfold fac_append
  by_cases hsz : F.A.size = 0
  · rw [dif_pos hsz]
    have hnil : F.A = #[] := Array.size_eq_zero_iff.mp hsz
    rw [fac_empty_iff.mpr hnil, fac_to_nat_one, Int.natCast_one, one_mul]
    rw [fac_to_nat_singleton]
  rename' hsz => hsnz; push_neg at hsnz
  rw [dif_neg hsnz]
  have hnil : F.A ≠ #[] :=
    fun h ↦ hsnz (Array.size_eq_zero_iff.mpr h)
  by_cases hp : p = (fac_back F hnil).p
  · rw [dif_pos hp, fac_to_nat_recurrence _ (by simp)]
    rw [fac_pop_push, fac_push_back, Int.natCast_mul]
    rw [prime_power_to_nat_inc _ (happ hnil hp), ← hp]
    rw [← mul_assoc, ← Int.natCast_mul]
    rw [← fac_to_nat_recurrence]
  rw [dif_neg hp, fac_to_nat_recurrence _ (by simp)]
  rw [fac_pop_push, fac_push_back, Int.natCast_mul]
  rw [prime_power_to_nat_singleton]

-- The natural number corresponding to a factorization is positive
theorem fac_to_nat_pos (F : Factorization) :
  0 < fac_to_nat F := by
  apply Nat.pos_of_ne_zero
  by_cases h : F.A = #[]
  · rw [fac_empty_iff.mpr h, fac_to_nat_one]
    decide
  rw [fac_to_nat_recurrence _ h]
  apply Nat.mul_ne_zero _ (Nat.ne_zero_of_lt (prime_power_to_nat_pos _))
  exact Nat.ne_zero_of_lt (fac_to_nat_pos _)
termination_by F.A.size
decreasing_by
  rw [fac_pop_array, Array.size_pop]
  apply Nat.sub_one_lt
  contrapose! h
  exact Array.size_eq_zero_iff.mp h

lemma fac_to_nat_gt_maxval {F : Factorization}
  (hmem : ∃ pp ∈ F.A, pp.x = Int32.maxValue) : 2 ^ 31 < fac_to_nat F := by
  rcases hmem with ⟨pp, pmem, hp⟩
  rcases Array.getElem_of_mem pmem with ⟨i, ilt, hi⟩
  have hnil : F.A ≠ #[] := by
    intro hnil; absurd ilt; push_neg
    rw [Array.size_eq_zero_iff.mpr hnil]
    exact Nat.zero_le _
  rw [fac_to_nat_recurrence _ hnil]
  by_cases hback : i = F.A.size - 1
  · subst hback
    apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_left _ (fac_to_nat_pos _))
    apply prime_power_to_nat_gt_maxval
    convert hp
  push_neg at hback
  apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ (prime_power_to_nat_pos _))
  apply fac_to_nat_gt_maxval
  use pp
  apply And.intro _ hp
  have ilt' : i < F.A.pop.size := by
    rw [Array.size_pop]
    exact lt_of_le_of_ne (Nat.le_sub_one_of_lt ilt) hback
  rw [← hi, fac_pop_array, ← Array.getElem_pop ilt']
  exact Array.getElem_mem _
termination_by F.A.size
decreasing_by
  rw [fac_pop_size]
  exact Nat.sub_one_lt (Nat.ne_zero_of_lt ilt)

structure FacBuilder (N : ℕ) where
  n : Int32
  F : Factorization
  npos : 0 < n
  Nle : N ≤ 2 ^ 31
  hN : n.toInt.natAbs * (fac_to_nat F) = N
  hdvdle : ∀ a, 1 < a → a.toInt ∣ n.toInt → (hnil : F.A ≠ #[]) →
    (F.A.back (Array.size_pos_iff.mpr hnil)).p ≤ a

-- This is required to show that the partial results in the
-- factorization algorithm are appendable
lemma fac_builder_exp_ne_maxVal_of_mem {N : ℕ} (FB : FacBuilder N) :
  ∀ pp ∈ FB.F.A, pp.x ≠ Int32.maxValue := by
  intro pp ppmem ppmv
  rcases Array.getElem_of_mem ppmem with ⟨i, ilt, hi⟩
  absurd FB.Nle; push_neg
  rw [← FB.hN]
  have npos : 0 < FB.n.toInt.natAbs := by
    apply Int.natAbs_pos.mpr
    apply (ne_of_lt _).symm
    exact Int32.lt_iff_toInt_lt.mp FB.npos
  apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_left _ npos)
  apply fac_to_nat_gt_maxval
  use pp

def fac_builder_init {N : ℕ}
  (n : Int32) (npos : 0 < n) (hn : n.toInt.natAbs = N) : FacBuilder N where
  n := n
  F := fac_one
  npos := npos
  Nle := hn ▸ (int32_natAbs_toInt_le _)
  hN := by rwa [fac_to_nat_one, mul_one]
  hdvdle := by
    intro _ _ _ hnil
    absurd hnil; simp

lemma fac_builder_ne1_of_not_term {N : ℕ} (FB : FacBuilder N)
  (hterm : ¬decide (FB.n.toInt.natAbs = 1) = true) : FB.n ≠ 1 := by
    contrapose! hterm
    rw [hterm]; decide

lemma fac_builder_natAbs_gt_of_not_term {N : ℕ} (FB : FacBuilder N)
  (hterm : ¬decide (FB.n.toInt.natAbs = 1) = true) :
  1 < FB.n.toInt.natAbs := by
  apply Int.lt_of_ofNat_lt_ofNat
  have ltn : 1 < FB.n.toInt := by
    have npos := Int32.lt_iff_toInt_lt.mp FB.npos
    rw [Int32.toInt_zero] at npos
    have len := (Int.zero_add _) ▸ (Int.add_one_le_of_lt npos)
    apply lt_of_le_of_ne len
    intro h1
    exact False.elim (fac_builder_ne1_of_not_term FB hterm (Int32.toInt_inj.mp h1.symm))
  convert ltn
  exact Int.ofNat_natAbs_of_nonneg (le_of_lt (lt_trans (by decide) ltn))

def fac_builder_advance {N : ℕ} (FB : FacBuilder N)
  (hterm : ¬decide (FB.n.toInt.natAbs = 1) = true) : FacBuilder N where
  n := FB.n / (smallest_divisor FB.n)
  F :=
    let n : Int32 := FB.n
    let d : Int32 := smallest_divisor n
    have ltn : 1 < n.toInt.natAbs := fac_builder_natAbs_gt_of_not_term _ hterm
    have ltd : 1 < d := smallest_divisor_gt _ ltn
    have ddvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
    fac_append FB.F d (smallest_divisor_prime _ ltn) (by
      intro hnil hd
      apply fac_builder_exp_ne_maxVal_of_mem FB
      rw [fac_back_eq_getElem]
      exact Array.getElem_mem _
    ) (fun hnil ↦ FB.hdvdle d ltd ddvd hnil)
  npos := by
    let n : Int32 := FB.n
    let d : Int32 := smallest_divisor n
    have ddvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
    have ltn : 1 < n.toInt.natAbs := fac_builder_natAbs_gt_of_not_term _ hterm
    have ltd : 1 < d := smallest_divisor_gt _ ltn
    have dtinn : 0 ≤ d.toInt :=
      le_of_lt (lt_of_lt_of_le (by decide) (Int32.lt_iff_toInt_lt.mp ltd))
    have dne1 : d ≠ -1 := by
      symm
      apply Int32.ne_of_lt
      exact Int32.lt_trans (by decide) ltd
    apply Int32.lt_iff_toInt_lt.mpr
    rw [Int32.toInt_div_of_ne_right n _ dne1, Int32.toInt_zero]
    exact Int.tdiv_pos_of_pos_of_dvd (Int32.lt_iff_toInt_lt.mp FB.npos) dtinn ddvd
  Nle := FB.Nle
  hN := by
    let n : Int32 := FB.n
    let d : Int32 := smallest_divisor n
    have ddvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
    have ltn : 1 < n.toInt.natAbs := fac_builder_natAbs_gt_of_not_term _ hterm
    have ltd : 1 < d := smallest_divisor_gt _ ltn
    have dtinn : 0 ≤ d.toInt :=
      le_of_lt (lt_of_lt_of_le (by decide) (Int32.lt_iff_toInt_lt.mp ltd))
    have dne1 : d ≠ -1 := by
      symm
      apply Int32.ne_of_lt
      exact Int32.lt_trans (by decide) ltd
    have divti : (FB.n / smallest_divisor FB.n).toInt = FB.n.toInt.tdiv d.toInt :=
      Int32.toInt_div_of_ne_right _ _ dne1
    have divnn : 0 ≤ (FB.n / smallest_divisor FB.n).toInt := by
      rw [divti]
      apply Int.le_of_lt (Int.tdiv_pos_of_pos_of_dvd _ dtinn ddvd)
      exact Int32.lt_iff_toInt_lt.mp FB.npos
    have ntinn : 0 ≤ n.toInt := Int32.le_iff_toInt_le.mp (Int32.le_of_lt FB.npos)
    apply Int.ofNat_inj.mp
    rw [Int.natCast_mul, fac_to_nat_append, mul_comm, mul_assoc, mul_comm]
    rw [Int.ofNat_natAbs_of_nonneg divnn, divti]
    change (d.toInt * _) * _ = _
    rw [Int.mul_tdiv_cancel_of_dvd ddvd]
    rw [← Int.ofNat_natAbs_of_nonneg ntinn, ← Int.natCast_mul]
    exact Int.natCast_inj.mpr FB.hN
  hdvdle := by
    dsimp
    intro a lta advd hnil
    let n : Int32 := FB.n
    let d : Int32 := smallest_divisor n
    have ddvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
    have ltn : 1 < n.toInt.natAbs := fac_builder_natAbs_gt_of_not_term _ hterm
    have ltd : 1 < d := smallest_divisor_gt _ ltn
    have dne1 : d ≠ -1 := by
      symm
      apply Int32.ne_of_lt
      exact Int32.lt_trans (by decide) ltd
    have divti : (FB.n / smallest_divisor FB.n).toInt = FB.n.toInt.tdiv d.toInt :=
      Int32.toInt_div_of_ne_right _ _ dne1
    rw [← fac_back_eq_back _ hnil, fac_append_back_power]
    apply smallest_divisor_le FB.n a lta (dvd_trans advd _)
    rw [divti]
    use d.toInt
    exact (Int.tdiv_mul_cancel_of_dvd ddvd).symm

instance {N : ℕ} : LoopBase (FacBuilder N) where
  term := fun FB ↦ FB.n.toInt.natAbs = 1
  adv := fac_builder_advance
  fdec := fun FB ↦ FB.n.toInt.natAbs
  hdec := by
    intro s h
    unfold fac_builder_advance; dsimp
    -- TODO: Um... maybe actually refactor this block of code rather
    -- than just copy it all over the place?
    let n : Int32 := s.n
    let d : Int32 := smallest_divisor n
    have ddvd : d.toInt ∣ n.toInt := smallest_divisor_dvd n
    have ltn : 1 < n.toInt.natAbs := fac_builder_natAbs_gt_of_not_term _ h
    have ltd : 1 < d := smallest_divisor_gt _ ltn
    have dne1 : d ≠ -1 := by
      symm
      apply Int32.ne_of_lt
      exact Int32.lt_trans (by decide) ltd
    have dtinn : 0 ≤ d.toInt :=
      le_of_lt (lt_of_lt_of_le (by decide) (Int32.lt_iff_toInt_lt.mp ltd))
    have divti : (s.n / smallest_divisor s.n).toInt = n.toInt.tdiv d.toInt :=
      Int32.toInt_div_of_ne_right _ _ dne1
    have divnn : 0 ≤ (s.n / smallest_divisor s.n).toInt := by
      rw [divti]
      apply Int.le_of_lt (Int.tdiv_pos_of_pos_of_dvd _ dtinn ddvd)
      exact Int32.lt_iff_toInt_lt.mp s.npos
    have ntinn : 0 ≤ n.toInt := Int32.le_iff_toInt_le.mp (Int32.le_of_lt s.npos)
    apply Int.natAbs_lt_natAbs_of_nonneg_of_lt divnn
    rw [divti, Int.tdiv_eq_ediv_of_nonneg ntinn]
    apply Int.ediv_lt_self_of_pos_of_ne_one (Int32.lt_iff_toInt_lt.mp s.npos)
    exact (Int.ne_of_lt (Int32.lt_iff_toInt_lt.mp ltd)).symm

def factor (n : Int32) (npos : 0 < n) : Factorization :=
  (do_loop (fac_builder_init n npos rfl)).F

end CodeChef
