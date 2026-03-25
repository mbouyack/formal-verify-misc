import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import FormalVerifyMisc.Int32.Basic
import FormalVerifyMisc.Int32.Abs
import FormalVerifyMisc.Iterator
import FormalVerifyMisc.Loops

namespace CodeChef

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

-- Prevent '2^31' from having to be written as '2 ^ 31'
set_option linter.style.commandStart false

def SIEVE_SIZE : ℕ := 1000001
def SIEVE_SIZE_32 : Int32 := 1000001

@[simp] theorem sieve_size_32_toInt : SIEVE_SIZE_32.toInt = SIEVE_SIZE := rfl

structure SieveParams where
  -- The length of the sieve
  L : Int32
  -- The sieve size must be at least 2
  hleL : 2 ≤ L
  -- The length of the sieve has an upper bound
  -- This is required to avoid exceeding Int32.maxValue
  hLlt : L < 2^30

-- Function to construct an iterator for the sieve
def sieve_iter_params (P : SieveParams) : IteratorInt32Params where
  start := 2
  finish := P.L
  inc := 1
  incpos := by decide
  hle := P.hleL
  hdvd := Int.one_dvd _

@[simp] theorem sieve_iter_start {P : SieveParams} :
  (sieve_iter_params P).start = 2 := rfl

@[simp] theorem sieve_iter_finish {P : SieveParams} :
  (sieve_iter_params P).finish = P.L := rfl

@[simp] theorem sieve_iter_inc {P : SieveParams} :
  (sieve_iter_params P).inc = 1 := rfl

structure Sieve (P : SieveParams) where
  -- The sieve - with non-zero values indicating divisors
  divs : Array Int32
  -- The list of primes found thus far
  primes : Array Int32
  -- An iterator, to allow the use of 'LoopIterator'
  iter : IteratorInt32 (sieve_iter_params P)
  -- The size of 'divs' is given by 'L'
  hsize : divs.size = P.L.toInt
  -- The entries in the sieve are non-negative
  hdivsnn : ∀ x ∈ divs, 0 ≤ x
  -- Each entry in the sieve is marked if-and-only-if its index
  -- is divisible by some prime in 'primes'
  hmarked : ∀ j, (0 < j) → (jlt : j < divs.size) →
    (∃ p ∈ primes, p.toInt ∣ (j : ℤ)) ↔ divs[j] ≠ 0
  -- The elements of 'primes' are non-negative
  -- Note that as-stated, 'hpmem_iff' (below) does not rule out this possibility
  hprimesnn : ∀ p ∈ primes, 0 ≤ p
  -- A natural number is in 'primes' if-and-only-if
  -- it is a prime less than 'i'
  hpmem_iff : ∀ p : ℕ,
    ((p : ℤ) ∈ (Array.map Int32.toInt primes) ↔
     (p : ℤ) < iter.val.toInt ∧ Nat.Prime p)
  -- If an entry in the sieve is non-zero, its value corresponds to the smallest
  -- divisor of its index greater than 1
  hdivs_dvd : ∀ j, (jlt : j < divs.size) → divs[j]'(jlt) ≠ 0 →
    (divs[j]'(jlt)).toInt ∣ j ∧
    ∀ y, 1 < y → y ∣ j → (divs[j]'(jlt)).toInt ≤ (y : ℤ)
  -- The number of elements in 'primes' is less than 'i'
  hprimessize : primes.size < iter.val.toInt
  -- The elements in 'primes' are strictly increasing
  hprimesinc : ∀ m n, (mlt : m < n) → (nlt : n < primes.size) →
    primes[m]'(lt_trans mlt nlt) < primes[n]

theorem sieve_index_toInt_pos {P : SieveParams} (S : Sieve P) : 0 < S.iter.val.toInt :=
  lt_of_lt_of_le (by simp) (Int32.le_iff_toInt_le.mp S.iter.hleval)

theorem sieve_index_pos {P : SieveParams} (S : Sieve P) : 0 < S.iter.val :=
  Int32.lt_iff_toInt_lt.mpr (sieve_index_toInt_pos S)

theorem sieve_length_pos {P : SieveParams} (S : Sieve P) : 0 < S.divs.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  rw [S.hsize]
  apply lt_of_lt_of_le (sieve_index_toInt_pos S)
  exact Int32.le_iff_toInt_le.mp S.iter.hvalle

-- Show equivalence for the two ways of expressing the upper bound on an index into S.divs
theorem lt_sieve_length_iff_of_nonneg
  {P : SieveParams} (S : Sieve P) (n : Int32) (hnnn : 0 ≤ n) :
  n.toInt.natAbs < S.divs.size ↔ n.toInt < P.L.toInt := by
  rw [← Int.ofNat_lt]
  rw [Int.ofNat_natAbs_of_nonneg (Int32.le_iff_toInt_le.mp hnnn), S.hsize]

theorem lt_sieve_length_of_lt_index
  {P : SieveParams} {S : Sieve P} {j : ℕ} (jlt : (j : ℤ) < S.iter.val.toInt) : j < S.divs.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  rw [S.hsize]
  apply lt_of_lt_of_le jlt (Int32.le_iff_toInt_le.mp S.iter.hvalle)

-- If an entry's index is divisible by some natural number less than S.i, the entry is marked
-- This is a more useable consequence of 'hmarked'
theorem sieve_marked_of_dvd_of_lt {P : SieveParams} (S : Sieve P) :
  ∀ (m n : ℕ), 0 < n → (nlt : n < S.divs.size) →
  m ≠ 1 → m ∣ n → m < S.iter.val.toInt → S.divs[n]'nlt ≠ 0 := by
  intro m n npos nlt mne1 mdvdn mlt
  apply (S.hmarked n npos nlt).mp
  rcases Nat.exists_prime_and_dvd mne1 with ⟨p, pprime, hp⟩
  have mpos := Nat.pos_of_dvd_of_pos mdvdn npos
  have plt := lt_of_le_of_lt (Int.ofNat_le_ofNat_of_le (Nat.le_of_dvd mpos hp)) mlt
  -- Get the Int32 that corresponds to 'p' in 'primes' (it must exist by 'hpmem_iff')
  rcases Array.exists_of_mem_map ((S.hpmem_iff p).mpr ⟨plt, pprime⟩) with ⟨p', p'mem, hp'p⟩
  use p', p'mem
  rw [hp'p]
  exact Int.ofNat_dvd.mpr (Nat.dvd_trans hp mdvdn)

-- Every entry properly between 1 and 'i' is marked
-- This is the result of combining 'hmarked' (every entry with a divisor in
-- 'primes' is marked) and 'hpmem_iff' (every prime less than S.i is in 'primes)
theorem sieve_marked_of_lt_index {P : SieveParams} (S : Sieve P) :
  ∀ (j : ℕ), (ltj : 1 < j) → (jlt : (j : ℤ) < S.iter.val.toInt) →
  S.divs[j]'(lt_sieve_length_of_lt_index jlt) ≠ 0 := by
  intro j ltj jlt
  have jlt' := lt_sieve_length_of_lt_index jlt
  -- Get some prime 'p' that divides 'j'
  rcases Nat.exists_prime_and_dvd (ne_of_lt ltj).symm with ⟨p, pprime, pdvd⟩
  have jpos : 0 < j := lt_trans (by simp) ltj
  apply (S.hmarked j jpos jlt').mp
  have ple := Nat.le_of_dvd jpos pdvd
  have plt : (p : ℤ) < S.iter.val.toInt :=
    lt_of_le_of_lt (Int.ofNat_le_ofNat_of_le ple) jlt
  -- Get the Int32 that corresponds to 'p' in 'primes' (it must exist by 'hpmem_iff')
  rcases Array.exists_of_mem_map ((S.hpmem_iff p).mpr ⟨plt, pprime⟩) with ⟨p', p'mem, hp'p⟩
  apply Int.ofNat_dvd.mpr at pdvd
  use p', p'mem
  rwa [hp'p]

def InitSieveParams : SieveParams where
  L := SIEVE_SIZE_32
  hleL := by decide
  hLlt := by decide

@[simp] theorem init_sieve_params_size : InitSieveParams.L = SIEVE_SIZE_32 := rfl

-- Construct a sieve with all elements set to zero
def init_sieve : Sieve InitSieveParams where
  divs := Array.replicate SIEVE_SIZE_32.toInt.toNat 0
  primes := #[]
  iter := iterator_int32_begin _
  hsize := by
    rw [Array.size_replicate]; decide
  hdivsnn := by
    intro x xmem
    rw [(Array.mem_replicate.mp xmem).2]; rfl
  hmarked := by simp
  hprimesnn := fun p pmem ↦ False.elim (Array.not_mem_empty _ pmem)
  hpmem_iff := by
    intro p;
    simp only [List.map_toArray, List.map_nil, List.mem_toArray, List.not_mem_nil,
      iterator_int32_begin_val, sieve_iter_start, Int32.reduceToInt, Nat.cast_lt_ofNat, false_iff,
      not_and];
    intro plt
    interval_cases p <;> norm_num
  hdivs_dvd := by
    intro j jlt hnz
    constructor
    · absurd hnz; simp
    · intro y lty ydvd; simp
  hprimessize := by simp
  hprimesinc := by simp

structure MarkMultiplesStateParams where
  L : Int32
  inc : Int32
  incpos : 0 < inc
  incle : inc ≤ L
  hLlt : L < 2^30

def mms_params_of_sieve {P : SieveParams} (S : Sieve P) : MarkMultiplesStateParams where
  L := P.L
  inc := S.iter.val
  incpos := by
    apply Int32.lt_of_lt_of_le _ S.iter.hleval
    rw [sieve_iter_start]; decide
  incle := S.iter.hvalle
  hLlt := P.hLlt

@[simp] theorem mms_params_of_sieve_L {P : SieveParams} (S : Sieve P) :
  (mms_params_of_sieve S).L = P.L := rfl

@[simp] theorem mms_params_of_sieve_inc {P : SieveParams} (S : Sieve P) :
  (mms_params_of_sieve S).inc = S.iter.val := rfl

lemma mms_params_toInt_inc_pos (P : MarkMultiplesStateParams) :
  0 < P.inc.toInt := Int32.lt_iff_toInt_lt.mp P.incpos

lemma mms_params_toInt_L_nonneg (P : MarkMultiplesStateParams) :
  0 ≤ P.L.toInt := by
  apply le_trans (le_of_lt (mms_params_toInt_inc_pos P))
  exact Int32.le_iff_toInt_le.mp P.incle

-- TODO: There has got to be a better approach to this than
-- reproving the same identity over and over
lemma mms_params_toInt_L_add_inc (P : MarkMultiplesStateParams) :
  (P.L + P.inc).toInt = P.L.toInt + P.inc.toInt := by
  rw [int32_toInt_add_of_bounds]
  constructor
  · exact le_trans (by decide) (Int.add_le_add
      (mms_params_toInt_L_nonneg P)
      (le_of_lt (mms_params_toInt_inc_pos P)))
  · have inclt : P.inc.toInt < 2^30 :=
      Int32.lt_iff_toInt_lt.mp (Int32.lt_of_le_of_lt P.incle P.hLlt)
    have Llt : P.L.toInt < 2^30 := Int32.lt_iff_toInt_lt.mp P.hLlt
    exact Int.add_lt_add Llt inclt

def mms_iter_finish (P : MarkMultiplesStateParams) : Int32 :=
  if P.L % P.inc = 0 then P.L else P.L + P.inc - (P.L % P.inc)

-- Prove the result of converting the 'finish' value of the MMS iterator
-- to an integer.
theorem mms_iter_finish_toInt (P : MarkMultiplesStateParams) :
  (mms_iter_finish P).toInt = P.L.toInt + (-P.L.toInt % P.inc.toInt) := by
  unfold mms_iter_finish
  have incpos' : 0 < P.inc.toInt :=
    Int32.lt_iff_toInt_lt.mp P.incpos
  have Lnn := mms_params_toInt_L_nonneg P
  have hdvd_iff : P.L % P.inc = 0 ↔ P.inc.toInt ∣ P.L.toInt := by
    rw [← Int32.toInt_inj, Int32.toInt_mod, Int32.toInt_zero]
    exact Int.dvd_iff_tmod_eq_zero.symm
  split_ifs with h <;> rw [hdvd_iff] at h
  · rw [Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr h)]
    exact (Int.sub_zero _).symm
  · have modnn : 0 ≤ P.L % P.inc := by
      apply Int32.le_iff_toInt_le.mpr
      rw [Int32.toInt_mod]
      exact Int.tmod_nonneg _ Lnn
    have modle : P.L % P.inc ≤ P.L + P.inc := by
      apply Int32.le_iff_toInt_le.mpr (le_of_lt _)
      rw [mms_params_toInt_L_add_inc]
      rw [Int32.toInt_mod]
      apply lt_of_lt_of_le (Int.tmod_lt_of_pos _ incpos')
      rw [add_comm]
      exact Int.le_add_of_nonneg_right Lnn
    rw [Int32.toInt_sub_of_le (P.L + P.inc) (P.L % P.inc) modnn modle]
    rw [mms_params_toInt_L_add_inc, Int32.toInt_mod]
    rw [Int.tmod_eq_emod, if_pos (Or.inl Lnn)]
    rw [Int.ofNat_zero, sub_zero]
    rw [Int.neg_emod, if_neg h, Int.ofNat_natAbs_of_nonneg (le_of_lt incpos')]
    rw [add_sub_assoc]

-- Function to construct iterator params for 'mark multiples'
def mms_iter_params (P : MarkMultiplesStateParams) : IteratorInt32Params where
  start := P.inc
  -- 'finish' is L rounded up to the next multiple of P.inc
  finish := mms_iter_finish P
  inc := P.inc
  incpos := P.incpos
  hle := by
    apply Int32.le_iff_toInt_le.mpr
    rw [mms_iter_finish_toInt]
    apply le_trans (Int32.le_iff_toInt_le.mp P.incle)
    apply Int.le_add_of_nonneg_right
    exact Int.emod_nonneg _ (ne_of_lt (mms_params_toInt_inc_pos P)).symm
  hdvd := by
    rw [mms_iter_finish_toInt, ← Int.dvd_neg]
    rw [Int.neg_sub, ← sub_sub, sub_eq_add_neg P.inc.toInt]
    rw [add_sub_assoc]
    apply Int.dvd_add (Int.dvd_refl _)
    exact Int.dvd_self_sub_emod

@[simp] theorem mms_iter_params_start (P : MarkMultiplesStateParams) :
  (mms_iter_params P).start = P.inc := rfl

@[simp] theorem mms_iter_params_finish (P : MarkMultiplesStateParams) :
  (mms_iter_params P).finish = mms_iter_finish P := rfl

@[simp] theorem mms_iter_params_inc (P : MarkMultiplesStateParams) :
  (mms_iter_params P).inc = P.inc := rfl

-- The state and constraints required for the 'mark_multiples' loop
@[ext] structure MarkMultiplesState (P : MarkMultiplesStateParams) where
  A : Array Int32
  iter : IteratorInt32 (mms_iter_params P)
  hsize : A.size = P.L.toInt

theorem mark_multiples_state_size_pos
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P) :
  0 < MMS.A.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  rw [MMS.hsize]
  exact Int32.lt_iff_toInt_lt.mp (Int32.lt_of_lt_of_le P.incpos P.incle)

-- Construct a 'MarkMultiplesState' given the array and parameters
def mark_multiples_state_of_sieve
  (P : MarkMultiplesStateParams) (A : Array Int32)
  (hsize : A.size = P.L.toInt) : MarkMultiplesState P where
  A := A
  iter := iterator_int32_begin _
  hsize := hsize

@[simp] theorem mark_multiples_state_of_sieve_cur {P : SieveParams} (S : Sieve P) :
  (mark_multiples_state_of_sieve (mms_params_of_sieve S)
    S.divs S.hsize).iter.val = S.iter.val := rfl

@[simp] theorem mark_multiples_state_of_sieve_array {P : SieveParams} (S : Sieve P) :
  (mark_multiples_state_of_sieve (mms_params_of_sieve S)
    S.divs S.hsize).A = S.divs := rfl

theorem sieve_iter_val_dvd_mms_iter_val {P : SieveParams} {S : Sieve P}
  (mms : MarkMultiplesState (mms_params_of_sieve S)) :
  S.iter.val.toInt ∣ mms.iter.val.toInt := by
  have := mms.iter.hdvd
  simp only [mms_iter_params_inc, mms_params_of_sieve_inc, mms_iter_params_start] at this
  rw [Int.dvd_iff_dvd_of_dvd_sub this]

theorem mms_iter_val_toInt_pos
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P) :
  0 < MMS.iter.val.toInt := by
  apply Int32.lt_iff_toInt_lt.mp (Int32.lt_of_lt_of_le P.incpos _)
  exact MMS.iter.hleval

theorem mms_iter_val_toInt_nonneg
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P) :
  0 ≤ MMS.iter.val.toInt := le_of_lt (mms_iter_val_toInt_pos MMS)

-- Prove that in MarkMultiplesState, we can use the iterator to access the array
lemma mms_iter_val_toInt_natAbs_lt
  {P : MarkMultiplesStateParams} {MMS : MarkMultiplesState P}
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  MMS.iter.val.toInt.natAbs < MMS.A.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  have hnef : MMS.iter.val ≠ (mms_iter_params P).finish := by
    rwa [IteratorInt32.ext_iff, iterator_int32_end_val] at hnend
  rw [Int.ofNat_natAbs_of_nonneg (mms_iter_val_toInt_nonneg MMS), MMS.hsize]
  have := iterator_int32_val_add_inc_le_finish hnef
  apply lt_of_le_of_lt (Int.le_sub_right_of_add_le this)
  rw [mms_iter_params_finish, mms_iter_finish_toInt, mms_iter_params_inc]
  apply Int.sub_right_lt_of_lt_add (Int.add_lt_add_left _ _)
  exact Int.emod_lt_of_pos _ (Int32.lt_iff_toInt_lt.mp P.incpos)

-- Advance the loop marking multiples of MMS.inc in MMS.A
def mark_multiples_advance
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) : MarkMultiplesState P :=
  have hlt := mms_iter_val_toInt_natAbs_lt hnend
  {
    A :=
      if MMS.A[MMS.iter.val.toInt.natAbs] ≠ 0 then MMS.A
      else MMS.A.set MMS.iter.val.toInt.natAbs P.inc
    iter := iterator_int32_next MMS.iter
    hsize := by
      split_ifs with h
      · exact MMS.hsize
      · rw [Array.size_set hlt]
        exact MMS.hsize
  }

instance {P : MarkMultiplesStateParams} :
  LoopIterator (MarkMultiplesState P) (IteratorInt32 (mms_iter_params P)) where
  iter := MarkMultiplesState.iter
  adv := mark_multiples_advance
  hadv := fun _ _ ↦ rfl

-- The size of the MarkMultiplesState doesn't change upon advancing
@[simp] theorem mark_multiples_advance_size
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  (mark_multiples_advance MMS hnend).A.size = MMS.A.size := by
  unfold mark_multiples_advance; dsimp
  split_ifs with h <;> simp

@[simp] theorem mark_multiples_advance_iter
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  (mark_multiples_advance MMS hnend).iter = iterator_int32_next MMS.iter := rfl

@[simp] theorem loop_iterator_iter_of_mms_params {P : MarkMultiplesStateParams}
  (mms : MarkMultiplesState P) :
  (LoopIterator.iter mms) = mms.iter := rfl

@[simp] theorem loop_iterator_adv_of_mms_params {P : MarkMultiplesStateParams}
  (mms : MarkMultiplesState P) (hnend : ¬mms.iter = iterator_int32_end _) :
  (LoopIterator.adv mms hnend) = mark_multiples_advance mms hnend := rfl

-- Advancing the 'mark_multiples' loop has no effect
-- on entries which have already been marked.
theorem mark_multiples_advance_unchanged_of_marked
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → MMS.A[j] ≠ 0 →
  (mark_multiples_advance MMS hnend).A[j]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.A[j] := by
  intro j jpos jlt hAjnz
  unfold mark_multiples_advance; dsimp
  split_ifs with h
  · apply Array.getElem_set_ne
    contrapose! hAjnz
    subst hAjnz; assumption
  · rfl

-- Advancing the 'mark_multiples' loop has no effect
-- on entries whose indices are not divisible by 'inc'
theorem mark_multiples_advance_unchanged_of_not_dvd
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → ¬P.inc.toInt ∣ (j : ℤ) →
  (mark_multiples_advance MMS hnend).A[j]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.A[j] := by
  intro j jpos jlt jndvd
  unfold mark_multiples_advance; dsimp
  split_ifs with h
  · apply Array.getElem_set_ne
    contrapose! jndvd
    rw [← jndvd, Int.ofNat_natAbs_of_nonneg (mms_iter_val_toInt_nonneg MMS)]
    have := MMS.iter.hdvd
    rw [mms_iter_params_inc, mms_iter_params_start] at this
    exact (Int.dvd_iff_dvd_of_dvd_sub this).mpr (Int.dvd_refl _)
  · rfl

-- Advancing the 'mark_multiples' loop has no effect
-- on entries other than 'cur'
theorem mark_multiples_advance_unchanged_of_not_cur
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → MMS.iter.val.toInt ≠ j →
  (mark_multiples_advance MMS hnend).A[j]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.A[j] := by
  intro j jpos jlt curnej
  unfold mark_multiples_advance; dsimp
  split_ifs with h
  · apply Array.getElem_set_ne
    contrapose! curnej
    rw [← curnej]; symm
    exact Int.ofNat_natAbs_of_nonneg (mms_iter_val_toInt_nonneg MMS)
  · rfl

-- The first entry in the array is never modifed
theorem mark_multiples_advance_unchanged_of_first
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  (mark_multiples_advance MMS hnend).A[0]'(by
    rw [mark_multiples_advance_size]
    exact mark_multiples_state_size_pos MMS
  ) = MMS.A[0]'(mark_multiples_state_size_pos MMS) := by
    unfold mark_multiples_advance; dsimp
    split_ifs with h
    · apply Array.getElem_set_ne
      exact Int.natAbs_ne_zero.mpr (ne_of_lt (mms_iter_val_toInt_pos MMS)).symm
    · rfl

-- If the current entry was previously zero, 'mark_multiples_advance' will set it to MMS.inc
theorem mark_multiples_advance_changed
  {P : MarkMultiplesStateParams} (MMS : MarkMultiplesState P)
  (hnend : ¬MMS.iter = iterator_int32_end _) :
  MMS.A[MMS.iter.val.toInt.natAbs]'(mms_iter_val_toInt_natAbs_lt hnend) = 0 →
  (mark_multiples_advance MMS hnend).A[MMS.iter.val.toInt.natAbs]'(by
    rw [mark_multiples_advance_size]
    exact mms_iter_val_toInt_natAbs_lt hnend
  ) = P.inc := by
  intro hz
  unfold mark_multiples_advance
  simp only [ne_eq, ite_not]
  rw [getElem_congr_coll (if_pos hz)]
  apply Array.getElem_set_self

/- Mark every entry of 'A' which is a multiple of P.inc

   Originally this function took a Sieve as an argument, but because it isn't
   given exclusive ownership of that Sieve, the entire array was being copied.
   Passing the raw array substantially improves the performance of the algorithm
   at the cost of slightly more verbose code.
-/
def mark_multiples (P : MarkMultiplesStateParams) (A : Array Int32)
  (hsize : A.size = P.L.toInt)  : MarkMultiplesState P :=
  do_loop (mark_multiples_state_of_sieve P A hsize)

-- The size of the marked array is the same as the size of the sieve
@[simp] theorem mark_multiples_size {P : SieveParams} (S : Sieve P) :
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A.size = S.divs.size := by
  unfold mark_multiples
  apply Int.ofNat_inj.mp
  rw [MarkMultiplesState.hsize, mms_params_of_sieve_L, S.hsize]

-- 'mark_multiples' has no effect on entries in the sieve
-- that were previous marked
theorem mark_multiples_unchanged_of_marked {P : SieveParams} (S : Sieve P) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.divs[j] ≠ 0 →
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A[j]'(by
    rwa [mark_multiples_size]) = S.divs[j] := by
  unfold mark_multiples
  intro j jpos jlt hnz
  let P := mms_params_of_sieve S
  let mms₀ := mark_multiples_state_of_sieve P S.divs S.hsize
  let prop (mms : MarkMultiplesState P) : Prop :=
    (_ : j < mms.A.size) → mms.A[j] ≠ 0 ∧ mms.A[j] = S.divs[j]
  have base : prop mms₀ := by
    unfold prop mms₀ P
    intro; simpa
  have step : ∀ t hterm,
    prop t → prop (LoopBase.adv t hterm) := by
    unfold prop
    intro t hterm h jlt'
    -- TODO: Is this really the best way of replacing invocations
    -- of the parent class with the specific implementation of the
    -- child class?
    simp only [loop_base_term_of_loop_iterator, loop_iterator_iter_of_mms_params] at hterm
    simp only [decide_eq_true_eq] at hterm
    simp only [loop_base_adv_of_loop_iterator, loop_iterator_adv_of_mms_params]
    simp only [loop_base_adv_of_loop_iterator, loop_iterator_adv_of_mms_params] at jlt'
    simp only [mark_multiples_advance_size] at jlt'
    obtain ⟨hnz', h⟩ := h jlt'
    rw [mark_multiples_advance_unchanged_of_marked t hterm j jpos jlt' hnz']
    exact ⟨hnz', h⟩
  exact (loop_prop_const mms₀ prop base step _).2

-- 'mark_multiples' has no effect on entries in the sieve
-- whose indices are not divisible by 'inc'
theorem mark_multiples_unchanged_of_not_dvd {P : SieveParams} (S : Sieve P) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → ¬S.iter.val.toInt ∣ (j : ℤ) →
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A[j]'(by
    rwa [mark_multiples_size]) = S.divs[j] := by
  intro j jpos jlt hdvd
  let P := mms_params_of_sieve S
  let mms₀ := mark_multiples_state_of_sieve P S.divs S.hsize
  let prop (mms : MarkMultiplesState P) : Prop :=
    (_ : j < mms.A.size) → ¬P.inc.toInt ∣ j ∧ mms.A[j] = S.divs[j]
  have base : prop mms₀ := by
    unfold prop mms₀ P
    intro; simpa
  have step : ∀ t hterm,
    prop t → prop (LoopBase.adv t hterm) := by
    unfold prop P
    intro t hterm h jlt
    have jlt' : j < t.A.size := by
      convert jlt using 1; simp
    convert h jlt' using 2
    simp only [loop_base_adv_of_loop_iterator, loop_iterator_adv_of_mms_params]
    apply mark_multiples_advance_unchanged_of_not_dvd <;> simpa
  exact (loop_prop_const mms₀ prop base step _).2

-- 'mark_multiples' has no effect on the first entry in the sieve
theorem mark_multiples_unchanged_of_first {P : SieveParams} (S : Sieve P) :
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A[0]'(
    (mark_multiples_size S) ▸ (sieve_length_pos S)
  ) = S.divs[0]'(sieve_length_pos S) := by
  let P := mms_params_of_sieve S
  let mms₀ := mark_multiples_state_of_sieve P S.divs S.hsize
  let prop (mms : MarkMultiplesState P) : Prop :=
    mms.A[0]'(mark_multiples_state_size_pos mms) = S.divs[0]'(sieve_length_pos S)
  have base : prop mms₀ := by
    unfold prop mms₀ P; simp
  have step : ∀ t hterm,
    prop t → prop (LoopBase.adv t hterm) := by
    unfold prop P
    intro t hterm h
    simp only [loop_base_adv_of_loop_iterator, loop_iterator_adv_of_mms_params]
    rwa [mark_multiples_advance_unchanged_of_first]
  exact loop_prop_const mms₀ prop base step

-- Any entry that was zero and has index divisible by 'inc' will be
-- set to 'inc' by mark_multiples
theorem mark_multiples_changed {P : SieveParams} (S : Sieve P) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) →
  S.divs[j] = 0 → S.iter.val.toInt ∣ (j : ℤ) →
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A[j]'(by
    rwa [mark_multiples_size]) = S.iter.val := by
  intro j jpos _ hz hdvd
  let P' := mms_params_of_sieve S
  let mms₀ := mark_multiples_state_of_sieve P' S.divs S.hsize
  let prop (mms : MarkMultiplesState P') : Prop :=
    (_ : j < mms.A.size) →
    (mms.iter.val.toInt ≤ j → mms.A[j] = 0) ∧
    (j < mms.iter.val.toInt → mms.A[j] = P'.inc)
  have base : prop mms₀ := by
    unfold prop mms₀ P';
    intro _
    simp only [mark_multiples_state_of_sieve_array]
    simp only [mark_multiples_state_of_sieve_cur, mms_params_of_sieve_inc]
    apply And.intro (fun _ ↦ hz)
    intro jlt
    have lej := Int.le_of_dvd (Int.ofNat_lt_ofNat_of_lt jpos) hdvd
    exact False.elim (Int.not_lt_of_ge lej jlt)
  have step : ∀ t hterm,
    prop t → prop (LoopBase.adv t hterm) := by
    unfold prop
    simp only [loop_base_term_of_loop_iterator, loop_iterator_iter_of_mms_params]
    simp only [decide_eq_true_eq, loop_base_adv_of_loop_iterator]
    simp only [loop_iterator_adv_of_mms_params, mark_multiples_advance_size]
    simp only [mark_multiples_advance_iter, iterator_end_of_iterator_int32]
    intro t hterm h jlt
    rw [iterator_int32_next_val_toInt _ hterm]
    rw [mms_iter_params_inc]
    constructor
    · intro hlej
      have ltj : t.iter.val.toInt < j := by
        apply lt_of_lt_of_le _ hlej
        exact Int.lt_add_of_pos_right _ (mms_params_toInt_inc_pos P')
      rw [mark_multiples_advance_unchanged_of_not_cur t hterm j jpos jlt (ne_of_lt ltj)]
      exact (h jlt).1 (le_of_lt ltj)
    · unfold P'
      simp only [mms_params_of_sieve_inc]
      intro jlt'
      by_cases valj : t.iter.val.toInt = j
      · have hnn := mms_iter_val_toInt_nonneg t
        have valj' :=
          Int.ofNat_inj.mp (Eq.trans (Int.ofNat_natAbs_of_nonneg hnn) valj)
        subst valj'
        apply mark_multiples_advance_changed
        exact (h jlt).1 (le_of_eq valj)
      rename' valj => valnej; push_neg at valnej
      rw [mark_multiples_advance_unchanged_of_not_cur t hterm j jpos jlt valnej]
      apply (h jlt).2 (lt_of_le_of_ne _ valnej.symm)
      -- The theorem we want here is Nat.le_of_lt_add_of_dvd but for integers.
      -- Unfortunately it doesn't seem to exist!
      rcases sieve_iter_val_dvd_mms_iter_val t with ⟨k₀, hk₀⟩
      rcases hdvd with ⟨k₁, hk₁⟩
      rw [hk₀, hk₁]
      rw [hk₀, hk₁] at jlt'
      nth_rw 3 [← Int.mul_one S.iter.val.toInt] at jlt'
      rw [← mul_add, Int.mul_lt_mul_left (sieve_index_toInt_pos S)] at jlt'
      rw [Int.mul_le_mul_left (sieve_index_toInt_pos S)]
      exact Int.le_of_lt_add_one jlt'
  have := loop_prop_const mms₀ prop base step
  unfold mark_multiples
  have jlt : j < (do_loop mms₀).A.size := by
    unfold mms₀ P'
    apply Int.lt_of_ofNat_lt_ofNat
    rw [MarkMultiplesState.hsize, mms_params_of_sieve_L, ← S.hsize]
    apply Int.ofNat_lt_ofNat_of_lt
    assumption
  have jlt' : ↑j < (do_loop mms₀).iter.val.toInt := by
    apply lt_of_lt_of_le (Int.ofNat_lt_ofNat_of_lt jlt)
    rw [MarkMultiplesState.hsize]
    have hterm := loop_term mms₀
    simp only [loop_base_term_of_loop_iterator, loop_iterator_iter_of_mms_params,
      iterator_end_of_iterator_int32, decide_eq_true_eq] at hterm
    rw [IteratorInt32.ext_iff] at hterm
    rw [hterm]
    simp only [iterator_int32_end_val, mms_iter_params_finish]
    rw [mms_iter_finish_toInt]
    apply Int.le_add_of_nonneg_right
    exact Int.emod_nonneg _ (ne_of_lt (mms_params_toInt_inc_pos P')).symm
  convert (this jlt).2 jlt'

-- Any entry whose index is divisible by 'inc' will be marked
-- after calling mark_multiples
theorem mark_multiples_marked_of_dvd {P : SieveParams} (S : Sieve P) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.iter.val.toInt ∣ (j : ℤ) →
  (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A[j]'(by
    rwa [mark_multiples_size]) ≠ 0 := by
  intro j jpos jlt idvd
  by_cases h : S.divs[j]'jlt = 0
  · rw [mark_multiples_changed S j jpos jlt h idvd]; symm
    exact Int32.ne_of_lt (Int32.lt_iff_toInt_lt.mpr (sieve_index_toInt_pos S))
  push_neg at h
  rwa [mark_multiples_unchanged_of_marked S j jpos jlt h]

lemma sieve_iter_val_nonneg {P : SieveParams} (S : Sieve P) : 0 ≤ S.iter.val := by
  apply Int32.le_trans _ S.iter.hleval; simp

-- This allows access to elements of the sieve given that iter ≠ end
lemma sieve_iter_val_lt {P : SieveParams} (S : Sieve P)
  (h : ¬S.iter = iterator_int32_end _) :
  S.iter.val.toInt.natAbs < S.divs.size := by
  rw [lt_sieve_length_iff_of_nonneg S _ (sieve_iter_val_nonneg S)]
  apply lt_of_le_of_ne (Int32.le_iff_toInt_le.mp S.iter.hvalle)
  contrapose! h
  rw [← iterator_int32_val_eq_finish_iff]
  exact Int32.toInt_inj.mp h

-- Advance the loop which fills out the sieve, in the case where S.divs[i] = 0
def advance_sieve_of_entry_eq_zero {P : SieveParams} (S : Sieve P)
  (hnend : ¬S.iter = iterator_int32_end _)
  (hiz : S.divs[S.iter.val.toInt.natAbs]'(sieve_iter_val_lt S hnend) = 0) : Sieve P where
  divs := (mark_multiples (mms_params_of_sieve S) S.divs S.hsize).A
  primes := S.primes.push S.iter.val
  iter := iterator_int32_next S.iter
  hsize := by
    rw [mark_multiples_size]
    exact S.hsize
  hdivsnn := by
    intro x xmem
    rcases Array.getElem_of_mem xmem with ⟨j, jlt, hjx⟩
    have jlt' : j < S.divs.size := by
      simp at jlt; assumption
    have hSjnn : 0 ≤ S.divs[j]'(by simp at jlt; assumption) :=
      S.hdivsnn _ (Array.getElem_mem _)
    rw [← hjx]
    by_cases hjz : j = 0
    · subst hjz
      rwa [mark_multiples_unchanged_of_first]
    rename' hjz => hjnz; push_neg at hjnz
    have jpos : 0 < j := Nat.pos_of_ne_zero hjnz
    by_cases hmarked : S.divs[j]'jlt' ≠ 0
    · rw [mark_multiples_unchanged_of_marked] <;> try assumption
    rename' hmarked => hnmarked; push_neg at hnmarked
    by_cases hndvd : ¬S.iter.val.toInt ∣ j
    · rw [mark_multiples_unchanged_of_not_dvd] <;> try assumption
    rename' hndvd => hdvd; push_neg at hdvd
    have hSinn : 0 ≤ S.iter.val := by
      apply Int32.le_iff_toInt_le.mpr
      exact le_of_lt (sieve_index_toInt_pos S)
    rw [mark_multiples_changed] <;> assumption
  hmarked := by
    intro j jpos jlt
    simp only [mark_multiples_size] at jlt
    constructor
    · intro h
      rcases h with ⟨p, pmem, hp⟩
      rcases Array.mem_push.mp pmem with lhs | rhs
      · have hSjz : S.divs[j] ≠ 0 :=
          (S.hmarked j jpos jlt).mp ⟨p, lhs, hp⟩
        rw [mark_multiples_unchanged_of_marked] <;> assumption
      · rw [rhs] at hp
        apply mark_multiples_marked_of_dvd <;> assumption
    · intro h
      by_cases h' : S.divs[j]'jlt ≠ 0
      · rcases (S.hmarked j jpos jlt).mpr h' with ⟨p, pmem, hp⟩; use p
        exact ⟨Array.mem_push_of_mem _ pmem, hp⟩
      push_neg at h'
      have hdvd : S.iter.val.toInt ∣ (j : ℤ) := by
        contrapose! h
        rwa [mark_multiples_unchanged_of_not_dvd] <;> assumption
      exact ⟨S.iter.val, Array.mem_push_self, hdvd⟩
  hprimesnn := by
    intro p pmem
    rcases Array.mem_or_eq_of_mem_push pmem with lhs | rfl
    · exact S.hprimesnn p lhs
    · exact Int32.le_of_lt (sieve_index_pos S)
  hpmem_iff := by
    intro p
    rw [iterator_int32_next_val_toInt _ hnend]
    constructor
    · intro pmem
      rcases Array.exists_of_mem_map pmem with ⟨p', p'mem, hp'⟩
      rcases Array.mem_or_eq_of_mem_push p'mem with lhs | rfl
      · have := (S.hpmem_iff p).mp (hp' ▸ (@Array.mem_map_of_mem _ _ _ _ Int32.toInt lhs))
        exact ⟨Int.lt_add_one_iff.mpr (le_of_lt this.1), this.2⟩
      · rw [← hp']
        use Int.lt_add_of_pos_right _ one_pos
        -- To prove 'p' is prime we need to show that any divisor 'm' is either 1 or p
        apply Nat.prime_def.mpr
        have pge2 : 2 ≤ p := by
          apply Int.le_of_ofNat_le_ofNat
          exact hp' ▸ (Int32.le_iff_toInt_le.mp S.iter.hleval)
        use pge2
        intro m mdvdp
        have ppos : 0 < p := lt_of_lt_of_le two_pos pge2
        have mlep : m ≤ p :=
          Nat.le_of_dvd ppos mdvdp
        have mpos := Nat.pos_of_dvd_of_pos mdvdp ppos
        -- Proof by contradiction: assume p is *not* prime
        -- and show that S.divs[i] must have already been marked
        contrapose! hiz
        rcases hiz with ⟨mne1, mnep⟩
        -- Show 1 < m < p
        have ltm := lt_of_le_of_ne (Nat.one_le_of_lt mpos) mne1.symm
        have mlt := lt_of_le_of_ne mlep mnep
        -- Because m ∣ S.i and m < S.i, S.divs[S.i] is marked
        rw [getElem_congr_idx (congrArg Int.natAbs hp')];
        simp only [Int.natAbs_natCast, ne_eq]
        apply sieve_marked_of_dvd_of_lt S m <;> try assumption
        rw [hp']
        exact Int.ofNat_lt_ofNat_of_lt mlt
    · intro ⟨ple, pprime⟩
      apply Int.le_of_lt_add_one at ple
      by_cases hpi : (p : ℤ) = S.iter.val.toInt
      · rw [hpi]
        exact Array.mem_map_of_mem Array.mem_push_self
      rename' hpi => pnei; push_neg at pnei
      have plt := lt_of_le_of_ne ple pnei
      have pmem := (S.hpmem_iff p).mpr ⟨(lt_of_le_of_ne ple pnei), pprime⟩
      rcases Array.exists_of_mem_map pmem with ⟨p', p'mem, hp'⟩
      rw [← hp']
      exact Array.mem_map_of_mem (Array.mem_push_of_mem _ p'mem)
  hdivs_dvd := by
    intro j jlt hAjz
    simp only [mark_multiples_size] at jlt
    -- Handle the case where j = 0
    by_cases j0 : j = 0
    · subst j0
      rw [mark_multiples_unchanged_of_first] at *
      exact S.hdivs_dvd 0 jlt hAjz
    rename' j0 => jnz; push_neg at jnz
    have jpos : 0 < j := Nat.pos_of_ne_zero jnz
    -- Handle the case where entry j was already marked
    by_cases hmarked : S.divs[j]'jlt ≠ 0
    · rw [mark_multiples_unchanged_of_marked] <;> try assumption
      exact S.hdivs_dvd j jlt hmarked
    push_neg at hmarked
    by_cases hdvd : ¬S.iter.val.toInt ∣ j
    · rw [mark_multiples_unchanged_of_not_dvd] at * <;> try assumption
      exact S.hdivs_dvd j jlt hAjz
    push_neg at hdvd
    rw [mark_multiples_changed] <;> try assumption
    use hdvd
    intro y lty ydvd
    -- Proof by contradiction:
    -- if y < i, we would have already marked entry j
    contrapose! hmarked
    rename' hmarked => ylt
    apply sieve_marked_of_dvd_of_lt S y j <;> try assumption
    exact (ne_of_lt lty).symm
  hprimessize := by
    rw [iterator_int32_next_val_toInt _ hnend]
    rw [sieve_iter_inc, Array.size_push]
    rw [← Int.ofNat_add_ofNat]
    exact Int.add_lt_add_right S.hprimessize 1
  hprimesinc := by
    intro m n mlt nlt
    rw [Array.size_push] at nlt
    have mlt' := lt_of_lt_of_le mlt (Nat.le_of_lt_add_one nlt)
    rw [Array.getElem_push_lt mlt']
    by_cases nlt' : n < S.primes.size
    · rw [Array.getElem_push_lt nlt']
      exact S.hprimesinc _ _ mlt nlt'
    rename' nlt' => len; push_neg at len
    have hns := le_antisymm (Nat.le_of_lt_add_one nlt) len
    rw [getElem_congr_idx hns, Array.getElem_push_eq]
    apply Int32.lt_iff_toInt_lt.mpr
    let p := S.primes[m].toInt.natAbs
    have pnn : 0 ≤ S.primes[m].toInt :=
      Int32.le_iff_toInt_le.mp (S.hprimesnn _ (Array.getElem_mem mlt'))
    rw [← Int.ofNat_natAbs_of_nonneg pnn]
    apply ((S.hpmem_iff p).mp _).1; unfold p
    rw [Int.ofNat_natAbs_of_nonneg pnn]
    apply Array.mem_map_of_mem; simp

-- Advance the loop which fills out the sieve, in the case where S.divs[i] ≠ 0
def advance_sieve_of_entry_ne_zero {P : SieveParams} (S : Sieve P)
  (hnend : ¬S.iter = iterator_int32_end _)
  (hinz : S.divs[S.iter.val.toInt.natAbs]'(sieve_iter_val_lt S hnend) ≠ 0) : Sieve P where
  divs := S.divs
  primes := S.primes
  iter := iterator_int32_next S.iter
  hsize := S.hsize
  hdivsnn := S.hdivsnn
  hmarked := S.hmarked
  hprimesnn := S.hprimesnn
  hpmem_iff := by
    intro p
    rw [iterator_int32_next_val_toInt _ hnend]
    rw [sieve_iter_inc]
    constructor
    · intro h
      obtain ⟨plt, pprime⟩ := (S.hpmem_iff p).mp h
      exact And.intro (Int.add_lt_add plt one_pos) pprime
    · -- TODO: Can we make this proof any shorter / simpler?
      -- It seems unnecessarly complex given that all we're doing is incrementing 'i'
      intro ⟨plt, pprime⟩
      apply (S.hpmem_iff p).mpr (And.intro (lt_of_le_of_ne (Int.le_of_lt_add_one plt) _) pprime)
      intro hpi
      have ppos : 0 < p := by
        apply Int.lt_of_ofNat_lt_ofNat
        rw [hpi]
        exact sieve_index_toInt_pos S
      -- Since entry 'i' is marked, 'i' is divisible by some element of primes, p'
      have hmark := S.hmarked S.iter.val.toInt.natAbs
        (by rwa [← hpi]) (sieve_iter_val_lt S hnend)
      rcases hmark.mpr hinz with ⟨p', p'mem, p'dvd⟩
      rw [← hpi] at p'dvd
      simp only [Int.natAbs_natCast] at p'dvd
      have p'nn : 0 ≤ p'.toInt :=
        Int32.le_iff_toInt_le.mp (S.hprimesnn p' p'mem)
      have hp'abs := Int.ofNat_natAbs_of_nonneg p'nn
      have : p'.toInt < S.iter.val.toInt ∧ Nat.Prime p'.toInt.natAbs := by
        rw [← hp'abs]
        apply ((S.hpmem_iff p'.toInt.natAbs).mp _)
        rw [hp'abs]
        exact Array.mem_map_of_mem p'mem
      rcases this with ⟨p'lt, p'prime⟩
      -- p' is prime, so it cannot be 1
      have p'ne1 : p'.toInt.natAbs ≠ 1 := by
        intro p'1
        rw [p'1] at p'prime
        exact Nat.prime_one_false p'prime
      -- Proof by contradiction: show that p cannot be prime
      absurd (Nat.prime_def.mp pprime).2 p'.toInt.natAbs; push_neg
      use Int.ofNat_dvd.mp (hp'abs ▸ p'dvd), p'ne1
      intro h
      apply Int.ofNat_inj.mpr at h
      rw [hpi, hp'abs] at h
      absurd h; push_neg
      exact ne_of_lt p'lt
  hdivs_dvd := S.hdivs_dvd
  hprimessize := by
    rw [iterator_int32_next_val_toInt _ hnend]
    rw [sieve_iter_inc]
    apply lt_trans _ (Int.add_lt_add_right S.hprimessize 1)
    simp
  hprimesinc := S.hprimesinc

-- Combine the two cases into a single advancement function
def advance_sieve {P : SieveParams} (S : Sieve P)
  (hnend : ¬S.iter = iterator_int32_end _) : Sieve P :=
  if hz : S.divs[S.iter.val.toInt.natAbs]'(sieve_iter_val_lt S hnend) = 0
  then advance_sieve_of_entry_eq_zero S hnend hz
  else advance_sieve_of_entry_ne_zero S hnend hz

-- Prove that 'Sieve' implements an iterator loop
instance {P : SieveParams} :
  LoopIterator (Sieve P) (IteratorInt32 (sieve_iter_params P)) where
  iter := fun S ↦ S.iter
  adv := advance_sieve
  hadv := by
    intro S hnend
    unfold advance_sieve
    split_ifs <;> rfl

@[simp] theorem sieve_term {P : SieveParams} (S : Sieve P) :
  LoopBase.term S = decide (S.iter = iterator_int32_end _) := rfl

def sieve_of_eratosthenes : Sieve InitSieveParams :=
  do_loop init_sieve

def primes : Array Int32 := sieve_of_eratosthenes.primes
def divs : Array Int32 := sieve_of_eratosthenes.divs

theorem sieve_of_eratosthenes_index :
  sieve_of_eratosthenes.iter.val = SIEVE_SIZE_32 := by
  unfold sieve_of_eratosthenes
  have := loop_term init_sieve
  rw [sieve_term, decide_eq_true_eq] at this
  rw [this]; rfl

theorem primes_nonneg : ∀ n ∈ primes, 0 ≤ n :=
  fun n nmem ↦ sieve_of_eratosthenes.hprimesnn n nmem

-- The elements of 'primes' are in-fact prime
theorem prime_of_mem_primes :
  ∀ n ∈ primes, ∃ (p : ℕ), n.toInt = p ∧ Nat.Prime p := by
  intro n nmem
  unfold primes at nmem
  let S := sieve_of_eratosthenes
  have nnn : 0 ≤ n.toInt := Int32.le_iff_toInt_le.mp (S.hprimesnn n nmem)
  have habs := Int.ofNat_natAbs_of_nonneg nnn
  use n.toInt.natAbs, habs.symm
  apply ((S.hpmem_iff n.toInt.natAbs).mp _).2
  rw [habs]
  exact Array.mem_map_of_mem nmem

-- The elements of 'primes' are positive
theorem primes_pos : ∀ n ∈ primes, 0 < n := by
  intro n nmem
  apply Int32.lt_iff_toInt_lt.mpr
  rcases prime_of_mem_primes n nmem with ⟨p, hp, pprime⟩
  rw [hp]
  exact Int.ofNat_lt_ofNat_of_lt (Nat.Prime.pos pprime)

-- All elements of 'primes' are less than SIEVE_SIZE
theorem lt_of_mem_primes :
  ∀ n ∈ primes, n.toInt < SIEVE_SIZE := by
  intro n nmem
  unfold primes at nmem
  let S := sieve_of_eratosthenes
  have nnn : 0 ≤ n.toInt := Int32.le_iff_toInt_le.mp (S.hprimesnn n nmem)
  have habs := Int.ofNat_natAbs_of_nonneg nnn
  rw [← habs]
  rw [← sieve_size_32_toInt, ← init_sieve_params_size]
  rw [← sieve_iter_finish]
  apply Int.lt_of_lt_of_le _ (Int32.le_iff_toInt_le.mp sieve_of_eratosthenes.iter.hvalle)
  apply ((S.hpmem_iff n.toInt.natAbs).mp _).1
  rw [habs]
  exact Array.mem_map_of_mem nmem

-- All primes less than 'SIEVE_SIZE' are in 'primes'
theorem mem_primes_of_prime_of_lt (p : ℕ) (hprime : Nat.Prime p) (plt : p < SIEVE_SIZE) :
  ∃ n ∈ primes, n.toInt = p := by
  let S := sieve_of_eratosthenes
  apply Int.ofNat_lt_ofNat_of_lt at plt
  rw [← sieve_size_32_toInt, ← sieve_of_eratosthenes_index] at plt
  exact Array.exists_of_mem_map ((S.hpmem_iff _).mpr ⟨plt, hprime⟩)

@[simp] theorem divs_size : divs.size = SIEVE_SIZE := by
  unfold divs
  apply Int.ofNat_inj.mp
  rw [sieve_of_eratosthenes.hsize]
  rw [init_sieve_params_size]; rfl

-- Each entry in 'divs' indicates the smallest divisor of the index of that entry.
-- Note that entry '1' is undefined. Entry '0' *is* defined but not worth proving.
theorem divs_getElem_dvd_and_le :
  ∀ n, (nlt : n < divs.size) → 1 < n →
  (divs[n]'nlt).toInt ∣ n ∧
  ∀ m, 1 < m → m ∣ n → (divs[n]'nlt).toInt ≤ m := by
  intro n nlt ltn
  let S := sieve_of_eratosthenes
  apply S.hdivs_dvd n nlt
  apply sieve_marked_of_lt_index S n ltn
  rw [sieve_of_eratosthenes_index]
  convert Int.ofNat_lt_ofNat_of_lt nlt
  rw [divs_size]; rfl

set_option linter.style.nativeDecide false
theorem primes_size : primes.size = 78498 := by native_decide

-- In particular, 2 ∈ primes
theorem primes_two_mem : 2 ∈ primes := by
  rcases mem_primes_of_prime_of_lt 2
    (Nat.prime_two) (by unfold SIEVE_SIZE; simp) with ⟨n, nprime, n2⟩
  convert nprime
  apply Int32.toInt_inj.mp
  rw [n2]; simp

-- Since 2 ∈ primes, primes ≠ #[]
theorem primes_ne_empty : primes ≠ #[] :=
  Array.ne_empty_of_mem primes_two_mem

theorem primes_size_pos : 0 < primes.size :=
  Array.size_pos_of_mem primes_two_mem

-- The last element in 'primes' is 999983
-- We prove this by showing primes.back is at least that value and that all
-- larger values less than SIEVE_SIZE are composite
theorem primes_back : primes.back (Array.size_pos_of_mem primes_two_mem) = 999983 := by
  -- Let the last element in primes correspond to the natural number 'p'
  rcases prime_of_mem_primes _ (Array.back_mem primes_size_pos) with ⟨p, hp, pprime⟩
  apply Int32.toInt_inj.mp
  simp only [Int32.reduceToInt]
  rw [hp]
  apply Int.ofNat_inj.mpr
  -- Prove primes.back is at least 999983
  have lep : 999983 ≤ p := by
    apply Int.le_of_ofNat_le_ofNat
    rw [← hp]
    simp only [Nat.cast_ofNat]
    -- Prove that 999983 is in the list and let 'i' be its location
    have hprime : Nat.Prime 999983 := by norm_num
    rcases mem_primes_of_prime_of_lt _
      hprime (by unfold SIEVE_SIZE; simp) with ⟨n, nprime, neq⟩
    rcases Array.getElem_of_mem nprime with ⟨i, ilt, hpin⟩
    rw [← Int32.toInt_inj, neq] at hpin
    simp only [Nat.cast_ofNat] at hpin
    rw [← hpin]
    apply Int32.le_iff_toInt_le.mp
    rw [Array.back_eq_getElem primes_size_pos]
    by_cases hips : i = primes.size - 1
    · subst hips
      exact Int32.le_refl _
    rename' hips => hineps; push_neg at hineps
    apply Int32.le_of_lt
    have ilt' : i < primes.size - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt ilt) hineps
    apply Sieve.hprimesinc _ i (primes.size - 1) ilt'
  by_contra! pne
  have ltp := lt_of_le_of_ne lep pne.symm
  have plt : p < 1000001 := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← hp]
    exact lt_of_mem_primes _ (Array.back_mem primes_size_pos)
  -- Every remaining possible value of p is composite
  -- Provide a factor pair for each value to show it is not prime
  apply (Nat.not_prime_iff_exists_mul_eq (le_of_lt (lt_trans (by simp) ltp))).mpr _ pprime
  interval_cases p
  · use 2, 499992; simp
  · use 5, 199997; simp
  · use 2, 499993; simp
  · use 3, 333329; simp
  · use 2, 499994; simp
  · use 19, 52631; simp
  · use 2, 499995; simp
  · use 17, 58823; simp
  · use 2, 499996; simp
  · use 3, 333331; simp
  · use 2, 499997; simp
  · use 5, 199999; simp
  · use 2, 499998; simp
  · use 757, 1321; simp
  · use 2, 499999; simp
  · use 3, 333333; simp
  · use 2, 500000; simp

-- Prove that the size of the primes array is less than the sieve size
-- Note that this result is less precise than 'primes_size' (above)
-- but doesn't rely on "native decide"
theorem primes_size_lt_sieve_size : primes.size < SIEVE_SIZE := by
  unfold primes
  apply Int.lt_of_ofNat_lt_ofNat
  apply lt_of_lt_of_eq sieve_of_eratosthenes.hprimessize
  rw [← sieve_size_32_toInt, sieve_of_eratosthenes_index]

-- For every 32-bit integer that is not prime and not equal to 1 or -1,
-- it is divisible by some member of 'primes'.
theorem mem_primes_dvd_exists_of_not_prime
  (n : Int32) (hnprime : ¬Nat.Prime n.toInt.natAbs) (hne1 : n.toInt.natAbs ≠ 1) :
  ∃ p ∈ primes, p.toInt ∣ n.toInt := by
  -- First handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    exact ⟨2, And.intro primes_two_mem ⟨0, by decide⟩⟩
  rename' nz => nnz; push_neg at nnz
  -- Handle the case where n = -2^31
  by_cases nmin : n = Int32.minValue
  · subst nmin
    exact ⟨2, And.intro primes_two_mem ⟨-2^30, by decide⟩⟩
  rename' nmin => nnemin; push_neg at nnemin
  have minltn := int32_minval_lt_of_ne_minval _ nnemin.symm
  -- The absolute value of n is at least two
  have twole : 2 ≤ n.toInt.natAbs := by
    by_contra! h
    apply nnz (Int32.toInt_inj.mp (Int.natAbs_eq_zero.mp _))
    by_contra! nnz
    interval_cases n.toInt.natAbs
    · exact nnz rfl
    · exact hne1 rfl
  -- Since n is not prime, it must have some divisor less than or equal to its square root
  rw [Nat.prime_def_le_sqrt] at hnprime; push_neg at hnprime
  rcases hnprime twole with ⟨d, led, dle, ddvd⟩
  -- That divisor must be less than the size of the sieve
  have dle' : d < SIEVE_SIZE := by
    unfold SIEVE_SIZE
    by_contra! led'
    have h := Nat.mul_le_mul led' led'
    absurd le_trans h (Nat.mul_le_mul dle dle)
    push_neg
    apply lt_trans (Nat.sqrt_mul_sqrt_lt_succ _)
    apply lt_trans (Nat.add_lt_add_right (int32_natAbs_toInt_lt n minltn) 1)
    decide
  have dne1 : d ≠ 1 := by
    intro h; subst h
    absurd led; decide
  -- Let p be a prime a prime dividing d
  rcases Nat.exists_prime_and_dvd dne1 with ⟨p, pprime, pdvd⟩
  have ple := Nat.le_of_dvd (lt_of_lt_of_le (by decide) led) pdvd
  -- Since d < SIEVE_SIZE, there must exist p' ∈ primes such that p' divides d
  rcases mem_primes_of_prime_of_lt p pprime (lt_of_le_of_lt ple dle') with ⟨p', p'mem, hp'⟩
  rw [← Int.ofNat_dvd, ← hp'] at pdvd
  -- Since p' ∣ d and d ∣ n, p' ∣ n
  exact ⟨p', p'mem, Int.dvd_trans pdvd (Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr ddvd))⟩

end CodeChef
