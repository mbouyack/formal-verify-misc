import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import FormalVerifyMisc.Int32.Basic

namespace CodeChef

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

-- Prevent '2^31' from having to be written as '2 ^ 31'
set_option linter.style.commandStart false

def SIEVE_SIZE : ℕ := 1000001

structure Sieve (L : ℕ) where
  -- The sieve - with non-zero values indicating divisors
  divs : Array Int32
  -- The list of primes found thus far
  primes : Array Int32
  -- Current search location
  i : Int32
  -- The size of 'divs' is given by 'L'
  hsize : divs.size = L
  -- The length of the sieve has an upper bound
  -- This is required to avoid exceeding Int32.maxValue
  hLlt : L < 2^30
  -- The entries in the sieve are non-negative
  hdivsnn : ∀ x ∈ divs, 0 ≤ x
  -- 'i' is positive
  hipos : 0 < i.toInt
  -- 'i' is less than or equal to 'L' - the size of the sieve
  -- TODO: Do we actually need this?
  hile : i.toInt ≤ (L : ℤ)
  -- Each entry in the sieve is marked if-and-only-if its index
  -- is divisible by some prime in 'primes'
  hmarked : ∀ j, (0 < j) → (jlt : j < divs.size) →
    (∃ p ∈ primes, p.toInt ∣ (j : ℤ)) ↔ divs[j] ≠ 0
  -- A natural number is in 'primes' if-and-only-if
  -- it is a prime less than 'i'
  hpmem_iff : ∀ p : ℕ,
    ((p : ℤ) ∈ (Array.map Int32.toInt primes) ↔
     (p : ℤ) < i.toInt ∧ Nat.Prime p)
  -- If an entry in the sieve is non-zero, its value corresponds to the smallest
  -- divisor of its index greater than 1
  hdivs_dvd : ∀ j, (jlt : j < divs.size) → divs[j]'(jlt) ≠ 0 →
    (divs[j]'(jlt)).toInt ∣ j ∧
    ∀ y, 1 < y → y ∣ j → (divs[j]'(jlt)).toInt ≤ (y : ℤ)

theorem sieve_length_pos {L : ℕ} (S : Sieve L) : 0 < S.divs.size := by
  rw [S.hsize]
  apply Int.lt_of_ofNat_lt_ofNat
  exact lt_of_lt_of_le S.hipos S.hile

-- Show equivalence for the two ways of expressing the upper bound on an index into S.divs
theorem lt_sieve_length_iff_of_nonneg
  {L : ℕ} (S : Sieve L) (n : Int32) (hnnn : 0 ≤ n) :
  n.toInt.natAbs < S.divs.size ↔ n.toInt < (L : ℤ) := by
  rw [← Int.ofNat_lt]
  rw [Int.ofNat_natAbs_of_nonneg (Int32.le_iff_toInt_le.mp hnnn), S.hsize]

theorem lt_sieve_length_of_lt_index
  {L : ℕ} {S : Sieve L} {j : ℕ} (jlt : (j : ℤ) < S.i.toInt) : j < S.divs.size := by
  rw [S.hsize]
  apply Int.lt_of_ofNat_lt_ofNat
  apply lt_of_lt_of_le jlt S.hile

-- Every entry properly between 1 and 'i' is marked
-- This is the result of combining 'hmarked' (every entry with a divisor in
-- 'primes' is marked) and 'hpmem_iff' (every prime less than S.i is in 'primes)
theorem sieve_marked_of_lt_index {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (ltj : 1 < j) → (jlt : (j : ℤ) < S.i.toInt) →
  S.divs[j]'(lt_sieve_length_of_lt_index jlt) ≠ 0 := by
  intro j ltj jlt
  have jlt' := lt_sieve_length_of_lt_index jlt
  -- Get some prime 'p' that divides 'j'
  rcases Nat.exists_prime_and_dvd (ne_of_lt ltj).symm with ⟨p, pprime, pdvd⟩
  have jpos : 0 < j := lt_trans (by simp) ltj
  apply (S.hmarked j jpos jlt').mp
  have ple := Nat.le_of_dvd jpos pdvd
  have plt : (p : ℤ) < S.i.toInt :=
    lt_of_le_of_lt (Int.ofNat_le_ofNat_of_le ple) jlt
  -- Get the Int32 that corresponds to 'p' in 'primes' (it must exist by 'hpmem_iff')
  rcases Array.exists_of_mem_map ((S.hpmem_iff p).mpr ⟨plt, pprime⟩) with ⟨p', p'mem, hp'p⟩
  apply Int.ofNat_dvd.mpr at pdvd
  use p', p'mem
  rwa [hp'p]

-- Construct a sieve with all elements set to zero
def init_sieve : Sieve SIEVE_SIZE where
  divs := Array.replicate SIEVE_SIZE 0
  primes := #[]
  i := 2
  hsize := Array.size_replicate
  hLlt := by
    unfold SIEVE_SIZE;
    simp
  hdivsnn := by
    intro x xmem
    rw [(Array.mem_replicate.mp xmem).2]; rfl
  hipos := by simp
  hile := by
    unfold SIEVE_SIZE
    simp
  hmarked := by simp
  hpmem_iff := by
    intro p; simp; intro plt
    interval_cases p <;> norm_num
  hdivs_dvd := by
    intro j jlt hnz
    constructor
    · absurd hnz; simp
    · intro y lty ydvd; simp

-- Prove that a loop that terminates by showing that 'cur' increases by 'inc'
-- on each iteration and that its absolute value never exceeds 'ub'.
--
-- TODO: This will likely be useful in other file as well
-- consider moving it to a separate file.
theorem termination_by_increasing_int32 (cur inc : Int32) (ub : ℕ)
  (curpos : 0 < cur) (incpos : 0 < inc)
  (curlt : cur.toInt < (ub : ℤ)) (inclt : inc.toInt < (ub : ℤ))
  (uble : ub ≤ 2^30) :
  ub - (cur + inc).toInt.natAbs < ub - cur.toInt.natAbs := by
  have curpos' : 0 < cur.toInt := Int32.lt_iff_toInt_lt.mp curpos
  have incpos' : 0 < inc.toInt := Int32.lt_iff_toInt_lt.mp incpos
  rw [int32_toInt_add_of_add_bounds
    (le_of_lt curpos')
    (lt_of_lt_of_le curlt (Int.ofNat_le_ofNat_of_le uble))
    (le_of_lt incpos')
    (lt_of_lt_of_le inclt (Int.ofNat_le_ofNat_of_le uble))
    (by simp) (by simp)]
  rw [← Int.ofNat_natAbs_of_nonneg (le_of_lt curpos')] at curlt
  apply Nat.sub_lt_sub_left (Int.lt_of_ofNat_lt_ofNat curlt)
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt curpos')
  exact Int.lt_add_of_pos_right _ incpos'

-- The state and constraints required for the 'mark_multiples' loop
@[ext] structure MarkMultiplesState where
  A : Array Int32
  inc : Int32
  cur : Int32
  incdvd : inc.toInt ∣ cur.toInt
  curpos : 0 < cur.toInt
  incpos : 0 < inc.toInt
  hAslt : A.size < 2^30
  hmarked : ∀ (j : ℕ),
    (jpos : 0 < j) → (jlt : j < min cur.toInt A.size) → inc.toInt ∣ (j : ℤ) →
    A[j]'(Int.lt_of_ofNat_lt_ofNat ((lt_min_iff.mp jlt).2)) ≠ 0

def mark_multiples_state_of_sieve {L : ℕ} (S : Sieve L) : MarkMultiplesState where
  A := S.divs
  inc := S.i
  cur := S.i
  incdvd := by simp
  curpos := S.hipos
  incpos := S.hipos
  hAslt := by rw [S.hsize]; exact S.hLlt
  hmarked := by
    intro j jpos jlt dvdj
    have jlti := (lt_min_iff.mp jlt).1
    have lej : 1 ≤ j := Nat.add_one_le_of_lt jpos
    -- Every entry in the sieve between 1 and i is marked
    apply sieve_marked_of_lt_index S j (lt_of_le_of_ne lej _) jlti
    intro j1; subst j1
    -- Now handle the case where j = 1
    -- This leads to a contradiction because i ∣ j and 1 < i
    exact not_lt_of_ge (Int.le_of_dvd (by simp) dvdj) jlti

@[simp] theorem mark_multiples_state_of_sieve_size {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve S).A.size = S.divs.size := rfl

@[simp] theorem mark_multiples_state_of_sieve_inc {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve S).inc = S.i := rfl

@[simp] theorem mark_multiples_state_of_sieve_cur {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve S).cur = S.i := rfl

-- When adding 'inc' to 'cur' we can move the addition across the 'toInt' conversion
lemma mms_cur_add_inc_toInt
  (MMS : MarkMultiplesState) (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (MMS.cur + MMS.inc).toInt = MMS.cur.toInt + MMS.inc.toInt := by
  have curnn : 0 ≤ MMS.cur.toInt := le_of_lt MMS.curpos
  have incnn : 0 ≤ MMS.inc.toInt := le_of_lt MMS.incpos
  have curlt' : MMS.cur.toInt < MMS.A.size := by
    convert Int.ofNat_lt_ofNat_of_lt curlt
    exact (Int.ofNat_natAbs_of_nonneg curnn).symm
  have incle := Int.le_of_dvd MMS.curpos MMS.incdvd
  have inclt' := lt_of_le_of_lt incle curlt'
  apply int32_toInt_add_of_add_bounds curnn curlt' incnn inclt' (by simp)
  rw [Int.ofNat_add_ofNat]
  convert Int.ofNat_le_ofNat_of_le (le_of_lt (Nat.add_lt_add MMS.hAslt MMS.hAslt)) using 1

-- Advance the loop marking multiples of MMS.inc in MMS.A
def mark_multiples_advance (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) : MarkMultiplesState where
  A := if MMS.A[MMS.cur.toInt.natAbs]'curlt ≠ 0 then MMS.A
    else MMS.A.set MMS.cur.toInt.natAbs MMS.inc
  inc := MMS.inc
  cur := MMS.cur + MMS.inc
  incdvd := by
    rw [mms_cur_add_inc_toInt MMS curlt]
    exact Int.dvd_add MMS.incdvd (by simp)
  curpos := by
    rw [mms_cur_add_inc_toInt MMS curlt]
    exact Int.add_lt_add MMS.curpos MMS.incpos
  incpos := MMS.incpos
  hAslt := by
    convert MMS.hAslt using 1
    split_ifs with h
    · rfl
    · exact Array.size_set curlt
  hmarked := by
    -- TODO: This proof seems much longer than necessary.
    -- Is there anything we can do to shorten / simplify it?
    intro j jpos jlt jdvd
    have := mms_cur_add_inc_toInt MMS curlt
    have incnz : MMS.inc ≠ 0 := by
      intro hz
      absurd Int32.toInt_inj.mpr hz; push_neg; symm
      exact ne_of_lt MMS.incpos
    by_cases jlt' : j < min MMS.cur.toInt MMS.A.size
    · obtain ⟨jlt_left, jlt_right⟩ := Int.lt_min.mp jlt'
      have jlt_left := (Int.lt_min.mp jlt').1
      have jlt_right := Int.lt_of_ofNat_lt_ofNat (Int.lt_min.mp jlt').2
      have hAjnz : MMS.A[j]'jlt_right ≠ 0 := by
        exact MMS.hmarked j jpos jlt' jdvd
      split_ifs with h
      · assumption
      · by_cases curj : MMS.cur.toInt.natAbs = j
        · rwa [← getElem_congr_idx curj, Array.getElem_set_self]
          convert curlt using 1
          exact Array.size_set curlt
        push_neg at curj
        rwa [Array.getElem_set_ne curlt jlt_right curj]
    rename' jlt' => jlb; push_neg at jlb
    have curlt' := Int.ofNat_lt_ofNat_of_lt curlt
    rw [Int.ofNat_natAbs_of_nonneg (le_of_lt MMS.curpos)] at curlt'
    rw [Int.min_eq_left (le_of_lt curlt')] at jlb
    have jlt' := this ▸ (Int.lt_min.mp jlt).1
    -- Rewrite 'j' and 'cur' as multiples of 'inc' to prove cur = j
    rcases dvd_def.mp jdvd with ⟨kj, hkj⟩
    rcases dvd_def.mp MMS.incdvd with ⟨kcur, hkcur⟩
    rw [hkj, hkcur] at jlt' jlb
    rw [Int.mul_le_mul_left MMS.incpos] at jlb
    nth_rw 3 [← mul_one MMS.inc.toInt] at jlt'
    rw [← mul_add, Int.mul_lt_mul_left MMS.incpos] at jlt'
    have hks := le_antisymm (Int.le_of_lt_add_one jlt') jlb
    rw [hks] at hkj
    rw [← hkj] at hkcur
    rename' hkcur => curj
    have curj' : MMS.cur.toInt.natAbs = j := by
      rw [curj]; simp
    split_ifs with h
    · rw [← getElem_congr_idx curj']
      assumption
    · rwa [← getElem_congr_idx curj', Array.getElem_set_self]
      rwa [Array.size_set]

-- The size of the MarkMultiplesState doesn't change upon advancing
@[simp] theorem mark_multiples_advance_size (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).A.size = MMS.A.size := by
  unfold mark_multiples_advance; dsimp
  split_ifs with h <;> simp

@[simp] theorem mark_multiples_advance_inc (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).inc = MMS.inc := rfl

-- After advancing the MarkMultiplesState, the new 'cur' value is
-- the sum of the old 'cur' value and the old 'inc' value
@[simp] theorem mark_multiples_advance_cur (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).cur.toInt = MMS.cur.toInt + MMS.inc.toInt := by
  unfold mark_multiples_advance; dsimp
  exact mms_cur_add_inc_toInt MMS curlt

-- Advancing the 'mark_multiples' loop has no effect
-- on entries which have already been marked.
theorem mark_multiples_advance_unchanged_of_marked (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → MMS.A[j] ≠ 0 →
  (mark_multiples_advance MMS curlt).A[j]'(by
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
theorem mark_multiples_advance_unchanged_of_not_dvd (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → ¬MMS.inc.toInt ∣ (j : ℤ) →
  (mark_multiples_advance MMS curlt).A[j]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.A[j] := by
  intro j jpos jlt jndvd
  unfold mark_multiples_advance; dsimp
  split_ifs with h
  · apply Array.getElem_set_ne
    contrapose! jndvd
    convert MMS.incdvd
    rw [← jndvd]; simp
    exact le_of_lt MMS.curpos
  · rfl

-- Advancing the 'mark_multiples' loop has no effect
-- on entries other than 'cur'
theorem mark_multiples_advance_unchanged_of_not_cur (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → MMS.cur.toInt ≠ j →
  (mark_multiples_advance MMS curlt).A[j]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.A[j] := by
  intro j jpos jlt curnej
  unfold mark_multiples_advance; dsimp
  split_ifs with h
  · apply Array.getElem_set_ne
    contrapose! curnej
    rw [← curnej]; symm
    apply Int.ofNat_natAbs_of_nonneg
    exact le_of_lt MMS.curpos
  · rfl

-- The first entry in the array is never modifed
theorem mark_multiples_advance_unchanged_of_first (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).A[0]'(by
    rw [mark_multiples_advance_size]
    exact Nat.zero_lt_of_lt curlt
  ) = MMS.A[0] := by
    unfold mark_multiples_advance; dsimp
    split_ifs with h
    · apply Array.getElem_set_ne
      exact Int.natAbs_ne_zero.mpr (ne_of_lt MMS.curpos).symm
    · rfl

-- If the current entry was previously zero, 'mark_multiples_advance' will set it to MMS.inc
theorem mark_multiples_advance_changed (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  MMS.A[MMS.cur.toInt.natAbs] = 0 →
  (mark_multiples_advance MMS curlt).A[MMS.cur.toInt.natAbs]'(by
    rwa [mark_multiples_advance_size]
  ) = MMS.inc := by
  intro hz
  unfold mark_multiples_advance; simp
  rw [getElem_congr_coll (if_pos hz)]
  apply Array.getElem_set_self

-- Prove 'mark_multiples' terminates
lemma mark_multiples_terminates (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (fun f mms' ↦ f mms' < f MMS)
  (fun mms ↦ mms.A.size - mms.cur.toInt.natAbs)
  (mark_multiples_advance MMS curlt) := by
  dsimp
  rw [mark_multiples_advance_size, mark_multiples_advance_cur]
  apply Nat.sub_lt_sub_left curlt
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt MMS.curpos)
  exact Int.lt_add_of_pos_right _ MMS.incpos

-- Recursively mark all multiples using 'mark_multiples_advance'
def mark_multiples_impl (MMS : MarkMultiplesState) : MarkMultiplesState :=
  if curlt : MMS.cur.toInt.natAbs < MMS.A.size then
    mark_multiples_impl (mark_multiples_advance MMS curlt) else
    MMS
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS curlt

-- Calling 'mark_multiples_impl' has no effect on the array size
@[simp] theorem mark_multiples_impl_size (MMS : MarkMultiplesState) :
  (mark_multiples_impl MMS).A.size = MMS.A.size := by
  unfold mark_multiples_impl
  split_ifs with h
  · rw [mark_multiples_impl_size, mark_multiples_advance_size]
  · rfl
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS h

-- Any non-zero entries in MMS.A will be unchanged by calling 'mark_multiples_impl'
theorem mark_multiples_impl_unchanged_of_marked (MMS : MarkMultiplesState) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → MMS.A[j]'jlt ≠ 0 →
  (mark_multiples_impl MMS).A[j]'(by rwa [mark_multiples_impl_size]) = MMS.A[j]'jlt := by
  intro j jpos jlt hAjnz
  unfold mark_multiples_impl
  split_ifs with h
  · rw [mark_multiples_impl_unchanged_of_marked _ j jpos]
    · apply mark_multiples_advance_unchanged_of_marked <;> assumption
    · rwa [mark_multiples_advance_size]
    · rw [mark_multiples_advance_unchanged_of_marked] <;> assumption
  · rfl
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS h

theorem mark_multiples_impl_unchanged_of_not_dvd (MMS : MarkMultiplesState) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < MMS.A.size) → ¬MMS.inc.toInt ∣ (j : ℤ) →
  (mark_multiples_impl MMS).A[j]'(by rwa [mark_multiples_impl_size]) = MMS.A[j]'jlt := by
  intro j jpos jlt jndvd
  unfold mark_multiples_impl
  split_ifs with h
  · rw [mark_multiples_impl_unchanged_of_not_dvd _ j jpos]
    · apply mark_multiples_advance_unchanged_of_not_dvd <;> assumption
    · rwa [mark_multiples_advance_size]
    · simpa
  · rfl
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS h

-- The first entry in the array in never modified
-- Note that to even be able to state the theorem, we need a proof that the array is non-empty
theorem mark_multiples_impl_unchanged_of_first (MMS : MarkMultiplesState)
  {lb : ℕ} (hlb : lb < MMS.A.size) :
  (mark_multiples_impl MMS).A[0]'(by simp; exact Nat.zero_lt_of_lt hlb) = MMS.A[0] := by
  unfold mark_multiples_impl
  split_ifs with h
  · rw [mark_multiples_impl_unchanged_of_first _ (by simpa)]
    rw [mark_multiples_advance_unchanged_of_first]
  · rfl
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS h

-- Any entry after (and including) the current entry that is zero and has
-- index divisible by 'inc' will be set to 'inc' by mark_multiples_impl
theorem mark_multiples_impl_changed (MMS : MarkMultiplesState) :
  ∀ (j : ℕ), MMS.cur.toInt ≤ j → (jlt : j < MMS.A.size) →
  MMS.A[j] = 0 → MMS.inc.toInt ∣ (j : ℤ) →
  (mark_multiples_impl MMS).A[j]'(by rwa [mark_multiples_impl_size]) = MMS.inc := by
  intro j lej jlt hz hdvd
  unfold mark_multiples_impl
  split_ifs with h
  · -- If cur = j, that entry will be marked by 'mark_multiples_advance'
    -- but will be unchanged by 'mark_multiples_impl' so that case
    -- must be dealt with separately.
    by_cases curj : MMS.cur.toInt = j
    · apply congr_arg Int.natAbs at curj
      simp at curj; subst curj
      rw [mark_multiples_impl_unchanged_of_marked]
      · apply mark_multiples_advance_changed MMS h hz
      · apply Int.lt_of_ofNat_lt_ofNat
        exact lt_of_lt_of_le MMS.curpos lej
      · simpa
      · have incnz : MMS.inc ≠ 0 := by
          symm; apply Int32.ne_of_lt
          apply Int32.lt_iff_toInt_lt.mpr
          exact MMS.incpos
        rwa [mark_multiples_advance_changed]
        assumption
    rename' curj => curnej; push_neg at curnej
    have ltj := lt_of_le_of_ne lej curnej
    -- Now handle the remaining case where 'mark_multiples_advance' has no
    -- effect on entry 'j', but 'mark_multiples_impl' does
    rw [mark_multiples_impl_changed]
    · simp
    · simp
      -- Rewite 'cur' and 'j' as multiples of 'inc'
      rcases dvd_def.mp hdvd with ⟨kj, hkj⟩
      rcases dvd_def.mp MMS.incdvd with ⟨kcur, hkcur⟩
      -- For some reason 'rw at *' doesn't work here
      rw [hkj]; rw [hkj] at ltj
      rw [hkcur]; rw [hkcur] at ltj
      -- Divide out 'inc' from the relevant inequalities
      nth_rw 2 [← mul_one MMS.inc.toInt]
      rw [← mul_add]
      rw [Int.mul_lt_mul_left MMS.incpos] at ltj
      rw [Int.mul_le_mul_left MMS.incpos]
      exact Int.add_one_le_of_lt ltj
    · simpa
    · rw [mark_multiples_advance_unchanged_of_not_cur] <;> try assumption
      apply Int.lt_of_ofNat_lt_ofNat
      exact lt_of_lt_of_le MMS.curpos lej
    · simpa
  · absurd h
    apply lt_of_le_of_lt (Int.le_of_ofNat_le_ofNat _) jlt
    convert lej
    exact Int.ofNat_natAbs_of_nonneg (le_of_lt MMS.curpos)
termination_by MMS.A.size - MMS.cur.toInt.natAbs
decreasing_by
  exact mark_multiples_terminates MMS h

-- Extract S.divs and mark every entry which is a multiple of S.i
def mark_multiples {L : ℕ} (S : Sieve L) : MarkMultiplesState :=
  mark_multiples_impl (mark_multiples_state_of_sieve S)

-- The size of the marked array is the same as the size of the sieve
@[simp] theorem mark_multiples_size {L : ℕ} (S : Sieve L) :
  (mark_multiples S).A.size = S.divs.size := by
  unfold mark_multiples
  rw [mark_multiples_impl_size]; simp

-- 'mark_multiples' has no effect on entries in the sieve
-- that were previous marked
theorem mark_multiples_unchanged_of_marked {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.divs[j] ≠ 0 →
  (mark_multiples S).A[j]'(by rwa [mark_multiples_size]) = S.divs[j] := by
    intro j jpos jlt hnz
    unfold mark_multiples
    rw [mark_multiples_impl_unchanged_of_marked _ j jpos]
    · rfl
    · contrapose! hnz
      convert hnz

-- 'mark_multiples' has no effect on entries in the sieve
-- whose indices are not divisible by 'inc'
theorem mark_multiples_unchanged_of_not_dvd {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → ¬S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S).A[j]'(by rwa [mark_multiples_size]) = S.divs[j] := by
  intro j jpos jlt jndvd
  unfold mark_multiples
  rw [mark_multiples_impl_unchanged_of_not_dvd _ j jpos]
  · rfl
  · simpa

-- 'mark_multiples' has no effect on the first entry in the sieve
theorem mark_multiples_unchanged_of_first {L : ℕ} (S : Sieve L) :
  (mark_multiples S).A[0]'(
    (mark_multiples_size S) ▸ (sieve_length_pos S)
  ) = S.divs[0]'(sieve_length_pos S) := by
  unfold mark_multiples
  rw [mark_multiples_impl_unchanged_of_first _ (by simp; exact sieve_length_pos S)]
  rfl

-- Any entry that was zero and has index divisible by 'inc' will be
-- set to 'inc' by mark_multiples
theorem mark_multiples_changed {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) →
  S.divs[j] = 0 → S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S).A[j]'(by rwa [mark_multiples_size]) = S.i := by
  intro j jpos jlt hz hdvd
  unfold mark_multiples
  rw [mark_multiples_impl_changed] <;> try simp; try assumption
  · exact Int.le_of_dvd (Int.ofNat_lt_ofNat_of_lt jpos) hdvd
  · convert hz

lemma sieve_toInt_index_succ {L : ℕ} (S : Sieve L) :
  (S.i + 1).toInt = S.i.toInt + 1 := by
  apply int32_toInt_add_of_bounds
  constructor
  · apply le_of_lt
    apply Int.lt_add_of_sub_right_lt
    exact lt_trans (by simp) S.hipos
  · apply Int.add_lt_of_lt_sub_right
    apply Int.lt_of_le_sub_one (le_of_lt _)
    apply lt_trans (lt_of_le_of_lt S.hile (Int.ofNat_lt_ofNat_of_lt S.hLlt))
    simp

end CodeChef
