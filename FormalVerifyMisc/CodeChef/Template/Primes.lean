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
  -- 'i' is greater than 1
  hlti : 1 < i.toInt
  -- 'i' is less than or equal to 'L' - the size of the sieve
  -- TODO: Do we actually need this?
  hile : i.toInt ≤ (L : ℤ)
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
     (p : ℤ) < i.toInt ∧ Nat.Prime p)
  -- If an entry in the sieve is non-zero, its value corresponds to the smallest
  -- divisor of its index greater than 1
  hdivs_dvd : ∀ j, (jlt : j < divs.size) → divs[j]'(jlt) ≠ 0 →
    (divs[j]'(jlt)).toInt ∣ j ∧
    ∀ y, 1 < y → y ∣ j → (divs[j]'(jlt)).toInt ≤ (y : ℤ)

theorem sieve_index_toInt_pos {L : ℕ} (S : Sieve L) : 0 < S.i.toInt := lt_trans (by simp) S.hlti

theorem sieve_index_pos {L : ℕ} (S : Sieve L) : 0 < S.i :=
  Int32.lt_iff_toInt_lt.mpr (sieve_index_toInt_pos S)

theorem sieve_length_pos {L : ℕ} (S : Sieve L) : 0 < S.divs.size := by
  rw [S.hsize]
  apply Int.lt_of_ofNat_lt_ofNat
  exact lt_of_lt_of_le (sieve_index_toInt_pos S) S.hile

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

-- If an entry's index is divisible by some natural number less than S.i, the entry is marked
-- This is a more useable consequence of 'hmarked'
theorem sieve_marked_of_dvd_of_lt {L : ℕ} (S : Sieve L) :
  ∀ (m n : ℕ), 0 < n → (nlt : n < S.divs.size) →
  m ≠ 1 → m ∣ n → m < S.i.toInt → S.divs[n]'nlt ≠ 0 := by
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
  hlti := by simp
  hile := by
    unfold SIEVE_SIZE
    simp
  hmarked := by simp
  hprimesnn := fun p pmem ↦ False.elim (Array.not_mem_empty _ pmem)
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

def mark_multiples_state_of_sieve {L : ℕ} (S : Sieve L) : MarkMultiplesState where
  A := S.divs
  inc := S.i
  cur := S.i
  incdvd := by simp
  curpos := sieve_index_toInt_pos S
  incpos := sieve_index_toInt_pos S
  hAslt := by rw [S.hsize]; exact S.hLlt

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

-- Any entry whose index is divisible by 'inc' will be marked
-- after calling mark_multiples
theorem mark_multiples_marked_of_dvd {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S).A[j]'(by rwa [mark_multiples_size]) ≠ 0 := by
  intro j jpos jlt idvd
  by_cases h : S.divs[j]'jlt = 0
  · rw [mark_multiples_changed S j jpos jlt h idvd]; symm
    exact Int32.ne_of_lt (Int32.lt_iff_toInt_lt.mpr (sieve_index_toInt_pos S))
  push_neg at h
  rwa [mark_multiples_unchanged_of_marked S j jpos jlt h]

lemma sieve_toInt_index_succ {L : ℕ} (S : Sieve L) :
  (S.i + 1).toInt = S.i.toInt + 1 := by
  apply int32_toInt_add_of_bounds
  constructor
  · apply le_of_lt
    apply Int.lt_add_of_sub_right_lt
    exact lt_trans (by simp) (sieve_index_toInt_pos S)
  · apply Int.add_lt_of_lt_sub_right
    apply Int.lt_of_le_sub_one (le_of_lt _)
    apply lt_trans (lt_of_le_of_lt S.hile (Int.ofNat_lt_ofNat_of_lt S.hLlt))
    simp

-- Advance the loop which fills out the sieve, in the case where S.divs[i] = 0
def advance_sieve_of_entry_eq_zero {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hiz : S.divs[S.i.toInt.natAbs]'ilt = 0) : Sieve L where
  divs := (mark_multiples S).A
  primes := S.primes.push S.i
  i := S.i + 1
  hsize := by
    rw [mark_multiples_size]
    exact S.hsize
  hLlt := S.hLlt
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
    by_cases hndvd : ¬S.i.toInt ∣ j
    · rw [mark_multiples_unchanged_of_not_dvd] <;> try assumption
    rename' hndvd => hdvd; push_neg at hdvd
    have hSinn : 0 ≤ S.i := by
      apply Int32.le_iff_toInt_le.mpr
      exact le_of_lt (sieve_index_toInt_pos S)
    rw [mark_multiples_changed] <;> assumption
  hlti := by
    rw [sieve_toInt_index_succ]
    exact Int.add_lt_add S.hlti one_pos
  hile := by
    rw [sieve_toInt_index_succ]
    apply Int.add_one_le_of_lt
    rw [← Int.ofNat_inj.mpr S.hsize]
    convert Int.ofNat_lt_ofNat_of_lt ilt; symm; simp
    exact le_of_lt (sieve_index_toInt_pos S)
  hmarked := by
    intro j jpos jlt
    simp at jlt
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
      have hdvd : S.i.toInt ∣ (j : ℤ) := by
        contrapose! h
        rwa [mark_multiples_unchanged_of_not_dvd] <;> assumption
      exact ⟨S.i, Array.mem_push_self, hdvd⟩
  hprimesnn := by
    intro p pmem
    rcases Array.mem_or_eq_of_mem_push pmem with lhs | rfl
    · exact S.hprimesnn p lhs
    · exact Int32.le_of_lt (sieve_index_pos S)
  hpmem_iff := by
    intro p
    rw [sieve_toInt_index_succ]
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
          exact (hp' ▸ (Int.add_one_le_of_lt S.hlti))
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
        rw [getElem_congr_idx (congrArg Int.natAbs hp')]; simp
        apply sieve_marked_of_dvd_of_lt S m <;> try assumption
        rw [hp']
        exact Int.ofNat_lt_ofNat_of_lt mlt
    · intro ⟨ple, pprime⟩
      apply Int.le_of_lt_add_one at ple
      by_cases hpi : (p : ℤ) = S.i.toInt
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
    simp at jlt
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
    by_cases hdvd : ¬S.i.toInt ∣ j
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

-- Advance the loop which fills out the sieve, in the case where S.divs[i] ≠ 0
def advance_sieve_of_entry_ne_zero {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hinz : S.divs[S.i.toInt.natAbs]'ilt ≠ 0) : Sieve L where
  divs := S.divs
  primes := S.primes
  i := S.i + 1
  hsize := S.hsize
  hLlt := S.hLlt
  hdivsnn := S.hdivsnn
  hlti := by
    rw [sieve_toInt_index_succ]
    exact Int.add_lt_add S.hlti one_pos
  hile := by
    rw [sieve_toInt_index_succ]
    apply Int.add_one_le_of_lt
    convert Int.ofNat_lt_ofNat_of_lt ilt
    · exact (Int.ofNat_natAbs_of_nonneg (le_of_lt (sieve_index_toInt_pos S))).symm
    · exact S.hsize.symm
  hmarked := S.hmarked
  hprimesnn := S.hprimesnn
  hpmem_iff := by
    intro p
    rw [sieve_toInt_index_succ]
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
      rcases (S.hmarked S.i.toInt.natAbs (by rwa [← hpi]) ilt).mpr hinz with ⟨p', p'mem, p'dvd⟩
      rw [← hpi] at p'dvd; simp at p'dvd
      have p'nn : 0 ≤ p'.toInt :=
        Int32.le_iff_toInt_le.mp (S.hprimesnn p' p'mem)
      have hp'abs := Int.ofNat_natAbs_of_nonneg p'nn
      have : p'.toInt < S.i.toInt ∧ Nat.Prime p'.toInt.natAbs := by
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

@[simp] theorem advance_sieve_of_entry_eq_zero_size {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hiz : S.divs[S.i.toInt.natAbs]'ilt = 0) :
  (advance_sieve_of_entry_eq_zero S ilt hiz).divs.size = S.divs.size := by
  repeat rw [Sieve.hsize]

@[simp] theorem advance_sieve_of_entry_ne_zero_size {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hinz : S.divs[S.i.toInt.natAbs]'ilt ≠ 0) :
  (advance_sieve_of_entry_ne_zero S ilt hinz).divs.size = S.divs.size := by
  repeat rw [Sieve.hsize]

@[simp] theorem advance_sieve_of_entry_eq_zero_index {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hiz : S.divs[S.i.toInt.natAbs]'ilt = 0) :
  (advance_sieve_of_entry_eq_zero S ilt hiz).i = S.i + 1 := rfl

@[simp] theorem advance_sieve_of_entry_ne_zero_index {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size)
  (hinz : S.divs[S.i.toInt.natAbs]'ilt ≠ 0) :
  (advance_sieve_of_entry_ne_zero S ilt hinz).i = S.i + 1 := rfl

def sieve_of_eratosthenes_impl {L : ℕ} (S : Sieve L) : Sieve L :=
  if ilt : S.i.toInt.natAbs < S.divs.size then
  sieve_of_eratosthenes_impl (
    if hz : S.divs[S.i.toInt.natAbs]'ilt = 0
    then advance_sieve_of_entry_eq_zero S ilt hz
    else advance_sieve_of_entry_ne_zero S ilt hz
  ) else S
termination_by S.divs.size - S.i.toInt.natAbs
decreasing_by
  have ipos : 0 < S.i := sieve_index_pos S
  have inn : 0 ≤ S.i := Int32.le_of_lt ipos
  rw [lt_sieve_length_iff_of_nonneg S _ inn] at ilt
  split_ifs with h
  · repeat rw [Sieve.hsize]
    rw [advance_sieve_of_entry_eq_zero_index]
    apply termination_by_increasing_int32
    · assumption
    · simp
    · assumption
    · exact lt_trans S.hlti ilt
    · exact le_of_lt S.hLlt
  · repeat rw [Sieve.hsize]
    rw [advance_sieve_of_entry_ne_zero_index]
    apply termination_by_increasing_int32
    · assumption
    · simp
    · assumption
    · exact lt_trans S.hlti ilt
    · exact le_of_lt S.hLlt

theorem sieve_of_eratosthenes_impl_index {L : ℕ} (S : Sieve L) :
  (sieve_of_eratosthenes_impl S).i.toInt = L := by
  unfold sieve_of_eratosthenes_impl
  have ipos := sieve_index_pos S
  have inn := le_of_lt (sieve_index_toInt_pos S)
  have hrw := lt_sieve_length_iff_of_nonneg S S.i (Int32.le_of_lt ipos)
  split_ifs with h₀ h₁ <;> try rw [hrw] at h₀
  · rw [sieve_of_eratosthenes_impl_index]
  · rw [sieve_of_eratosthenes_impl_index]
  · push_neg at h₀
    exact Int.le_antisymm S.hile h₀
termination_by S.divs.size - S.i.toInt.natAbs
decreasing_by
  · rw [advance_sieve_of_entry_eq_zero_size]
    rw [advance_sieve_of_entry_eq_zero_index]
    rw [hrw, ← Int.ofNat_inj.mpr S.hsize] at h₀
    apply termination_by_increasing_int32
    · assumption
    · simp
    · assumption
    · exact lt_trans S.hlti h₀
    · rw [S.hsize]
      exact le_of_lt S.hLlt
  · rw [advance_sieve_of_entry_ne_zero_size]
    rw [advance_sieve_of_entry_ne_zero_index]
    rw [hrw, ← Int.ofNat_inj.mpr S.hsize] at h₀
    apply termination_by_increasing_int32
    · assumption
    · simp
    · assumption
    · exact lt_trans S.hlti h₀
    · rw [S.hsize]
      exact le_of_lt S.hLlt

def sieve_of_eratosthenes : Sieve SIEVE_SIZE :=
  sieve_of_eratosthenes_impl init_sieve

def primes : Array Int32 := sieve_of_eratosthenes.primes
def divs : Array Int32 := sieve_of_eratosthenes.divs

theorem sieve_of_eratosthenes_index :
  sieve_of_eratosthenes.i.toInt = SIEVE_SIZE := by
  exact sieve_of_eratosthenes_impl_index _

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

-- All elements of 'primes' are less than SIEVE_SIZE
theorem lt_of_mem_primes :
  ∀ n ∈ primes, n.toInt < SIEVE_SIZE := by
  intro n nmem
  unfold primes at nmem
  let S := sieve_of_eratosthenes
  have nnn : 0 ≤ n.toInt := Int32.le_iff_toInt_le.mp (S.hprimesnn n nmem)
  have habs := Int.ofNat_natAbs_of_nonneg nnn
  rw [← habs]
  apply Int.lt_of_lt_of_le _ S.hile
  apply ((S.hpmem_iff n.toInt.natAbs).mp _).1
  rw [habs]
  exact Array.mem_map_of_mem nmem

-- All primes less than 'SIEVE_SIZE' are in 'primes'
theorem mem_primes_of_prime_of_lt (p : ℕ) (hprime : Nat.Prime p) (plt : p < SIEVE_SIZE) :
  ∃ n ∈ primes, n.toInt = p := by
  let S := sieve_of_eratosthenes
  apply Int.ofNat_lt_ofNat_of_lt at plt
  rw [← sieve_of_eratosthenes_index] at plt
  exact Array.exists_of_mem_map ((S.hpmem_iff _).mpr ⟨plt, hprime⟩)

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
  rw [sieve_of_eratosthenes_index, ← S.hsize]
  exact Int.ofNat_lt_ofNat_of_lt nlt

end CodeChef
