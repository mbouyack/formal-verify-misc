import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import FormalVerifyMisc.Int32.Basic
import FormalVerifyMisc.Loops

namespace CodeChef

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

-- Prevent '2^31' from having to be written as '2 ^ 31'
set_option linter.style.commandStart false
set_option linter.flexible false

def SIEVE_SIZE : ℕ := 1000001
def SIEVE_SIZE_32 : Int32 := 1000001

@[simp] theorem sieve_size_32_toInt : SIEVE_SIZE_32.toInt = SIEVE_SIZE := rfl

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
  -- The number of elements in 'primes' is less than 'i'
  hprimessize : primes.size < i.toInt
  -- The elements in 'primes' are strictly increasing
  hprimesinc : ∀ m n, (mlt : m < n) → (nlt : n < primes.size) →
    primes[m]'(lt_trans mlt nlt) < primes[n]

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
  hprimessize := by simp
  hprimesinc := by simp

theorem init_sieve_size : init_sieve.divs.size = SIEVE_SIZE :=
  Array.size_replicate

-- The state and constraints required for the 'mark_multiples' loop
@[ext] structure MarkMultiplesState where
  A : Array Int32
  inc : Int32
  cur : Int32
  incdvd : inc.toInt ∣ cur.toInt
  curpos : 0 < cur.toInt
  incpos : 0 < inc.toInt
  incle : inc.toInt ≤ A.size
  hAslt : A.size < 2^30

-- For performance reasons we can't pass the sieve itself into 'mark_multiples'
-- Use this structure to easily repackage and pass the relevant theorems
structure MMSArgs (L : ℕ) where
  i : Int32
  hlti : 1 < i.toInt
  hile : i.toInt ≤ L
  hLlt : L < 2^30

def mms_args_of_sieve {L : ℕ} (S : Sieve L) : MMSArgs L where
  i := S.i
  hlti := S.hlti
  hile := S.hile
  hLlt := S.hLlt

def mark_multiples_state_of_sieve {L : ℕ} (A : Array Int32)
  (hsize : A.size = L) (args : MMSArgs L)  : MarkMultiplesState where
  inc := args.i
  cur := args.i
  A := A
  incdvd := by simp
  curpos := by linarith [args.hlti]
  incpos := by linarith [args.hlti]
  incle := le_of_le_of_eq args.hile (Int.ofNat_inj.mpr hsize).symm
  hAslt := by rw [hsize]; exact args.hLlt

@[simp] theorem mark_multiples_state_of_sieve_size {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)).A.size = S.divs.size := rfl

@[simp] theorem mark_multiples_state_of_sieve_inc {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)).inc = S.i := rfl

@[simp] theorem mark_multiples_state_of_sieve_cur {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)).cur = S.i := rfl

@[simp] theorem mark_multiples_state_of_sieve_array {L : ℕ} (S : Sieve L) :
  (mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)).A = S.divs := rfl

theorem mark_multiples_state_size_pos (MMS : MarkMultiplesState) : 0 < MMS.A.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  exact lt_of_lt_of_le MMS.incpos MMS.incle

/- When adding 'inc' to 'cur' we can move the addition across the 'toInt' conversion

  Note: We would like to use 'simple_loop_state_toInt_cur_add_inc' instead, but we
  can only use that once we prove 'MarkMultiplesState' is a 'SimpleLoopState', but
  we need this result in order to prove that.
-/
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
  incle := by
    split_ifs with h
    · exact MMS.incle
    · convert MMS.incle using 1; simp
  hAslt := by
    convert MMS.hAslt using 1
    split_ifs with h
    · rfl
    · simp

-- The size of the MarkMultiplesState doesn't change upon advancing
@[simp] theorem mark_multiples_advance_size (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).A.size = MMS.A.size := by
  unfold mark_multiples_advance; dsimp
  split_ifs with h <;> simp

@[simp] theorem mark_multiples_advance_inc (MMS : MarkMultiplesState)
  (curlt : MMS.cur.toInt.natAbs < MMS.A.size) :
  (mark_multiples_advance MMS curlt).inc = MMS.inc := rfl

-- Useful lemma for converting between two different statements
-- of the bounds check
lemma int32_lt_ofNat_iff_toInt_natAbs_lt {a : Int32} {n : ℕ}
  (hnn : 0 ≤ a.toInt) (hlt : n < 2^31) :
  a < Int32.ofNat n ↔ a.toInt.natAbs < n := by
  rw [← Int.ofNat_lt, Int32.lt_iff_toInt_lt]
  rw [Int32.toInt_ofNat_of_lt hlt]
  rw [Int.ofNat_natAbs_of_nonneg hnn]

-- The SimpleLoopState needs the upper bound of the loop stated as an Int32
-- while the MarkMultipleState has it as a natural number. This lemma
-- allows us to convert between the two
lemma mark_multiples_state_size_ofNat_toInt (MMS : MarkMultiplesState) :
  (Int32.ofNat MMS.A.size).toInt = MMS.A.size :=
  Int32.toInt_ofNat_of_lt (lt_trans MMS.hAslt (by simp))

-- Adapt 'int32_lt_ofNat_iff_toInt_natAbs_lt' for MarkMultiplesState
lemma mark_multiples_state_cur_lt_size_iff (MMS : MarkMultiplesState) :
  MMS.cur < Int32.ofNat MMS.A.size ↔ MMS.cur.toInt.natAbs < MMS.A.size :=
  int32_lt_ofNat_iff_toInt_natAbs_lt (le_of_lt MMS.curpos) (lt_trans MMS.hAslt (by simp))

instance : SimpleLoopState MarkMultiplesState where
  cur := MarkMultiplesState.cur
  inc := MarkMultiplesState.inc
  finish := fun mms ↦ Int32.ofNat mms.A.size
  adv := fun mms hlt ↦ mark_multiples_advance mms
    ((mark_multiples_state_cur_lt_size_iff mms).mp hlt)
  hpos :=
    fun mms ↦ Int32.lt_iff_toInt_lt.mpr (Int32.toInt_zero ▸ mms.incpos)
  hsafe := by
    intro mms
    apply le_trans (Int.add_le_add_left mms.incle _)
    rw [mark_multiples_state_size_ofNat_toInt]
    have hle := Int.le_sub_one_of_lt (Int.ofNat_lt_ofNat_of_lt mms.hAslt)
    apply le_trans (Int.add_le_add hle hle)
    unfold Int32.maxValue; simp
  hadv := fun _ _ ↦ rfl
  hinc := fun _ _ ↦ rfl
  hfinish := by
    intro mms hlt; congr 1
    simp

@[simp] theorem mark_multiples_state_sls_cur (MMS : MarkMultiplesState) :
  SimpleLoopState.cur MMS = MMS.cur := rfl

@[simp] theorem mark_multiples_state_sls_inc (MMS : MarkMultiplesState) :
  SimpleLoopState.inc MMS = MMS.inc := rfl

@[simp] theorem mark_multiples_state_sls_finish (MMS : MarkMultiplesState) :
  SimpleLoopState.finish MMS = Int32.ofNat MMS.A.size := rfl

@[simp] theorem mark_multiples_state_sls_adv (MMS : MarkMultiplesState) :
  SimpleLoopState.adv MMS = fun hlt ↦
  mark_multiples_advance MMS (by
    simp at hlt
    exact ((mark_multiples_state_cur_lt_size_iff MMS).mp hlt)
  ) := rfl

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

/- Mark every entry of 'A' which is a multiple of args.i

   Originally this function took a Sieve as an argument, but because it isn't
   given exclusive ownership of that Sieve, the entire array was being copied.
   This change substantially improves the performance of the algorithm at the
   cost of slightly more verbose code.
-/
def mark_multiples {L : ℕ} (A : Array Int32)
  (hsize : A.size = L) (args : MMSArgs L) : MarkMultiplesState :=
  do_simple_loop (mark_multiples_state_of_sieve A hsize args)

-- The size of the marked array is the same as the size of the sieve
@[simp] theorem mark_multiples_size {L : ℕ} (S : Sieve L) :
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A.size = S.divs.size := by
  unfold mark_multiples
  rw [← mark_multiples_state_of_sieve_size S]
  apply simple_loop_val_const (_ : MarkMultiplesState) (fun mms ↦ mms.A.size)
  intro mms hlt
  apply mark_multiples_advance_size mms

-- The increment of the marked array is the same as S.i
@[simp] theorem mark_multiples_inc {L : ℕ} (S : Sieve L) :
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).inc = S.i :=
  @simple_loop_inc_const MarkMultiplesState _ _

-- Prove the equivalence between cur < finish in the SimpleLoopState interface
-- and the corresponding statement in MarkMultiplesState
lemma mark_multiples_cur_lt_size_iff_cur_lt_finish (MMS : MarkMultiplesState) :
  MMS.cur.toInt.natAbs < MMS.A.size ↔ SimpleLoopState.cur MMS < SimpleLoopState.finish MMS := by
  rw [← mark_multiples_state_cur_lt_size_iff MMS]; simp

-- 'mark_multiples' has no effect on entries in the sieve
-- that were previous marked
theorem mark_multiples_unchanged_of_marked {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.divs[j] ≠ 0 →
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A[j]'(by
    rwa [mark_multiples_size]) = S.divs[j] := by
  unfold mark_multiples
  intro j jpos jlt hnz
  let mms₀ := mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)
  let prop (mms : MarkMultiplesState) : Prop :=
    (_ : j < mms.A.size) → mms.A[j] ≠ 0 ∧ mms.A[j] = S.divs[j]
  have base : prop mms₀ := by
    unfold prop mms₀
    intro; simpa
  have step : ∀ t curlt,
    prop t → prop (SimpleLoopState.adv t curlt) := by
    unfold prop
    intro t curlt h jlt'; simp
    rw [← mark_multiples_cur_lt_size_iff_cur_lt_finish] at curlt
    simp at jlt'
    obtain ⟨hnz', h⟩ := h jlt'
    rw [mark_multiples_advance_unchanged_of_marked t curlt j jpos jlt' hnz']
    exact ⟨hnz', h⟩
  exact (simple_loop_prop_const mms₀ prop base step _).2

-- 'mark_multiples' has no effect on entries in the sieve
-- whose indices are not divisible by 'inc'
theorem mark_multiples_unchanged_of_not_dvd {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → ¬S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A[j]'(by
    rwa [mark_multiples_size]) = S.divs[j] := by
  intro j jpos jlt hdvd
  let mms₀ := mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)
  let prop (mms : MarkMultiplesState) : Prop :=
    (_ : j < mms.A.size) → ¬mms.inc.toInt ∣ j ∧ mms.A[j] = S.divs[j]
  have base : prop mms₀ := by
    unfold prop mms₀
    intro; simpa
  have step : ∀ t curlt,
    prop t → prop (SimpleLoopState.adv t curlt) := by
    unfold prop
    intro t curlt h jlt'; simp
    rw [← mark_multiples_cur_lt_size_iff_cur_lt_finish] at curlt
    simp at jlt'
    obtain ⟨hdvd', h⟩ := h jlt'
    rw [mark_multiples_advance_unchanged_of_not_dvd t curlt j jpos jlt' hdvd']
    exact ⟨hdvd', h⟩
  exact (simple_loop_prop_const mms₀ prop base step _).2

-- 'mark_multiples' has no effect on the first entry in the sieve
theorem mark_multiples_unchanged_of_first {L : ℕ} (S : Sieve L) :
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A[0]'(
    (mark_multiples_size S) ▸ (sieve_length_pos S)
  ) = S.divs[0]'(sieve_length_pos S) := by
  let mms₀ := mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)
  let prop (mms : MarkMultiplesState) : Prop :=
    mms.A[0]'(mark_multiples_state_size_pos mms) = S.divs[0]'(sieve_length_pos S)
  have base : prop mms₀ := by
    unfold prop mms₀; simp
  have step : ∀ t curlt,
    prop t → prop (SimpleLoopState.adv t curlt) := by
    unfold prop
    intro t curlt h; simp
    rw [← mark_multiples_cur_lt_size_iff_cur_lt_finish] at curlt
    rwa [mark_multiples_advance_unchanged_of_first t curlt]
  exact simple_loop_prop_const mms₀ prop base step

-- Any entry that was zero and has index divisible by 'inc' will be
-- set to 'inc' by mark_multiples
theorem mark_multiples_changed {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) →
  S.divs[j] = 0 → S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A[j]'(by
    rwa [mark_multiples_size]) = S.i := by
  intro j jpos _ hz hdvd
  let mms₀ := mark_multiples_state_of_sieve
    S.divs S.hsize (mms_args_of_sieve S)
  let prop (mms : MarkMultiplesState) : Prop :=
    (_ : j < mms.A.size) → mms.inc.toInt = S.i.toInt →
    (mms.cur.toInt ≤ j → mms.A[j] = 0) ∧
    (j < mms.cur.toInt → mms.A[j] = mms.inc)
  have base : prop mms₀ := by
    unfold prop mms₀; simp
    intro _
    apply And.intro (fun _ ↦ hz)
    intro jlt
    have lej := Int.le_of_dvd (Int.ofNat_lt_ofNat_of_lt jpos) hdvd
    exact False.elim (Int.not_lt_of_ge lej jlt)
  have step : ∀ t curlt,
    prop t → prop (SimpleLoopState.adv t curlt) := by
    unfold prop
    intro t curlt h jlt hinc
    simp; simp at jlt hinc
    rw [← mark_multiples_cur_lt_size_iff_cur_lt_finish] at curlt
    constructor
    · intro hlej
      have ltj : t.cur.toInt < j := by linarith [t.incpos, hlej]
      have curnej : t.cur.toInt ≠ j := ne_of_lt ltj
      rw [mark_multiples_advance_unchanged_of_not_cur t curlt j jpos jlt curnej]
      exact (h jlt hinc).1 (le_of_lt ltj)
    · intro jlt'
      by_cases curj : t.cur.toInt = j
      · have curj' :=
          Int.ofNat_inj.mp (Eq.trans (Int.ofNat_natAbs_of_nonneg (le_of_lt t.curpos)) curj)
        subst curj'
        apply mark_multiples_advance_changed
        exact (h jlt hinc).1 (le_of_eq curj)
      rw [← hinc] at hdvd
      rw [mark_multiples_advance_unchanged_of_not_cur t curlt j jpos jlt curj]
      push_neg at curj
      apply (h jlt hinc).2 (lt_of_le_of_ne _ curj.symm)
      -- Rewrite everything as multiples of 'inc' to prove the final inequality
      rcases t.incdvd with ⟨ki, hki⟩
      rcases hdvd with ⟨kj, hkj⟩
      rw [hki, hkj] at jlt'
      nth_rw 3 [← mul_one t.inc.toInt] at jlt'
      rw [← mul_add, Int.mul_lt_mul_left t.incpos] at jlt'
      rw [hki, hkj]
      rw [Int.mul_le_mul_left t.incpos]
      exact Int.le_of_lt_add_one jlt'
  rw [← mark_multiples_inc]
  have := simple_loop_prop_const mms₀ prop base step
  apply (this _ (Int32.toInt_inj.mpr (mark_multiples_inc S))).2 _
  -- The final step is to prove that j < cur so the
  -- right-hand side of the property is applicable
  rename j < S.divs.size => jlt
  apply lt_of_lt_of_le (Int.ofNat_lt_ofNat_of_lt jlt)
  have lecur := Int32.le_iff_toInt_le.mp (simple_loop_index_ge mms₀)
  rw [mark_multiples_state_sls_finish] at lecur
  rw [mark_multiples_state_size_ofNat_toInt] at lecur
  exact lecur

-- Any entry whose index is divisible by 'inc' will be marked
-- after calling mark_multiples
theorem mark_multiples_marked_of_dvd {L : ℕ} (S : Sieve L) :
  ∀ (j : ℕ), (jpos : 0 < j) → (jlt : j < S.divs.size) → S.i.toInt ∣ (j : ℤ) →
  (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A[j]'(by
    rwa [mark_multiples_size]) ≠ 0 := by
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
  divs := (mark_multiples S.divs S.hsize (mms_args_of_sieve S)).A
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
  hprimessize := by
    rw [sieve_toInt_index_succ, Array.size_push]
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
  hprimessize := by
    rw [sieve_toInt_index_succ]
    apply lt_trans _ (Int.add_lt_add_right S.hprimessize 1)
    simp
  hprimesinc := S.hprimesinc

-- Combine the two cases into a single advancement function
def advance_sieve {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size) : Sieve L :=
  if hz : S.divs[S.i.toInt.natAbs]'ilt = 0
  then advance_sieve_of_entry_eq_zero S ilt hz
  else advance_sieve_of_entry_ne_zero S ilt hz

@[simp] theorem advance_sieve_size {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size) :
  (advance_sieve S ilt).divs.size = S.divs.size := by
  repeat rw [Sieve.hsize]

@[simp] theorem advance_sieve_index {L : ℕ} (S : Sieve L)
  (ilt : S.i.toInt.natAbs < S.divs.size) :
  (advance_sieve S ilt).i = S.i + 1 := by
  unfold advance_sieve
  split_ifs <;> rfl

-- Adapt 'int32_lt_ofNat_iff_toInt_natAbs_lt' for Sieve
lemma sieve_index_lt_size_iff {L : ℕ} (S : Sieve L) :
  S.i < Int32.ofNat S.divs.size ↔ S.i.toInt.natAbs < S.divs.size :=
  int32_lt_ofNat_iff_toInt_natAbs_lt
    (by linarith [S.hlti])
    (by rw [S.hsize]; exact lt_trans S.hLlt (by simp))

-- Prove that 'Sieve' implements a simple loop
instance (L : ℕ) : SimpleLoopState (Sieve L) where
  cur := Sieve.i
  inc := fun _ ↦ 1
  finish := fun S ↦ Int32.ofNat S.divs.size
  adv := fun S ilt ↦ advance_sieve S (by rwa [← sieve_index_lt_size_iff S])
  hpos := fun _ ↦ by simp
  hsafe := by
    intro S
    unfold Int32.maxValue
    rw [S.hsize]
    rw [Int32.toInt_ofNat_of_lt (lt_trans S.hLlt (by simp))]; simp
    apply Int.add_one_le_of_lt
    exact lt_trans (Int.ofNat_lt_ofNat_of_lt S.hLlt) (by simp)
  hadv := fun S ilt ↦ advance_sieve_index _ _
  hinc := fun _ _ ↦ rfl
  hfinish := by simp

@[simp] theorem sieve_loop_cur {L : ℕ} (S : Sieve L) :
  SimpleLoopState.cur S = S.i := rfl

@[simp] theorem sieve_loop_inc {L : ℕ} (S : Sieve L) :
  SimpleLoopState.inc S = 1 := rfl

@[simp] theorem sieve_loop_finish {L : ℕ} (S : Sieve L) :
  SimpleLoopState.finish S = Int32.ofNat S.divs.size := rfl

@[simp] theorem sieve_loop_adv {L : ℕ} (S : Sieve L) :
  SimpleLoopState.adv S = fun hlt ↦
    advance_sieve S (by rwa [← sieve_index_lt_size_iff S]) := rfl

def sieve_of_eratosthenes : Sieve SIEVE_SIZE :=
  do_simple_loop init_sieve

def primes : Array Int32 := sieve_of_eratosthenes.primes
def divs : Array Int32 := sieve_of_eratosthenes.divs

-- Prove that the value of Sieve.i is at least SIEVE_SIZE
-- after loop execution is complete
theorem sieve_of_eratosthenes_index_ge :
  SIEVE_SIZE ≤ sieve_of_eratosthenes.i.toInt := by
  have := simple_loop_index_ge init_sieve
  simp at this
  apply Int32.le_iff_toInt_le.mp at this
  rwa [Sieve.hsize, Int32.toInt_ofNat_of_lt] at this
  unfold SIEVE_SIZE; simp

theorem sieve_of_eratosthenes_index :
  sieve_of_eratosthenes.i.toInt = SIEVE_SIZE := by
  have curlt : SimpleLoopState.cur init_sieve < SimpleLoopState.finish init_sieve := by
    unfold init_sieve SIEVE_SIZE; simp
  apply le_antisymm _ sieve_of_eratosthenes_index_ge
  apply Int.le_of_lt_add_one
  apply lt_of_lt_of_eq (Int32.lt_iff_toInt_lt.mp (simple_loop_index_lt_of_lt init_sieve curlt))
  rw [simple_loop_state_toInt_finish_add_inc]
  rw [simple_loop_finish_const, simple_loop_inc_const]; dsimp
  rw [Int.add_left_inj, init_sieve_size]
  apply Int32.toInt_ofNat_of_lt
  unfold SIEVE_SIZE; simp

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
  replace plt := lt_of_lt_of_le plt sieve_of_eratosthenes_index_ge
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
  apply lt_of_lt_of_le (Int.ofNat_lt_ofNat_of_lt _) sieve_of_eratosthenes_index_ge
  rwa [← S.hsize]

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
  apply Int32.toInt_inj.mp; simp
  rw [hp]
  apply Int.ofNat_inj.mpr
  -- Prove primes.back is at least 999983
  have lep : 999983 ≤ p := by
    apply Int.le_of_ofNat_le_ofNat
    rw [← hp]; simp
    -- Prove that 999983 is in the list and let 'i' be its location
    have hprime : Nat.Prime 999983 := by norm_num
    rcases mem_primes_of_prime_of_lt _
      hprime (by unfold SIEVE_SIZE; simp) with ⟨n, nprime, neq⟩
    rcases Array.getElem_of_mem nprime with ⟨i, ilt, hpin⟩
    rw [← Int32.toInt_inj, neq] at hpin; simp at hpin
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
  exact sieve_of_eratosthenes_index

end CodeChef
