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
  -- The next prime to be added to the sieve
  p : Int32
  -- The size of 'divs' is given by 'L'
  hsize : divs.size = L
  -- The length of the sieve has an upper bound
  -- This is required to avoid exceeding Int32.maxValue
  hLlt : L < 2^30
  -- The entries in the sieve are non-negative
  hdivsnn : ∀ x ∈ divs, 0 ≤ x
  -- The values in 'primes' are all positive
  hprimespos : ∀ q ∈ primes, 0 < q
  -- 'p' is positive
  hppos : 0 < p
  -- 'p' is less than 'L' - the size of the sieve
  hplt : p.toInt < (L : ℤ)
  -- The absolute value of 'p' is prime
  hpprime : Nat.Prime p.toInt.natAbs
  -- Any prime less than 'p' is already in 'primes'
  hpnext : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt primes)
  -- For every value 'q' in 'primes', every multiple of 'q' is marked in 'divs'
  hmarked : ∀ q ∈ primes, ∀ i, (0 < i) → (ilt : i < divs.size) →
    q.toInt ∣ (i : ℤ) → divs[i] ≠ 0
  -- A natural number is in 'primes' if-and-only-if it is a prime
  -- less than or equal to the last value in 'primes'
  hpmem_iff : (hnnil : primes ≠ #[]) → ∀ q : ℕ,
    ((q : ℤ) ∈ (Array.map Int32.toInt primes) ↔
     (q : ℤ) ≤ (primes.back (Array.size_pos_iff.mpr hnnil)).toInt ∧ Nat.Prime q)
  -- If an entry in the sieve is non-zero, its value corresponds to the smallest
  -- divisor of its index greater than 1
  hdivs_dvd : ∀ i, (ilt : i < divs.size) → divs[i]'(ilt) ≠ 0 →
    (divs[i]'(ilt)).toInt ∣ i ∧
    ∀ y, 1 < y → y ∣ i → (divs[i]'(ilt)).toInt ≤ (y : ℤ)

-- Construct a sieve with all elements set to zero
def init_sieve : Sieve SIEVE_SIZE where
  divs := Array.replicate SIEVE_SIZE 0
  primes := #[]
  p := 2
  hsize := Array.size_replicate
  hLlt := by
    unfold SIEVE_SIZE;
    simp
  hdivsnn := by
    intro x xmem
    rw [(Array.mem_replicate.mp xmem).2]; rfl
  hprimespos :=
    fun _ hmem ↦ False.elim (Array.not_mem_empty _ hmem)
  hppos := rfl
  hplt := by
    unfold SIEVE_SIZE
    simp
  hpprime := by
    simp; norm_num
  hpnext := by
    intro q qprime qlt
    absurd qlt; simp
    exact Nat.Prime.two_le qprime
  hmarked := by
    intro _ pmem
    exact False.elim (Array.not_mem_empty _ pmem)
  hpmem_iff := fun h ↦ False.elim (h rfl)
  hdivs_dvd := by
    intro i ilt hnz
    constructor
    · absurd hnz; simp
    · intro y lty ydvd; simp

-- Update the sieve to indicate that 'p' is the smallest divisor of 'n'
def mark_sieve {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) : Sieve L where
  divs := if S.divs[n.toInt.natAbs] ≠ 0 then S.divs
    else S.divs.set n.toInt.natAbs S.p nlt
  primes := S.primes
  p := S.p
  hsize := by
    split_ifs with h
    · exact S.hsize
    · rw [Array.size_set nlt]
      exact S.hsize
  hLlt := S.hLlt
  hdivsnn := by
    intro x
    split_ifs with h
    · intro xmem
      exact S.hdivsnn x xmem
    · intro xmem
      rcases Array.mem_or_eq_of_mem_set xmem with lhs | rhs
      · exact S.hdivsnn x lhs
      · rw [rhs]
        exact Int32.le_of_lt S.hppos
  hprimespos := S.hprimespos
  hppos := S.hppos
  hplt := S.hplt
  hpprime := S.hpprime
  hpnext := S.hpnext
  hmarked := by
    intro q qmem i ipos
    split_ifs with h
    · intro ilt qdvd
      exact S.hmarked q qmem i ipos ilt qdvd
    · intro ilt qdvd
      rw [Array.getElem_set nlt ilt]
      split_ifs with h'
      · intro h
        absurd S.hppos
        rw [h]; simp
      · rw [Array.size_set nlt] at ilt
        exact S.hmarked q qmem i ipos ilt qdvd
  hpmem_iff := S.hpmem_iff
  hdivs_dvd := by
    intro i
    split_ifs with h
    · intro ilt hinz
      exact S.hdivs_dvd i ilt hinz
    · intro ilt hinz
      rw [Array.getElem_set nlt ilt] at *
      split_ifs with h'
      · subst h'
        use Int.dvd_natAbs.mpr hdvd
        intro y lty ydvd
        /- By contradiction:
          Suppose y < p. Since 1 < y, there exists a prime 'q' such that q ∣ y
          but because y ∣ n, q ∣ n. By 'hnextp' we can conclude that q ∈ S.primes
          Then by 'S.hmarked', because q ∈ S.primes and q ∣ n, S.divs[n] ≠ 0
          which is a contradiction
        -/
        contrapose! h
        rcases Nat.exists_prime_and_dvd (Nat.ne_of_lt lty).symm with ⟨q, qprime, qdvdy⟩
        have qdvdn : q ∣ n.toInt.natAbs := Nat.dvd_trans qdvdy ydvd
        have nabspos : 0 < n.toInt.natAbs := by
          apply Int.natAbs_pos.mpr
          apply int32_toInt_ne_zero_of_ne_zero
          exact (Int32.ne_of_lt hnpos).symm
        have qley : q ≤ y := Nat.le_of_dvd (lt_trans (by norm_num) lty) qdvdy
        have qmem := S.hpnext q qprime (lt_of_le_of_lt (Int.ofNat_le_ofNat_of_le qley) h)
        rcases Array.exists_of_mem_map qmem with ⟨m, mmem, hmq⟩
        apply S.hmarked m mmem _ nabspos nlt
        rw [hmq]
        exact Int.ofNat_dvd.mpr qdvdn
      · rw [if_neg h'] at hinz
        rw [Array.size_set nlt] at ilt
        exact S.hdivs_dvd i ilt hinz

@[simp] theorem mark_sieve_divs_size {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_sieve S n hnpos nlt hdvd).divs.size = S.divs.size := by
  rw [Sieve.hsize, Sieve.hsize]

@[simp] theorem mark_sieve_primes {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_sieve S n hnpos nlt hdvd).primes = S.primes := rfl

@[simp] theorem mark_sieve_next_prime {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_sieve S n hnpos nlt hdvd).p = S.p := rfl

-- Every cell marked in 'S' is also marked in 'mark_sieve S'
theorem mark_sieve_marked_of_marked {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) :
  ∀ i, (ilt : i < S.divs.size) → S.divs[i]'ilt ≠ 0 →
  (mark_sieve S n hnpos nlt hdvd).divs[i]'(by simpa) ≠ 0 := by
  intro i ilt hmark
  unfold mark_sieve; simp
  split_ifs with h
  · have hnnein : n.toInt.natAbs ≠ i := by
      contrapose! hmark
      subst hmark
      assumption
    rw [Array.getElem_set_ne] <;> assumption
  · exact hmark

-- The given index is non-zero after calling 'mark_sieve'
theorem mark_sieve_index_marked {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_sieve S n hnpos nlt hdvd).divs[n.toInt.natAbs]'(by simpa) ≠ 0 := by
  unfold mark_sieve; dsimp
  split_ifs with h
  · rw [Array.getElem_set]; simp
    intro hpz
    absurd S.hppos
    rw [hpz]; simp
  · assumption

lemma int32_toInt_lt_of_lt_divs_size {L : ℕ} (S : Sieve L) (n : Int32)
  (hnlt : n.toInt.natAbs < S.divs.size) : n.toInt < 2^30 := by
  by_cases h : n.toInt ≤ 0
  · apply lt_of_le_of_lt h (by simp)
  push_neg at h
  apply Int.ofNat_lt.mpr at hnlt
  rw [Int.natAbs_of_nonneg (le_of_lt h), S.hsize] at hnlt
  exact lt_trans hnlt (Int.ofNat_lt_ofNat_of_lt S.hLlt)

-- We'll need this result below for "mark_multiples"
lemma int32_toInt_add_of_pos_of_dvd_of_lt (m n : Int32)
  (hmpos : 0 < m) (hnpos : 0 < n)
  (hdvd : m.toInt ∣ n.toInt) (hnlt : n.toInt < 2^30) :
  (m + n).toInt = m.toInt + n.toInt := by
  have hmpos' := int32_toInt_pos_of_pos hmpos
  have hnpos' := int32_toInt_pos_of_pos hnpos
  apply int32_toInt_add_of_bounds
  constructor
  · apply le_of_lt
    exact lt_trans (by simp) (Int.add_lt_add hmpos' hnpos')
  · rw [add_comm]
    apply lt_of_le_of_lt (Int.add_le_add_left (Int.le_of_dvd hnpos' hdvd) n.toInt)
    rw [← two_mul, Int.pow_succ, mul_comm]
    exact (Int.mul_lt_mul_right (two_pos)).mpr hnlt

-- Useful alternate upper bound on 'n'
lemma sieve_idx_lt_divs_size
  {L : ℕ} (S : Sieve L) (n : Int32)
  (hnnn : 0 ≤ n) (hnlt : n.toInt < (L : ℤ)) :
  n.toInt.natAbs < S.divs.size := by
  apply Int.lt_of_ofNat_lt_ofNat
  rw [S.hsize]
  convert hnlt
  have hnnn' := Int32.le_iff_toInt_le.mp hnnn
  exact Int.ofNat_natAbs_of_nonneg hnnn'

-- General strategy for proving termination when iterating over the sieve
lemma sieve_termination {L : ℕ} (S : Sieve L) (n m : Int32)
  (hnpos : 0 < n) (hmpos : 0 < m)
  (hnlt : n.toInt.natAbs < S.divs.size) (hmle : m ≤ n) :
  S.divs.size - (n + m).toInt.natAbs < S.divs.size - n.toInt.natAbs := by
  have hnpos' : 0 < n.toInt := int32_toInt_pos_of_pos hnpos
  have hmpos' : 0 < m.toInt := int32_toInt_pos_of_pos hmpos
  have hnub : n.toInt < 2 ^ 30 := int32_toInt_lt_of_lt_divs_size S n hnlt
  have hmub : m.toInt < 2 ^ 30 :=
    lt_of_le_of_lt (Int32.le_iff_toInt_le.mp hmle) hnub
  have hnm : (n + m).toInt = n.toInt + m.toInt := by
    rw [int32_toInt_add_of_bounds]
    constructor
    · exact le_trans (by simp) (le_of_lt (Int.add_lt_add hnpos' hmpos'))
    · exact Int.add_lt_add hnub hmub
  rw [hnm]
  apply Nat.sub_lt_sub_left hnlt
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hnpos')
  exact Int.lt_add_of_pos_right _ hmpos'

-- Prove the termination requirements for 'mark_multiple'
lemma mark_multiple_termination {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt)
  (hnlt : n.toInt.natAbs < S.divs.size) :
  S.divs.size - (n + S.p).toInt.natAbs < S.divs.size - n.toInt.natAbs := by
  have hnpos' := int32_toInt_pos_of_pos hnpos
  apply sieve_termination S _ _ hnpos S.hppos hnlt
  exact Int32.le_iff_toInt_le.mpr (Int.le_of_dvd hnpos' hdvd)

-- Mark one multiple of 'p' in sieve 'S'
def mark_multiple {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt) : Sieve L :=
  if hnlt : n.toInt.natAbs < S.divs.size then
  (fun (hnp : (n + S.p).toInt = n.toInt + S.p.toInt) ↦
    mark_multiple
      (mark_sieve S n hnpos hnlt hdvd)
      (n + S.p) (by
        apply Int32.lt_iff_toInt_lt.mpr
        rw [hnp]
        apply Int.add_pos (Int32.lt_iff_toInt_lt.mp hnpos)
        exact Int32.lt_iff_toInt_lt.mp S.hppos
      ) (by
        rw [hnp]
        exact Int.dvd_add hdvd (by use 1; simp)
      ))
  (by
    have hppos' := int32_toInt_pos_of_pos S.hppos
    have hnpos' := int32_toInt_pos_of_pos hnpos
    rw [Int.add_comm, Int32.add_comm]
    apply int32_toInt_add_of_pos_of_dvd_of_lt S.p n S.hppos hnpos hdvd
    exact int32_toInt_lt_of_lt_divs_size S _ hnlt
  ) else S
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Mark all multiples of the next prime, 'p', in the Sieve
def mark_multiples {L : ℕ} (S : Sieve L) : Sieve L :=
  mark_multiple S S.p S.hppos (by use 1; simp)

@[simp] theorem mark_multiple_divs_size {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_multiple S n hnpos hdvd).divs.size = S.divs.size := by
  rw [Sieve.hsize, Sieve.hsize]

-- The 'primes' field is unchanged by 'mark_multiple'
@[simp] theorem mark_multiple_primes {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt) :
  (mark_multiple S n hnpos hdvd).primes = S.primes := by
  unfold mark_multiple; simp
  split_ifs with h
  · apply mark_multiple_primes
  · rfl
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Every cell marked in 'S' is also marked in 'mark_multiple S'
theorem mark_multiple_marked_of_marked {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt) :
  ∀ i, (ilt : i < S.divs.size) → S.divs[i]'ilt ≠ 0 →
  (mark_multiple S n hnpos hdvd).divs[i]'(by simpa) ≠ 0 := by
  intro i ilt hmark
  unfold mark_multiple; dsimp
  split_ifs with h
  · push_neg
    apply mark_multiple_marked_of_marked
    · apply mark_sieve_marked_of_marked <;> assumption
  · exact hmark
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Show that 'mark_multiple' does indeed mark every
-- multiple of 'p' greater than or equal to 'n'
theorem mark_multiple_verify {L : ℕ} (S : Sieve L) (n : Int32)
  (hnpos : 0 < n)
  (hdvd : S.p.toInt ∣ n.toInt) :
  ∀ (i : ℕ), (n.toInt ≤ (i : ℤ)) → (ilt : i < S.divs.size) →
    S.p.toInt ∣ (i : ℤ) →
  (mark_multiple S n hnpos hdvd).divs[i]'(by
    rwa [mark_multiple_divs_size]
  ) ≠ 0 := by
  have hppos' := int32_toInt_pos_of_pos S.hppos
  have hnpos' := int32_toInt_pos_of_pos hnpos
  have hnabs : (n.toInt.natAbs : ℤ) = n.toInt := Int.natAbs_of_nonneg (le_of_lt hnpos')
  intro i nlei ilt pdvdi
  unfold mark_multiple
  split_ifs with h
  · simp; push_neg
    have hnlt : n.toInt < 2^30 :=
      int32_toInt_lt_of_lt_divs_size S _ h
    have ipos : 0 < (i : ℤ) :=
      lt_of_lt_of_le (int32_toInt_pos_of_pos hnpos) nlei
    have := int32_toInt_add_of_pos_of_dvd_of_lt S.p n S.hppos hnpos hdvd hnlt
    rw [Int.add_comm, Int32.add_comm] at this
    have hnppos : 0 < n + S.p := by
      apply Int32.lt_iff_toInt_lt.mpr
      rw [this]; simp
      exact Int.add_pos hnpos' hppos'
    have hdvd' : S.p.toInt ∣ (n + S.p).toInt := by
      rw [this]
      exact Int.dvd_add hdvd (by use 1; simp)
    let S' := (mark_sieve S n hnpos h hdvd)
    have hnextp' :
      ∀ (q : ℕ), Nat.Prime q → ↑q < S.p.toInt → ↑q ∈ Array.map Int32.toInt S'.primes := by
      intro q qprime qlt
      unfold S'
      rw [mark_sieve_primes]
      exact S.hpnext q qprime qlt
    by_cases hnple : (n + S.p).toInt ≤ (i : ℤ)
    · apply mark_multiple_verify S' (n + S.p) hnppos hdvd' i hnple _ pdvdi
      unfold S'; simpa
    rename' hnple => ilt'; push_neg at ilt'
    -- At this point, from nlei, ilt', and pdvdi we can conclude that i = n
    rw [this] at ilt'
    rcases pdvdi with ⟨ki, hipk⟩
    have hdvdcp := hdvd
    rcases hdvdcp with ⟨kn, hnpk⟩
    rw [hipk, hnpk] at ilt'
    rw [hipk, hnpk] at nlei
    nth_rw 3 [← Int.mul_one S.p.toInt] at ilt'
    rw [← Int.mul_add] at ilt'
    apply (Int.mul_lt_mul_left hppos').mp at ilt'
    apply (Int.mul_le_mul_left hppos').mp at nlei
    have hknki : kn = ki := Int.le_antisymm nlei (Int.le_of_lt_add_one ilt')
    rw [← hknki, ← hnpk] at hipk
    rename' hipk => hin
    apply mark_multiple_marked_of_marked
    · convert mark_sieve_index_marked S n hnpos h hdvd
      apply Int.ofNat_inj.mp; symm
      exact hin ▸ hnabs
    simpa
  · intro h'
    apply h
    apply lt_of_le_of_lt _ ilt
    apply Int.le_of_ofNat_le_ofNat
    rwa [hnabs]
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Verify that 'mark_multiples' does indeed mark every multiple of 'p'
theorem mark_multiples_verify {L : ℕ} (S : Sieve L) :
  ∀ (i : ℕ), (0 < i) → (ilt : i < S.divs.size) →
    S.p.toInt ∣ (i : ℤ) →
  (mark_multiples S).divs[i]'(by
    unfold mark_multiples; simpa
  ) ≠ 0 := by
  intro i hipos ilt pdvdi
  unfold mark_multiples
  have hipos' : 0 < (i : ℤ) := Int.ofNat_lt_ofNat_of_lt hipos
  have plei := Int.le_of_dvd hipos' pdvdi
  apply mark_multiple_verify <;> assumption

-- Used in 'find_next_prime' below
lemma int32_toInt_succ_of_lt_sieve_length {L : ℕ} (S : Sieve L)
  (n : Int32) (hlt : n.toInt < (L : ℤ)) :
  (n + 1).toInt = n.toInt + 1 := by
  apply int32_toInt_succ _ (Int32.lt_iff_toInt_lt.mpr _)
  apply lt_trans hlt (lt_trans (Int.ofNat_lt_ofNat_of_lt S.hLlt) _)
  unfold Int32.maxValue; simp

-- Used in 'find_next_prime' below
lemma int32_lt_succ_of_lt_sieve_length {L : ℕ} (S : Sieve L)
  (n : Int32) (hlt : n.toInt < (L : ℤ)) :
  n < n + 1 := by
  apply Int32.lt_iff_toInt_lt.mpr
  convert Int.lt_succ n.toInt
  exact int32_toInt_succ_of_lt_sieve_length S n hlt

-- Prove that 'find_next_prime_impl' (defined below) terminates
-- This will also be used to prove termination for many related proofs
lemma find_next_prime_impl_termination
  {L : ℕ} (S : Sieve L) (n : Int32) (hltn : 1 < n) (nlt : n.toInt < (L : ℤ)) :
  S.divs.size - (n + 1).toInt.natAbs < S.divs.size - n.toInt.natAbs := by
  have hnpos : 0 < n := Int32.lt_trans (by simp) hltn
  have nlt' := sieve_idx_lt_divs_size S n (Int32.le_of_lt hnpos) nlt
  exact sieve_termination S _ _ hnpos (by simp) nlt' (Int32.le_of_lt hltn)

-- Loop over the entries in the sieve to find the next prime
def find_next_prime_impl {L : ℕ} (S : Sieve L)
  (n : Int32) (hltn : 1 < n) : Int32 :=
  if nlt : n.toInt < (L : ℤ) then
  if h : S.divs[n.toInt.natAbs]'(by
      apply Int.lt_of_ofNat_lt_ofNat
      convert S.hsize ▸ nlt
      apply Int.natAbs_of_nonneg (le_of_lt _)
      apply lt_trans _ (Int32.lt_iff_toInt_lt.mp hltn); simp
  ) = 0 then n else
  find_next_prime_impl S (n + 1) (by
    apply Int32.lt_trans hltn
    exact int32_lt_succ_of_lt_sieve_length S _ nlt
  ) else Int32.ofInt (L : ℤ)
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  apply find_next_prime_impl_termination <;> assumption

-- Starting with the current prime, search for the next prime
def find_next_prime {L : ℕ} (S : Sieve L) : Int32 :=
  find_next_prime_impl S (S.p + 1) (by
    apply Int32.lt_iff_toInt_lt.mpr
    rw [int32_toInt_succ_of_lt_sieve_length S _ S.hplt]; simp
    exact Int32.lt_iff_toInt_lt.mp S.hppos
  )

-- 'find_next_prime_impl' always returns a non-negative integer
theorem find_next_prime_impl_nonneg {L : ℕ} (S : Sieve L)
  (n : Int32) (hltn : 1 < n) :
  0 ≤ (find_next_prime_impl S n hltn).toInt := by
  unfold find_next_prime_impl; dsimp
  split_ifs with h₀ h₁
  · exact le_of_lt (lt_trans (by simp) (Int32.lt_iff_toInt_lt.mp hltn))
  · apply find_next_prime_impl_nonneg
  · have Lnn := Int.natCast_nonneg L
    have ltL : -2^31 ≤ (L : ℤ) := le_trans (by simp) Lnn
    rwa [Int32.toInt_ofInt_of_le ltL]
    exact lt_trans (Int.ofNat_lt_ofNat_of_lt S.hLlt) (by simp)
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  apply find_next_prime_impl_termination <;> assumption

-- 'find_next_prime' always returns a non-negative integer
theorem find_next_prime_nonneg {L : ℕ} (S : Sieve L) :
  0 ≤ (find_next_prime S).toInt := by
  unfold find_next_prime
  apply find_next_prime_impl_nonneg

-- For the length of the sieve, Int32.ofInt and Int32.toInt are inverses
lemma sieve_length_toInt_ofInt {L : ℕ} (S : Sieve L) :
  (Int32.ofInt (L : ℤ)).toInt = (L : ℤ) := by
  apply Int32.toInt_ofInt_of_le
  · exact le_trans (by simp) (Int.natCast_nonneg L)
  · exact lt_trans (Int.ofNat_lt_ofNat_of_lt S.hLlt) (by simp)

-- 'find_next_prime_impl' finds an unmarked entry in the sieve
-- if its search doesn't reach the end of the sieve
theorem find_next_prime_impl_unmarked {L : ℕ} (S : Sieve L)
  (n : Int32) (hltn : 1 < n) :
  (fun p (pnn : 0 ≤ p) ↦ (h : p.toInt < (L : ℤ)) →
    S.divs[p.toInt.natAbs]'(sieve_idx_lt_divs_size S p pnn h) = 0
  ) (find_next_prime_impl S n hltn) (by
    apply Int32.le_iff_toInt_le.mpr
    exact find_next_prime_impl_nonneg S n hltn
  ) := by
  dsimp
  intro h
  unfold find_next_prime_impl; dsimp
  split_ifs with h₀ h₁
  · exact h₁
  · unfold find_next_prime_impl at h; dsimp at h
    rw [dif_pos h₀, if_neg h₁] at h
    apply find_next_prime_impl_unmarked
    assumption
  · unfold find_next_prime_impl at h; dsimp at h
    rw [dif_neg h₀] at h
    absurd h; push_neg
    apply Int.le_of_eq; symm
    exact sieve_length_toInt_ofInt S
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  apply find_next_prime_impl_termination <;> assumption

-- 'find_next_prime' finds an unmarked entry in the sieve
-- if its search doesn't reach the end of the sieve
theorem find_next_prime_unmarked {L : ℕ} (S : Sieve L) :
  (fun p (pnn : 0 ≤ p) ↦ (h : p.toInt < (L : ℤ)) →
    S.divs[p.toInt.natAbs]'(
      sieve_idx_lt_divs_size S p pnn h
    ) = 0
  ) (find_next_prime S) (by
    apply Int32.le_iff_toInt_le.mpr
    exact find_next_prime_nonneg S
  ) := by
  dsimp
  intro h
  unfold find_next_prime at *
  apply find_next_prime_impl_unmarked
  assumption

-- The value of 'find_next_prime_impl' does not exceed 'L'
theorem find_next_prime_impl_ub
  {L : ℕ} (S : Sieve L) (n : Int32) (hltn : 1 < n) :
  (find_next_prime_impl S n hltn).toInt ≤ (L : ℤ) := by
  unfold find_next_prime_impl; dsimp
  split_ifs with h₀ h₁
  · exact le_of_lt h₀
  · apply find_next_prime_impl_ub
  · apply Int.le_of_eq
    exact sieve_length_toInt_ofInt S
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  apply find_next_prime_impl_termination <;> assumption

-- The value of 'find_next_prime' does not exceed 'L'
theorem find_next_prime_ub {L : ℕ} (S : Sieve L) :
  (find_next_prime S).toInt ≤ (L : ℤ) := by
  unfold find_next_prime
  apply find_next_prime_impl_ub

-- Every entry between the starting point of the search and
-- the value returned by 'find_next_prime_impl' is marked
theorem find_next_prime_impl_first_unmarked
  {L : ℕ} (S : Sieve L) (n : Int32) (hltn : 1 < n) :
  ∀ (i : ℕ), n.toInt ≤ (i : ℤ) →
  (ilt : (i : ℤ) < (find_next_prime_impl S n hltn).toInt) →
  S.divs[i]'(by
    rw [S.hsize]
    apply Int.lt_of_ofNat_lt_ofNat (lt_of_lt_of_le ilt _)
    apply find_next_prime_impl_ub
  ) ≠ 0 := by
  intro i nlei ilt
  have ilt' : i < L := by
    apply Int.lt_of_ofNat_lt_ofNat
    apply lt_of_lt_of_le ilt
    apply find_next_prime_impl_ub
  unfold find_next_prime_impl at ilt; dsimp at ilt
  split_ifs at ilt with h₀ h₁
  · absurd nlei; push_neg
    assumption
  · by_cases hni : n.toInt = (i : ℤ)
    · convert h₁
      rw [hni]; simp
    have hnlti : n.toInt < (i : ℤ) := lt_of_le_of_ne nlei hni
    have hltns : 1 < n + 1 := by
      apply Int32.lt_trans hltn
      exact int32_lt_succ_of_lt_sieve_length S n h₀
    apply find_next_prime_impl_first_unmarked S (n + 1) hltns i _ ilt
    rw [int32_toInt_succ_of_lt_sieve_length S n h₀]
    exact Int.add_one_le_of_lt hnlti
  · absurd nlei; push_neg
    apply lt_of_lt_of_le _ (le_of_not_gt h₀)
    exact Int.ofNat_lt_ofNat_of_lt ilt'
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  apply find_next_prime_impl_termination <;> assumption

-- Every entry between the starting point of the search and
-- the value returned by 'find_next_prime_impl' is marked
theorem find_next_prime_first_unmarked
  {L : ℕ} (S : Sieve L) :
  ∀ (i : ℕ), S.p.toInt + 1 ≤ (i : ℤ) →
  (ilt : (i : ℤ) < (find_next_prime S).toInt) →
  S.divs[i]'(by
    rw [S.hsize]
    apply Int.lt_of_ofNat_lt_ofNat (lt_of_lt_of_le ilt _)
    apply find_next_prime_ub
  ) ≠ 0 := by
  intro i plti ilt
  unfold find_next_prime at ilt
  rw [← int32_toInt_succ_of_lt_sieve_length S S.p S.hplt] at plti
  apply find_next_prime_impl_first_unmarked S (S.p + 1) _ i plti ilt

end CodeChef
