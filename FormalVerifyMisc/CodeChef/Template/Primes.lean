import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import FormalVerifyMisc.Int32.Basic

namespace CodeChef

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

-- Prevent '2^31' from having to be written as '2 ^ 31'
set_option linter.style.commandStart false

def SIEVE_SIZE : Nat := 1000001

structure Sieve where
  divs : Array Int32
  primes : Array Int32
  hsize : divs.size < 2^30
  hdivsnn : ∀ x ∈ divs, 0 ≤ x
  hprimespos : ∀ p ∈ primes, 0 < p
  hmarked : ∀ p ∈ primes, ∀ i, (0 < i) → (ilt : i < divs.size) →
    p.toInt ∣ (i : ℤ) → divs[i] ≠ 0
  hpmem_iff : (hnnil : primes ≠ #[]) → ∀ p : Nat,
    ((p : ℤ) ∈ (Array.map Int32.toInt primes) ↔
     (p : ℤ) ≤ (primes.back (Array.size_pos_iff.mpr hnnil)).toInt ∧ Nat.Prime p)
  hdivs_dvd : ∀ i, (ilt : i < divs.size) → divs[i]'(ilt) ≠ 0 →
    (divs[i]'(ilt)).toInt ∣ i ∧
    ∀ y, 1 < y → y ∣ i → (divs[i]'(ilt)).toInt ≤ (y : ℤ)

-- Construct a sieve with all elements set to zero
def init_sieve : Sieve where
  divs := Array.replicate SIEVE_SIZE 0
  primes := #[]
  hsize := by
    unfold SIEVE_SIZE;
    simp
  hdivsnn := by
    intro x xmem
    rw [(Array.mem_replicate.mp xmem).2]; rfl
  hprimespos :=
    fun _ hmem ↦ False.elim (Array.not_mem_empty _ hmem)
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
def mark_sieve (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) : Sieve where
  divs := if S.divs[n.toInt.natAbs] ≠ 0 then S.divs
    else S.divs.set n.toInt.natAbs p nlt
  primes := S.primes
  hsize := by
    split_ifs with h
    · exact S.hsize
    · rw [Array.size_set nlt]
      exact S.hsize
  hdivsnn := by
    intro x
    split_ifs with h
    · intro xmem
      exact S.hdivsnn x xmem
    · intro xmem
      rcases Array.mem_or_eq_of_mem_set xmem with lhs | rhs
      · exact S.hdivsnn x lhs
      · rw [← rhs] at hppos
        exact Int32.le_of_lt hppos
  hprimespos := S.hprimespos
  hmarked := by
    intro q qmem i ipos
    split_ifs with h
    · intro ilt qdvd
      exact S.hmarked q qmem i ipos ilt qdvd
    · intro ilt qdvd
      rw [Array.getElem_set nlt ilt]
      split_ifs with h'
      · contrapose! hppos; subst hppos; simp
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
        have qmem := hnextp q qprime (lt_of_le_of_lt (Int.ofNat_le_ofNat_of_le qley) h)
        rcases Array.exists_of_mem_map qmem with ⟨m, mmem, hmq⟩
        apply S.hmarked m mmem _ nabspos nlt
        rw [hmq]
        exact Int.ofNat_dvd.mpr qdvdn
      · rw [if_neg h'] at hinz
        rw [Array.size_set nlt] at ilt
        exact S.hdivs_dvd i ilt hinz

@[simp] theorem mark_sieve_divs_size (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  (mark_sieve S p n hppos hnpos nlt hprime hnextp hdvd).divs.size = S.divs.size := by
  unfold mark_sieve; simp
  split_ifs with h
  · exact Array.size_set nlt
  · rfl

@[simp] theorem mark_sieve_primes (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  (mark_sieve S p n hppos hnpos nlt hprime hnextp hdvd).primes = S.primes := rfl

-- Every cell marked in 'S' is also marked in 'mark_sieve S'
theorem mark_sieve_marked_of_marked (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  ∀ i, (ilt : i < S.divs.size) → S.divs[i]'ilt ≠ 0 →
  (mark_sieve S p n hppos hnpos nlt hprime hnextp hdvd).divs[i]'(by simpa) ≠ 0 := by
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
theorem mark_sieve_index_marked (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (nlt : n.toInt.natAbs < S.divs.size)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  (mark_sieve S p n hppos hnpos nlt hprime hnextp hdvd).divs[n.toInt.natAbs]'(by simpa) ≠ 0 := by
  unfold mark_sieve; dsimp
  split_ifs with h
  · rw [Array.getElem_set]; simp
    contrapose! hppos
    rw [hppos]; simp
  · assumption

lemma int32_toInt_lt_of_lt_divs_size (S : Sieve) (n : Int32)
  (hnlt : n.toInt.natAbs < S.divs.size) : n.toInt < 2^30 := by
  by_cases h : n.toInt ≤ 0
  · apply lt_of_le_of_lt h (by simp)
  push_neg at h
  apply Int.ofNat_lt.mpr at hnlt
  rw [Int.natAbs_of_nonneg (le_of_lt h)] at hnlt
  exact lt_trans hnlt (Int.ofNat_lt_ofNat_of_lt S.hsize)

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

-- Prove the termination requirements for 'mark_multiple'
lemma mark_multiple_termination (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hdvd : p.toInt ∣ n.toInt)
  (hnlt : n.toInt.natAbs < S.divs.size) :
  S.divs.size - (n + p).toInt.natAbs < S.divs.size - n.toInt.natAbs := by
  have hppos' := int32_toInt_pos_of_pos hppos
  have hnpos' := int32_toInt_pos_of_pos hnpos
  have hnp : (n + p).toInt = n.toInt + p.toInt := by
    rw [Int.add_comm, Int32.add_comm]
    apply int32_toInt_add_of_pos_of_dvd_of_lt p n hppos hnpos hdvd
    exact int32_toInt_lt_of_lt_divs_size S _ hnlt
  rw [hnp]
  apply Nat.sub_lt_sub_left hnlt
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hnpos')
  exact Int.lt_add_of_pos_right _ hppos'

-- Mark one multiple of 'p' in sieve 'S'
def mark_multiple (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) : Sieve :=
  if hnlt : n.toInt.natAbs < S.divs.size then
  (fun (hnp : (n + p).toInt = n.toInt + p.toInt) ↦
    mark_multiple
      (mark_sieve S p n hppos hnpos hnlt hprime hnextp hdvd)
      p (n + p) hppos (by
        apply Int32.lt_iff_toInt_lt.mpr
        rw [hnp]
        apply Int.add_pos (Int32.lt_iff_toInt_lt.mp hnpos)
        exact Int32.lt_iff_toInt_lt.mp hppos
      ) hprime hnextp (by
        rw [hnp]
        exact Int.dvd_add hdvd (by use 1; simp)
      ))
  (by
    have hppos' := int32_toInt_pos_of_pos hppos
    have hnpos' := int32_toInt_pos_of_pos hnpos
    rw [Int.add_comm, Int32.add_comm]
    apply int32_toInt_add_of_pos_of_dvd_of_lt p n hppos hnpos hdvd
    exact int32_toInt_lt_of_lt_divs_size S _ hnlt
  ) else S
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Mark all multiples of the next prime, 'p', in the Sieve
def mark_multiples (S : Sieve) (p : Int32)
  (hppos : 0 < p)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes)) : Sieve :=
  mark_multiple S p p hppos hppos hprime hnextp (by use 1; simp)

@[simp] theorem mark_multiple_divs_size (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  (mark_multiple S p n hppos hnpos hprime hnextp hdvd).divs.size = S.divs.size := by
  unfold mark_multiple; simp
  split_ifs with h
  · rw [mark_multiple_divs_size, mark_sieve_divs_size]
  · rfl
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- The 'primes' field is unchanged by 'mark_multiple'
@[simp] theorem mark_multiple_primes (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  (mark_multiple S p n hppos hnpos hprime hnextp hdvd).primes = S.primes := by
  unfold mark_multiple; simp
  split_ifs with h
  · apply mark_multiple_primes
  · rfl
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  rw [mark_sieve_divs_size]
  apply mark_multiple_termination <;> assumption

-- Every cell marked in 'S' is also marked in 'mark_multiple S'
theorem mark_multiple_marked_of_marked (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  ∀ i, (ilt : i < S.divs.size) → S.divs[i]'ilt ≠ 0 →
  (mark_multiple S p n hppos hnpos hprime hnextp hdvd).divs[i]'(by simpa) ≠ 0 := by
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
theorem mark_multiple_verify (S : Sieve) (p n : Int32)
  (hppos : 0 < p) (hnpos : 0 < n)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes))
  (hdvd : p.toInt ∣ n.toInt) :
  ∀ (i : ℕ), (n.toInt ≤ (i : ℤ)) → (ilt : i < S.divs.size) →
    p.toInt ∣ (i : ℤ) →
  (mark_multiple S p n hppos hnpos hprime hnextp hdvd).divs[i]'(by
    rwa [mark_multiple_divs_size]
  ) ≠ 0 := by
  have hppos' := int32_toInt_pos_of_pos hppos
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
    have := int32_toInt_add_of_pos_of_dvd_of_lt p n hppos hnpos hdvd hnlt
    rw [Int.add_comm, Int32.add_comm] at this
    have hnppos : 0 < n + p := by
      apply Int32.lt_iff_toInt_lt.mpr
      rw [this]; simp
      exact Int.add_pos hnpos' hppos'
    have hdvd' : p.toInt ∣ (n + p).toInt := by
      rw [this]
      exact Int.dvd_add hdvd (by use 1; simp)
    let S' := (mark_sieve S p n hppos hnpos h hprime hnextp hdvd)
    have hnextp' :
      ∀ (q : ℕ), Nat.Prime q → ↑q < p.toInt → ↑q ∈ Array.map Int32.toInt S'.primes := by
      intro q qprime qlt
      unfold S'
      rw [mark_sieve_primes]
      exact hnextp q qprime qlt
    by_cases hnple : (n + p).toInt ≤ (i : ℤ)
    · apply mark_multiple_verify S' p (n + p) hppos hnppos hprime hnextp' hdvd' i hnple _ pdvdi
      unfold S'
      rwa [mark_sieve_divs_size]
    rename' hnple => ilt'; push_neg at ilt'
    -- At this point, from nlei, ilt', and pdvdi we can conclude that i = n
    rw [this] at ilt'
    rcases pdvdi with ⟨ki, hipk⟩
    have hdvdcp := hdvd
    rcases hdvdcp with ⟨kn, hnpk⟩
    rw [hipk, hnpk] at ilt'
    rw [hipk, hnpk] at nlei
    nth_rw 3 [← Int.mul_one p.toInt] at ilt'
    rw [← Int.mul_add] at ilt'
    apply (Int.mul_lt_mul_left hppos').mp at ilt'
    apply (Int.mul_le_mul_left hppos').mp at nlei
    have hknki : kn = ki := Int.le_antisymm nlei (Int.le_of_lt_add_one ilt')
    rw [← hknki, ← hnpk] at hipk
    rename' hipk => hin
    apply mark_multiple_marked_of_marked
    · convert mark_sieve_index_marked S p n hppos hnpos h hprime hnextp hdvd
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
theorem mark_multiples_verify (S : Sieve) (p : Int32)
  (hppos : 0 < p)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes)) :
  ∀ (i : ℕ), (0 < i) → (ilt : i < S.divs.size) →
    p.toInt ∣ (i : ℤ) →
  (mark_multiples S p hppos hprime hnextp).divs[i]'(by
    unfold mark_multiples; simpa
  ) ≠ 0 := by
  intro i hipos ilt pdvdi
  unfold mark_multiples
  have hipos' : 0 < (i : ℤ) := Int.ofNat_lt_ofNat_of_lt hipos
  have plei := Int.le_of_dvd hipos' pdvdi
  apply mark_multiple_verify <;> assumption

end CodeChef
