import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import FormalVerifyMisc.Int32.Basic

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

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

theorem mark_sieve_divs_size (S : Sieve) (p n : Int32)
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
    have hppos' : 0 < p.toInt := Int32.lt_iff_toInt_lt.mp hppos
    have hnpos' : 0 < n.toInt := Int32.lt_iff_toInt_lt.mp hnpos
    apply int32_toInt_add_of_bounds
    constructor
    · apply le_of_lt
      exact lt_trans (by simp) (Int.add_lt_add hnpos' hppos')
    · apply Int.ofNat_lt.mpr at hnlt
      rw [Int.natAbs_of_nonneg (le_of_lt hnpos')] at hnlt
      apply lt_of_le_of_lt (Int.add_le_add_left (Int.le_of_dvd hnpos' hdvd) n.toInt)
      rw [← two_mul, Int.pow_succ, mul_comm]
      apply (Int.mul_lt_mul_right (two_pos)).mpr
      exact lt_trans hnlt (Int.ofNat_lt.mpr S.hsize)
  ) else S
termination_by S.divs.size - n.toInt.natAbs
decreasing_by
  have hppos' : 0 < p.toInt := Int32.lt_iff_toInt_lt.mp hppos
  have hnpos' : 0 < n.toInt := Int32.lt_iff_toInt_lt.mp hnpos
  rw [mark_sieve_divs_size, hnp]
  apply Nat.sub_lt_sub_left hnlt
  apply Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hnpos')
  exact Int.lt_add_of_pos_right _ hppos'

-- Mark all multiples of the next prime, 'p', in the Sieve
def mark_multiples (S : Sieve) (p : Int32)
  (hppos : 0 < p)
  (hprime : Nat.Prime p.toInt.natAbs)
  (hnextp : ∀ q, Nat.Prime q → (q : ℤ) < p.toInt →
    (q : ℤ) ∈ (Array.map Int32.toInt S.primes)) : Sieve :=
  mark_multiple S p p hppos hppos hprime hnextp (by use 1; simp)
