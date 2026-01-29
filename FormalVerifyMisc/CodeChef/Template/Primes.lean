import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import FormalVerifyMisc.Int32.Basic

/- The purpose of this file is to verify the implementation of the
   Sieve of Eratosthenes from the template code I use on codechef.com -/

def SIEVE_SIZE : Nat := 1000001

structure Sieve where
  divs : Array Int32
  primes : Array Int32
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
