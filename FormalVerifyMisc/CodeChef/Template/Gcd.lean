import FormalVerifyMisc.Int32.Abs
import FormalVerifyMisc.Int32.Mod

namespace CodeChef

/- The purpose of this file is to verify the implementation of 'gcd' from the
   template code I use on codechef.com -/

/-
  // Here is the original C implementation
  int gcd(int a, int b) {
    while (b) {
        int r = a % b;
        a = b;
        b = r;
    }

    return (a < 0 ? -a : a);
  }
-/

def gcd (a b : Int32) : Int32 :=
  if b = 0 then int32_abs a else gcd b (a % b)
termination_by b.toInt.natAbs
decreasing_by
  rename ¬b = 0 => hnz; simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  contrapose! hnz
  apply Int32.toInt_inj.mp; simp
  exact Int.natAbs_eq_zero.mp hnz

@[simp] theorem gcd_zero_right (a : Int32) : gcd a 0 = int32_abs a := by
  unfold gcd; simp

@[simp] theorem gcd_zero_left (a : Int32) : gcd 0 a = int32_abs a := by
  unfold gcd; simp
  intro h
  convert int32_abs_zero.symm

@[simp] theorem gcd_self (a : Int32) : gcd a a = int32_abs a := by
  unfold gcd; simp

@[simp] theorem gcd_neg_self (a : Int32) : gcd a (-a) = int32_abs a := by
  unfold gcd; simp

-- The gcd function is commutative
theorem gcd_comm (a b : Int32) : gcd a b = gcd b a := by
  -- Assume without loss of generality that |a| ≤ |b|
  wlog h : int32_abs a ≤ int32_abs b
  · exact (this b a (Int32.le_of_lt (Int32.not_le.mp h))).symm
  -- Now take care of the pathological cases
  by_cases hamv : a = Int32.minValue
  · subst hamv
    by_cases hbmv : b = Int32.minValue
    · subst hbmv; rfl
    push_neg at hbmv
    have hlbb := Int32.lt_of_le_of_ne (Int32.minValue_le b) hbmv.symm
    nth_rw 2 [gcd]
    rw [if_neg (by simp), int32_mod_minval _ hlbb]
  push_neg at hamv
  have hlba := Int32.lt_of_le_of_ne (Int32.minValue_le a) hamv.symm
  by_cases hbmv : b = Int32.minValue
  · subst hbmv
    nth_rw 1 [gcd]
    rw [if_neg (by simp), int32_mod_minval _ hlba]
  push_neg at hbmv
  have hlbb := Int32.lt_of_le_of_ne (Int32.minValue_le b) hbmv.symm
  -- Now that we have proven 'a' and 'b' are well-behaved we can begin the proof, proper.
  by_cases hab : a = b
  · subst hab; rfl
  push_neg at hab
  nth_rw 1 [gcd]
  by_cases habseq : int32_abs a = int32_abs b
  · rcases (int32_abs_eq_abs_iff a b).mp habseq with lhs | rhs
    · exact False.elim (hab lhs)
    · subst rhs
      split_ifs with h'
      · subst h'; simp
      · rw [int32_neg_mod b b hlbb]; simp
  rename' habseq => habsne; push_neg at habsne
  replace h : int32_abs a < int32_abs b := Int32.lt_of_le_of_ne h habsne
  split_ifs with h'
  · subst h'; simp
  · rw [int32_mod_of_abs_lt a b h hlba hlbb]

-- Prove that int32_gcd is nonnegative when certain conditions are met.
-- Note that when these conditions are not met, the true gcd cannot be
-- represented using a signed 32-bit integer.
theorem gcd_nonneg (a b : Int32)
  (h : (Int32.minValue < a ∧ a ≠ 0) ∨ (Int32.minValue < b ∧ b ≠ 0) ∨ (a = 0 ∧ b = 0)) :
  0 ≤ gcd a b := by
  unfold gcd
  -- First handle the case where b = 0 so we can avoid recursing in more than one place
  -- That will simplify our termination proof
  by_cases h' : b = 0
  · rw [if_pos h']
    rcases h with h₀ | h₁ | h₂
    · exact int32_abs_nonneg a h₀.1
    · exact False.elim (h₁.2 h')
    · rw [h₂.1]; simp
  rw [if_neg h']
  -- Do the recursion here
  apply gcd_nonneg
  rcases h with h₀ | h₁ | h₂
  · by_cases h : Int32.minValue < b
    · exact Or.inl ⟨h, h'⟩
    replace h := int32_eq_minval b h
    right; left
    rwa [h, int32_mod_minval a h₀.1]
  · exact Or.inl h₁
  · rw [h₂.1, h₂.2]
    right; right; simp
termination_by b.toInt.natAbs
decreasing_by
  push_neg at h'; simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  contrapose! h'
  apply Int32.toInt_inj.mp; simp
  exact Int.natAbs_eq_zero.mp h'

-- Useful result needed for the theorem below
lemma dvd_of_dvd_of_dvd_tmod (a b c : Int) (h₀ : a ∣ c) (h₁ : a ∣ (b.tmod c)) : a ∣ b := by
  rw [← Int.mul_tdiv_add_tmod b c]
  exact Int.dvd_add (Int.dvd_mul_of_dvd_left h₀) h₁

-- The gcd, converted from Int32 to Int, is in-fact a common divisor
theorem gcd_dvd (a b : Int32) :
  (gcd a b).toInt ∣ a.toInt ∧ (gcd a b).toInt ∣ b.toInt := by
  unfold gcd
  -- First handle the case where b = 0
  by_cases hbz : b = 0
  · subst hbz; simp
    by_cases hmmv : a = Int32.minValue
    · subst hmmv
      rw [int32_abs_minval]
    push_neg at hmmv
    rw [int32_toInt_abs a (int32_minval_lt_of_ne_minval a hmmv.symm)]
    exact abs_dvd_self _
  rename' hbz => hbnz; push_neg at hbnz
  rw [if_neg hbnz]
  have hbnz' := int32_toInt_ne_zero_of_ne_zero hbnz
  -- Do the recursion - note that this relies on b ≠ 0
  have hrecurse := gcd_dvd b (a % b)
  rw [Int32.toInt_mod] at hrecurse
  constructor
  · exact dvd_of_dvd_of_dvd_tmod _ _ b.toInt hrecurse.1 hrecurse.2
  · exact hrecurse.1
termination_by b.toInt.natAbs
decreasing_by
  simp
  exact Nat.mod_lt _ (Int.natAbs_pos.mpr hbnz')

-- Useful result needed for the theorem below
lemma dvd_tmod_of_dvd_of_dvd
  (a b c : Int) (hdvdb : a ∣ b) (hdvdc : a ∣ c) : a ∣ b.tmod c := by
  rw [← Int.mul_tdiv_add_tmod b c] at hdvdb
  exact (dvd_add_right (dvd_mul_of_dvd_left hdvdc (b.tdiv c))).mp hdvdb

-- The gcd is in-fact the "greatest" divisor
theorem dvd_gcd_of_dvd_of_dvd
  {a b : Int32} (c : Int) (hdvda : c ∣ a.toInt) (hdvdb : c ∣ b.toInt) :
  c ∣ (gcd a b).toInt := by
  unfold gcd
  by_cases hbz : b = 0
  · subst hbz; simp
    by_cases hmmv : a = Int32.minValue
    · subst hmmv
      rwa [int32_abs_minval]
    push_neg at hmmv
    rw [int32_toInt_abs a (int32_minval_lt_of_ne_minval a hmmv.symm)]
    rwa [dvd_abs]
  rename' hbz => hbnz; push_neg at hbnz
  have hbnz' := int32_toInt_ne_zero_of_ne_zero hbnz
  rw [if_neg hbnz]
  -- Recurse
  apply dvd_gcd_of_dvd_of_dvd _ hdvdb; simp
  apply dvd_tmod_of_dvd_of_dvd <;> assumption
termination_by b.toInt.natAbs
decreasing_by
· simp
  exact Nat.mod_lt _ (Int.natAbs_pos.mpr hbnz')

-- The 'gcd' function can be moved across the 'toInt' conversion
-- if one of three conditions is met
theorem gcd_toInt_gcd (a b : Int32)
  (h : (Int32.minValue < a ∧ a ≠ 0) ∨ (Int32.minValue < b ∧ b ≠ 0) ∨ (a = 0 ∧ b = 0)) :
  (gcd a b).toInt = ↑(Int.gcd a.toInt b.toInt) := by
  have hnn := Int32.le_iff_toInt_le.mp (gcd_nonneg _ _ h); simp at hnn
  rw [← Int.ofNat_natAbs_of_nonneg hnn]
  apply Int.ofNat_inj.mpr; symm
  apply Int.gcd_eq_iff.mpr
  rw [← Int.abs_eq_natAbs]
  rw [abs_dvd, abs_dvd]
  use (gcd_dvd a b).1
  use (gcd_dvd a b).2
  intro c hdvda hdvdb
  rw [dvd_abs]
  exact dvd_gcd_of_dvd_of_dvd _ hdvda hdvdb

end CodeChef
