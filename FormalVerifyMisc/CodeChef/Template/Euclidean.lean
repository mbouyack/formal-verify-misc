import FormalVerifyMisc.CodeChef.Template.Gcd
import FormalVerifyMisc.Int64.Abs
import FormalVerifyMisc.Int64.Mod

namespace CodeChef

/- The purpose of this file is to verify the implementation of the
   extended eucliean algorithm from the template code I use on codechef.com -/

/-
  // Here is the original C++ implementation
  std::pair<int64_t, int64_t> solvelinear(int64_t X, int64_t Y, int64_t Z) {
    static std::vector<int64_t> stack;

    int64_t prev = X;
    int64_t cur = Y;
    int64_t next;

    while (cur) {
        next = prev % cur;
        stack.push_back(prev / cur);
        prev = cur;
        cur = next;
    }

    int64_t d = prev;
    int64_t a, b, new_b;

    a = 1;
    b = 1 - stack.back();
    stack.pop_back();

    while (!stack.empty()) {
        new_b = a - stack.back()*b;
        a = b;
        b = new_b;
        stack.pop_back();
    }

    return std::make_pair((Z/d)*a, (Z/d)*b);
}-/

-- Solves the equation ax + by = gcd x y
-- Returns the triple ⟨a, b, gcd x y⟩
def euclidean (x y : Int64)
  (_ : x ≠ 0) (hynz : y ≠ 0) : Int64 × Int64 × Int64 :=
  if h : x % y = 0 then ⟨0, int64_sign y, y⟩ else
  (fun ⟨a, b, d⟩ ↦ ⟨b, a - (x / y) * b, d⟩) (euclidean y (x % y) hynz h)
termination_by y.toInt.natAbs
decreasing_by
  simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  apply Int.natAbs_ne_zero.mpr
  exact int64_toInt_ne_zero_of_ne_zero hynz

-- Solves the equation ax + by = z, when gcd x y ∣ z
def euclidean' (x y z : Int64) (hxnz : x ≠ 0) (hynz : y ≠ 0) : Int64 × Int64 :=
  (fun ⟨a, b, d⟩ ↦ ⟨(z / d) * a, (z / d) * b⟩)
  (euclidean x y hxnz hynz)

-- This result will be used in both 'euclidean_bounds' and 'euclidean_verify'
lemma int64_sub_tdiv_mul_abs_lt_of_natAbs_le (a b x y : Int64)
  (hlbx : Int64.minValue < x)
  (hab : a.toInt.natAbs ≤ (x % y).toInt.natAbs)
  (hbb : b.toInt.natAbs ≤ y.toInt.natAbs) :
  |a.toInt - x.toInt.tdiv y.toInt * b.toInt| < 2 ^ 63 := by
  rw [Int.abs_eq_natAbs]
  apply Int.ofNat_lt_ofNat_of_lt
  rw [Int64.toInt_mod, Int.natAbs_tmod] at hab
  apply Nat.lt_of_le_of_lt _ (int64_natAbs_toInt_lt _ hlbx)
  apply le_trans (Int.natAbs_sub_le _ _)
  rw [Int.natAbs_mul, Int.natAbs_tdiv]
  nth_rw 2 [← Nat.div_add_mod x.toInt.natAbs y.toInt.natAbs]
  rw [add_comm, mul_comm]
  apply Nat.add_le_add _ hab
  exact Nat.mul_le_mul_right _ hbb

-- This result will be used in both 'euclidean_bounds' and 'verify_euclidean'
lemma int64_tdiv_mul_abs_lt_of_natAbs_le
  (x y z : Int64) (hlbx : Int64.minValue < x)
  (hzb : z.toInt.natAbs ≤ y.toInt.natAbs) :
  |(x / y).toInt * z.toInt| < 2 ^ 63 := by
  rw [int64_toInt_div _ _ (Or.inl hlbx)]
  convert int64_sub_tdiv_mul_abs_lt_of_natAbs_le
    0 z x y hlbx (Nat.zero_le _) hzb using 1
  simp

lemma euclidean_bounds (x y : Int64)
  (hxnz : x ≠ 0) (hynz : y ≠ 0)
  (hlbx : Int64.minValue < x) (hlby : Int64.minValue < y) :
  (euclidean x y hxnz hynz).1.toInt.natAbs ≤ y.toInt.natAbs ∧
  (euclidean x y hxnz hynz).2.1.toInt.natAbs ≤ x.toInt.natAbs := by
  unfold euclidean
  by_cases h : x % y = 0
  · rw [dif_pos h]; simp
    rw [int64_toInt_sign]
    rw [Int.natAbs_sign]
    rw [if_neg (int64_toInt_ne_zero_of_ne_zero hynz)]
    apply Nat.one_le_of_lt
    apply Int.natAbs_pos.mpr
    contrapose! hxnz
    apply Int64.toInt_inj.mp
    rw [hxnz, Int64.toInt_zero]
  rw [dif_neg h]; dsimp
  let a := (euclidean y (x % y) hynz h).1
  let b := (euclidean y (x % y) hynz h).2.1
  have hlbmod := int64_minval_lt_mod x y  hlbx
  have hrecurse := euclidean_bounds y (x % y) hynz h hlby hlbmod
  have hab : a.toInt.natAbs ≤ (x % y).toInt.natAbs := hrecurse.1
  have hbb : b.toInt.natAbs ≤ y.toInt.natAbs := hrecurse.2
  clear hrecurse
  use hbb
  change (a - (x / y) * b).toInt.natAbs ≤ x.toInt.natAbs
  have h₀ : in_bounds_64 ((x / y).toInt * b.toInt) := by
    apply in_bounds_64_of_abs_lt
    apply int64_tdiv_mul_abs_lt_of_natAbs_le <;> assumption
  have h₁ : in_bounds_64 (a.toInt - ((x / y) * b).toInt) := by
    apply in_bounds_64_of_abs_lt
    rw [int64_toInt_mul_of_bounds _ _ h₀]
    rw [int64_toInt_div _ _ (Or.inl hlbx)]
    apply int64_sub_tdiv_mul_abs_lt_of_natAbs_le <;> assumption
  rw [int64_toInt_sub_of_bounds _ _ h₁]
  apply le_trans (Int.natAbs_sub_le _ _)
  rw [int64_toInt_mul_of_bounds _ _ h₀, int64_toInt_div _ _ (Or.inl hlbx)]
  rw [Int.natAbs_mul, Int.natAbs_tdiv]
  nth_rw 2 [← Nat.div_add_mod x.toInt.natAbs y.toInt.natAbs]
  rw [add_comm, mul_comm]
  rw [Int64.toInt_mod, Int.natAbs_tmod] at hab
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hbb) hab
termination_by y.toInt.natAbs
decreasing_by
  simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  apply Int.natAbs_ne_zero.mpr
  exact int64_toInt_ne_zero_of_ne_zero hynz

-- 'Int.gcd_tmod' seems to be a missing theorem, so prove this lemma instead
lemma int64_gcd_toInt_mod (x y : Int64) :
  Int.gcd (x % y).toInt y.toInt = Int.gcd x.toInt y.toInt := by
  rw [Int64.toInt_mod, Int.tmod_eq_emod]
  rw [← Int.gcd_emod x.toInt]
  apply Int.gcd_sub_right_left_of_dvd
  split_ifs with h
  · simp
  · exact Int.dvd_natAbs_self

theorem euclidean_verify (x y : Int64)
  (hxnz : x ≠ 0) (hynz : y ≠ 0)
  (hlbx : Int64.minValue < x) (hlby : Int64.minValue < y) :
  (fun ⟨a, b, _⟩ ↦ a.toInt * x.toInt + b.toInt * y.toInt)
  (euclidean x y hxnz hynz) = ↑(Int.gcd x.toInt y.toInt) := by
  dsimp
  unfold euclidean
  by_cases hmodz : x % y = 0
  · rw [dif_pos hmodz]; simp
    rw [int64_toInt_sign]
    rw [Int.sign_mul_self]
    apply Int.ofNat_inj.mpr; symm
    apply Int.gcd_eq_natAbs_right
    apply Int.dvd_of_tmod_eq_zero
    rw [← Int64.toInt_mod]
    rwa [← int64_toInt_zero_iff]
  rw [dif_neg hmodz]; dsimp
  let a := (euclidean y (x % y) hynz hmodz).1
  let b := (euclidean y (x % y) hynz hmodz).2.1
  have hlbmod := int64_minval_lt_mod x y hlbx
  have hbounds := euclidean_bounds y (x % y) hynz hmodz hlby hlbmod
  have hab : a.toInt.natAbs ≤ (x % y).toInt.natAbs := hbounds.1
  have hbb : b.toInt.natAbs ≤ y.toInt.natAbs := hbounds.2
  clear hbounds
  change b.toInt * x.toInt + (a - x / y * b).toInt * y.toInt = _
  have hbounds₀ : in_bounds_64 ((x / y).toInt * b.toInt) := by
    apply in_bounds_64_of_abs_lt
    apply int64_tdiv_mul_abs_lt_of_natAbs_le <;> assumption
  have hbounds₁ : in_bounds_64 (a.toInt - ((x / y) * b).toInt) := by
    rw [int64_toInt_mul_of_bounds _ _ hbounds₀]
    rw [int64_toInt_div _ _ (Or.inl hlbx)]
    apply in_bounds_64_of_abs_lt
    apply int64_sub_tdiv_mul_abs_lt_of_natAbs_le <;> assumption
  rw [int64_toInt_sub_of_bounds _ _ hbounds₁]
  rw [int64_toInt_mul_of_bounds _ _ hbounds₀]
  rw [← int64_gcd_toInt_mod, Int.gcd_comm]
  rw [← euclidean_verify y (x % y) hynz hmodz hlby hlbmod]; dsimp
  change _ = a.toInt * _ + b.toInt * _
  rw [Int.sub_mul, ← Int.add_sub_assoc]
  apply sub_eq_of_eq_add
  rw [add_comm, add_assoc]
  apply (Int.add_right_inj (a.toInt * y.toInt)).mpr
  rw [mul_comm _ b.toInt, mul_assoc, ← mul_add]
  rw [add_comm, int64_toInt_div _ _ (Or.inl hlbx)]
  rw [Int64.toInt_mod]
  rw [Int.tdiv_mul_add_tmod]
termination_by y.toInt.natAbs
decreasing_by
  simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  apply Int.natAbs_ne_zero.mpr
  exact int64_toInt_ne_zero_of_ne_zero hynz

end CodeChef
