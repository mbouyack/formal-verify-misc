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
  if h : x % y = 0 then ⟨0, 1, y⟩ else
  (fun P ↦ ⟨P.2.1, P.1 - (x / y) * P.2.1, P.2.2⟩) (euclidean y (x % y) hynz h)
termination_by y.toInt.natAbs
decreasing_by
  simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  apply Int.natAbs_ne_zero.mpr
  exact int64_toInt_ne_zero_of_ne_zero hynz

lemma euclidean_bounds (x y : Int64)
  (hxnz : x ≠ 0) (hynz : y ≠ 0)
  (hlbx : Int64.minValue < x) (hlby : Int64.minValue < y) :
  (euclidean x y hxnz hynz).1.toInt.natAbs ≤ y.toInt.natAbs ∧
  (euclidean x y hxnz hynz).2.1.toInt.natAbs ≤ x.toInt.natAbs := by
  unfold euclidean
  by_cases h : x % y = 0
  · rw [dif_pos h]; simp
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
  rw [Int64.toInt_mod, Int.natAbs_tmod] at hab
  have h₀ : x.toInt.natAbs < 2^63 := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← Int.abs_eq_natAbs]
    rw [← int64_toInt_abs _ hlbx]
    exact int64_toInt_abs_lt _
  have h₁ : in_bounds_64 ((x / y).toInt * b.toInt) := by
    apply in_bounds_64_of_abs_lt
    rw [Int.abs_eq_natAbs]
    apply Int.ofNat_lt_ofNat_of_lt
    rw [Int.natAbs_mul, int64_toInt_div _ _ (Or.inl hlbx)]
    rw [Int.natAbs_tdiv, mul_comm]
    apply Nat.lt_of_le_of_lt _ h₀
    apply le_trans _ (Nat.mul_div_le _ y.toInt.natAbs)
    exact Nat.mul_le_mul_right _ hbb
  have h₂ : (a.toInt - (x / y * b).toInt).natAbs ≤ x.toInt.natAbs := by
    apply le_trans (Int.natAbs_sub_le _ _)
    rw [int64_toInt_mul_of_bounds _ _ h₁, int64_toInt_div _ _ (Or.inl hlbx)]
    rw [Int.natAbs_mul, Int.natAbs_tdiv]
    nth_rw 2 [← Nat.div_add_mod x.toInt.natAbs y.toInt.natAbs]
    rw [add_comm, mul_comm]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hbb) hab
  have h₃ : in_bounds_64 (a.toInt - ((x / y) * b).toInt) := by
    apply in_bounds_64_of_abs_lt
    apply Int.ofNat_le_ofNat_of_le at h₂
    rw [← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs] at h₂
    apply Int.lt_of_le_of_lt h₂
    rw [← int64_toInt_abs _ hlbx]
    exact int64_toInt_abs_lt _
  rwa [int64_toInt_sub_of_bounds _ _ h₃]
termination_by y.toInt.natAbs
decreasing_by
  simp
  apply Nat.mod_lt _ (Nat.pos_of_ne_zero _)
  apply Int.natAbs_ne_zero.mpr
  exact int64_toInt_ne_zero_of_ne_zero hynz

-- Solves the equation ax + by = z, when gcd x y ∣ z
def euclidean' (x y z : Int64)
  (hxnz : x ≠ 0) (hynz : y ≠ 0) : Int64 × Int64 :=
  (fun P ↦
    (fun k (Q : Int64 × Int64) ↦ ⟨k * Q.1, k * Q.2⟩)
    (z / P.2.2) ⟨P.1, P.2.1⟩)
  (euclidean x y hxnz hynz)

end CodeChef
