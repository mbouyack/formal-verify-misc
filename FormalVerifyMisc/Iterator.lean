import FormalVerifyMisc.Int32.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

-- Define an iterator as commonly used the C++ Standard Template Library
class Iterator (α : Type) [DecidableEq α] where
  -- Get the iterator corresponding to the beginning of loop
  Begin : α
  -- Get the iterator corresponding to the end of the loop
  End : α
  -- Advance the iterator
  next : α → α
  -- Calling 'next' on 'End' has no effect
  hend : next End = End
  -- Repeatedly calling 'next' on the Begin iterator will
  -- eventually reach every other iterator.
  hbegin : ∀ iter, ∃ n, next^[n] Begin = iter

-- Repeatedly calling 'next' on the end iterator has no effect
theorem iterate_end_eq_end {α : Type} [DecidableEq α] [Iterator α] :
  ∀ n, Iterator.next^[n] (Iterator.End : α) = Iterator.End := by
  intro n
  match n with
  | 0 => rw [Function.iterate_zero_apply]
  | Nat.succ n =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [Iterator.hend]
    exact iterate_end_eq_end n

-- Repeatedly calling 'next' on an iterator eventually reaches the end
theorem iterate_eq_end {α : Type} [DecidableEq α] [Iterator α] (iter : α) :
  ∃ n, Iterator.next^[n] iter = Iterator.End := by
  rcases Iterator.hbegin iter with ⟨n₀, h₀⟩
  rcases Iterator.hbegin (Iterator.End : α) with ⟨n₁, h₁⟩
  by_cases hend : iter = Iterator.End
  · use 0; subst hend
    rw [Function.iterate_zero_apply]
  have hlt : n₀ ≤ n₁ := by
    by_contra! h
    apply hend
    rw [← h₀]
    rcases Nat.exists_eq_add_of_lt h with ⟨k, rfl⟩
    rw [add_assoc, add_comm, Function.iterate_add_apply, h₁]
    exact iterate_end_eq_end (k + 1)
  rcases Nat.exists_eq_add_of_le hlt with ⟨k, rfl⟩
  use k
  rw [← h₁, add_comm, Function.iterate_add_apply, h₀]

-- Find the distance to the 'End' iterator
-- NOTE: Originally the plan was to use this to define an efficient
-- implementation of 'iter_dist', but we don't actually need it to be
-- efficient. I've left this here in case I change my mind.
def iter_find_end {α : Type} [DecidableEq α] [Iterator α] (iter : α) : ℕ :=
  if iter = Iterator.End then 0 else
  iter_find_end (Iterator.next iter) + 1
termination_by Nat.find (iterate_eq_end iter)
decreasing_by
  rename ¬iter = Iterator.End => hend
  nth_rw 2 [Nat.find_comp_succ]
  · exact Nat.lt_add_one _
  · rwa [Function.iterate_zero_apply]

theorem iter_find_end_end {α : Type} [DecidableEq α] [Iterator α] :
  iter_find_end (Iterator.End : α) = 0 := by
  unfold iter_find_end; simp

theorem iter_find_end_next_add_one {α : Type} [DecidableEq α] [Iterator α]
  {iter : α} (hnend : ¬iter = Iterator.End) :
  iter_find_end (Iterator.next iter) + 1 = iter_find_end iter := by
  nth_rw 2 [iter_find_end]
  rw [if_neg hnend]

-- Find the distance between two iterators
-- WARNING: Runs in O(n ^ 2) time!
def iter_dist {α : Type} [DecidableEq α] [Iterator α] (iter₀ iter₁ : α) : ℕ :=
  Nat.dist (Nat.find (Iterator.hbegin iter₀)) (Nat.find (Iterator.hbegin iter₁))

theorem iter_dist_self {α : Type} [DecidableEq α] [Iterator α] (iter : α) :
  iter_dist iter iter = 0 := by
  unfold iter_dist
  exact Nat.dist_self _

-- Construct an iterator type from Int32
-- TODO: Generalize this for any native integer type
@[ext] structure IteratorInt32 (start finish inc : Int32) where
  val : Int32
  hleval : start ≤ val
  hvalle : val ≤ finish
  hdvdval : inc.toInt ∣ (val.toInt - start.toInt)
  incpos : 0 < inc
  hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt)
  hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt

instance (start finish inc : Int32) :
  DecidableEq (IteratorInt32 start finish inc) :=
  fun iter₀ iter₁ =>
    if h : iter₀.val = iter₁.val then
      isTrue (IteratorInt32.ext h)
    else
      isFalse (fun h' ↦ h (IteratorInt32.ext_iff.mp h'))

-- Construct the 'begin' iterator for InteratorInt32
def iterator_int32_begin (start finish inc : Int32)
  (incpos : 0 < inc)
  (hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt))
  (hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt)
  (hle : start ≤ finish) : IteratorInt32 start finish inc where
  val := start
  hleval := Int32.le_refl _
  hvalle := hle
  hdvdval := by
    rw [sub_self]
    exact dvd_zero _
  incpos := incpos
  hdvdfin := hdvdfin
  hsafe := hsafe

-- Construct the 'end' iterator for InteratorInt32
def iterator_int32_end (start finish inc : Int32)
  (incpos : 0 < inc)
  (hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt))
  (hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt)
  (hle : start ≤ finish) : IteratorInt32 start finish inc where
  val := finish
  hleval := hle
  hvalle := Int32.le_refl _
  hdvdval := hdvdfin
  incpos := incpos
  hdvdfin := hdvdfin
  hsafe := hsafe

@[simp] theorem iterator_int32_begin_val (start finish inc : Int32)
  (incpos : 0 < inc)
  (hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt))
  (hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt)
  (hle : start ≤ finish) :
  (iterator_int32_begin start finish inc incpos hdvdfin hsafe hle).val = start := rfl

@[simp] theorem iterator_int32_end_val (start finish inc : Int32)
  (incpos : 0 < inc)
  (hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt))
  (hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt)
  (hle : start ≤ finish) :
  (iterator_int32_end start finish inc incpos hdvdfin hsafe hle).val = finish := rfl

-- Prove that the value increment can be move across the 'toInt' conversion
lemma iterator_int32_toInt_val_inc {start finish inc : Int32}
  (iter : IteratorInt32 start finish inc) :
  (iter.val + inc).toInt = iter.val.toInt + inc.toInt := by
  have hleval' := Int32.le_iff_toInt_le.mp iter.hleval
  have hvalle' := Int32.le_iff_toInt_le.mp iter.hvalle
  have incnn := le_of_lt (Int32.lt_iff_toInt_lt.mp iter.incpos)
  rw [int32_toInt_add_of_bounds]
  constructor
  · rw [← add_zero (-2 ^ 31), ← Int32.toInt_zero]
    exact Int.add_le_add (int32_minval_le_toInt iter.val) incnn
  · apply Int.lt_of_le_sub_one
    rw [← Int32.toInt_maxValue]
    apply le_trans (Int.add_le_add_right hvalle' _) iter.hsafe

-- Define a function for advancing an IteratorInt32
def iterator_int32_next {start finish inc : Int32}
  (iter : IteratorInt32 start finish inc) : IteratorInt32 start finish inc :=
  if h : iter.val = finish then iter else
  have incnn := le_of_lt (Int32.lt_iff_toInt_lt.mp iter.incpos)
  {
    val := iter.val + inc
    hleval := by
      have hleval' := Int32.le_iff_toInt_le.mp iter.hleval
      apply Int32.le_iff_toInt_le.mpr
      rw [iterator_int32_toInt_val_inc]
      rw [← add_zero start.toInt, ← Int32.toInt_zero]
      exact Int.add_le_add hleval' incnn
    hvalle := by
      have hvalle' := Int32.le_iff_toInt_le.mp iter.hvalle
      apply Int32.le_iff_toInt_le.mpr
      rw [iterator_int32_toInt_val_inc]
      apply @Int.le_of_sub_le_sub_right _ _ start.toInt
      rw [add_sub_right_comm]
      rcases iter.hdvdval with ⟨k₀, hk₀⟩
      rcases iter.hdvdfin with ⟨k₁, hk₁⟩
      rw [hk₀, hk₁, ← mul_add_one]
      apply Int.mul_le_mul_of_nonneg_left _ incnn
      apply Int.add_one_le_of_lt
      apply Int.lt_of_mul_lt_mul_left _ incnn
      rw [← hk₀, ← hk₁]
      apply Int.sub_lt_sub_right (lt_of_le_of_ne hvalle' _)
      exact fun h' ↦ h (Int32.toInt_inj.mp h')
    hdvdval := by
      rw [iterator_int32_toInt_val_inc, add_sub_right_comm]
      apply Int.dvd_add
      · exact iter.hdvdval
      · exact dvd_refl _
    incpos := iter.incpos
    hdvdfin := iter.hdvdfin
    hsafe := iter.hsafe
  }

-- Equation for the value of an IteratorInt32 after iterating 'n' times
theorem iterator_int32_iterate_val_eq {start finish inc : Int32}
  (iter : IteratorInt32 start finish inc) (n : ℕ) :
  (iterator_int32_next^[n] iter).val.toInt =
    min finish.toInt (iter.val.toInt + n * inc.toInt) := by
  match n with
  | 0 =>
    rw [Function.iterate_zero_apply]
    rw [Int.ofNat_zero, zero_mul, add_zero]
    exact (min_eq_right (Int32.le_iff_toInt_le.mp iter.hvalle)).symm
  | Nat.succ n' =>
    rw [Function.iterate_succ_apply]
    rw [iterator_int32_iterate_val_eq]
    unfold iterator_int32_next
    split_ifs with h
    · rw [h, min_eq_left, min_eq_left]
      repeat {
      · apply Int.le_add_of_nonneg_right (Int.mul_nonneg _ _ )
        · exact Int.natCast_nonneg _
        · exact le_of_lt (Int32.lt_iff_toInt_lt.mp iter.incpos) }
    · dsimp
      rw [iterator_int32_toInt_val_inc, add_assoc, add_comm inc.toInt]
      rw [add_mul, one_mul]

instance (start finish inc : Int32)
  (incpos : 0 < inc)
  (hdvdfin : inc.toInt ∣ (finish.toInt - start.toInt))
  (hsafe : finish.toInt + inc.toInt ≤ Int32.maxValue.toInt)
  (hle : start ≤ finish) :
  Iterator (IteratorInt32 start finish inc) where
  Begin := iterator_int32_begin start finish inc incpos hdvdfin hsafe hle
  End := iterator_int32_end start finish inc incpos hdvdfin hsafe hle
  next := iterator_int32_next
  hend := by
    unfold iterator_int32_next iterator_int32_end; simp
  hbegin := by
    intro iter
    let n := (iter.val.toInt - start.toInt) / inc.toInt
    by_cases h : start.toInt = iter.val.toInt
    · use 0
      rw [Function.iterate_zero_apply]
      exact IteratorInt32.ext (Int32.toInt_inj.mp h)
    have npos : 0 < n := by
      unfold n
      apply Int.ediv_pos_of_pos_of_dvd
      · rw [Int.sub_pos]
        apply lt_of_le_of_ne _ h
        exact Int32.le_iff_toInt_le.mp iter.hleval
      · apply le_of_lt
        exact Int32.lt_iff_toInt_lt.mp incpos
      · exact iter.hdvdval
    use n.natAbs
    apply IteratorInt32.ext (Int32.toInt_inj.mp _)
    rw [iterator_int32_iterate_val_eq]
    rw [iterator_int32_begin_val]
    rw [Int.ofNat_natAbs_of_nonneg (le_of_lt npos)]
    unfold n
    rw [mul_comm]
    rw [Int.mul_ediv_cancel_of_dvd iter.hdvdval]
    rw [add_sub_cancel, min_eq_right]
    exact Int32.le_iff_toInt_le.mp iter.hvalle
