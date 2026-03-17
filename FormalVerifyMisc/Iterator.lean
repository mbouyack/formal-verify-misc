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

-- Separating these parameters from the IteratorInt32 structure
-- will make it possible to reference 'Begin' and 'End' without
-- re-proving all these results. Also, it should make the
-- invocations of functions and results related to IteratorInt32
-- more concise.
structure IteratorInt32Params where
  start : Int32
  finish : Int32
  inc : Int32
  incpos : 0 < inc
  hle : start ≤ finish
  hdvd : inc.toInt ∣ (finish.toInt - start.toInt)

-- Construct an iterator type from Int32
-- TODO: Generalize this for any native integer type
@[ext] structure IteratorInt32 (P : IteratorInt32Params) where
  val : Int32
  hleval : P.start ≤ val
  hvalle : val ≤ P.finish
  hdvd : P.inc.toInt ∣ (val.toInt - P.start.toInt)

instance {P : IteratorInt32Params} :
  DecidableEq (IteratorInt32 P) :=
  fun iter₀ iter₁ =>
    if h : iter₀.val = iter₁.val then
      isTrue (IteratorInt32.ext h)
    else
      isFalse (fun h' ↦ h (IteratorInt32.ext_iff.mp h'))

-- Construct the 'begin' iterator for InteratorInt32
def iterator_int32_begin (P : IteratorInt32Params) : IteratorInt32 P where
  val := P.start
  hleval := Int32.le_refl _
  hvalle := P.hle
  hdvd := by
    rw [sub_self]
    exact dvd_zero _

-- Construct the 'end' iterator for InteratorInt32
def iterator_int32_end (P : IteratorInt32Params) : IteratorInt32 P where
  val := P.finish
  hleval := P.hle
  hvalle := Int32.le_refl _
  hdvd := P.hdvd

@[simp] theorem iterator_int32_begin_val {P : IteratorInt32Params} :
  (iterator_int32_begin P).val = P.start := rfl

@[simp] theorem iterator_int32_end_val {P : IteratorInt32Params} :
  (iterator_int32_end P).val = P.finish := rfl

-- If the iterator has not reach "finish", we can safely add 'inc' to its value
lemma iterator_int32_val_add_inc_le_finish {P : IteratorInt32Params}
  {iter : IteratorInt32 P} (hnef : iter.val ≠ P.finish) :
  iter.val.toInt + P.inc.toInt ≤ P.finish.toInt := by
  have incnn := le_of_lt (Int32.lt_iff_toInt_lt.mp P.incpos)
  have hvalle := Int32.le_iff_toInt_le.mp iter.hvalle
  -- Subtract 'start' from both sides of the equation and
  -- rewrite everything as a multiple of 'inc'
  apply @Int.le_of_sub_le_sub_right _ _ P.start.toInt
  rw [add_sub_right_comm]
  rcases iter.hdvd with ⟨k₀, hk₀⟩
  rcases P.hdvd with ⟨k₁, hk₁⟩
  rw [hk₀, hk₁, ← mul_add_one]
  apply Int.mul_le_mul_of_nonneg_left _ incnn
  apply Int.add_one_le_of_lt
  apply Int.lt_of_mul_lt_mul_left _ incnn
  rw [← hk₀, ← hk₁]
  apply Int.sub_lt_sub_right (lt_of_le_of_ne hvalle _)
  exact fun h' ↦ hnef (Int32.toInt_inj.mp h')

-- Prove that the value increment can be move across the 'toInt' conversion
-- (as long as its value has not yet reached "finish")
theorem iterator_int32_toInt_val_inc {P : IteratorInt32Params}
  (iter : IteratorInt32 P) (hnef : iter.val ≠ P.finish) :
  (iter.val + P.inc).toInt = iter.val.toInt + P.inc.toInt := by
  have hleval' := Int32.le_iff_toInt_le.mp iter.hleval
  have hvalle' := Int32.le_iff_toInt_le.mp iter.hvalle
  have incnn := le_of_lt (Int32.lt_iff_toInt_lt.mp P.incpos)
  rw [int32_toInt_add_of_bounds]
  constructor
  · rw [← add_zero (-2 ^ 31), ← Int32.toInt_zero]
    exact Int.add_le_add (int32_minval_le_toInt iter.val) incnn
  · apply Int.lt_of_le_sub_one
    rw [← Int32.toInt_maxValue]
    apply le_trans (iterator_int32_val_add_inc_le_finish hnef)
    exact Int.le_sub_one_of_lt (int32_toInt_lt_maxval _)

-- Define a function for advancing an IteratorInt32
def iterator_int32_next {P : IteratorInt32Params}
  (iter : IteratorInt32 P) : IteratorInt32 P :=
  if h : iter.val = P.finish then iter else
  have incnn := le_of_lt (Int32.lt_iff_toInt_lt.mp P.incpos)
  {
    val := iter.val + P.inc
    hleval := by
      have hleval' := Int32.le_iff_toInt_le.mp iter.hleval
      apply Int32.le_iff_toInt_le.mpr
      rw [iterator_int32_toInt_val_inc _ h]
      rw [← add_zero P.start.toInt, ← Int32.toInt_zero]
      exact Int.add_le_add hleval' incnn
    hvalle := by
      have hvalle' := Int32.le_iff_toInt_le.mp iter.hvalle
      apply Int32.le_iff_toInt_le.mpr
      rw [iterator_int32_toInt_val_inc _ h]
      exact iterator_int32_val_add_inc_le_finish h
    hdvd := by
      rw [iterator_int32_toInt_val_inc _ h, add_sub_right_comm]
      apply Int.dvd_add
      · exact iter.hdvd
      · exact dvd_refl _
  }

theorem iterator_int32_next_val {P : IteratorInt32Params}
  (iter : IteratorInt32 P)
  (hnend : ¬iter = iterator_int32_end _) :
  (iterator_int32_next iter).val = iter.val + P.inc := by
  unfold iterator_int32_next
  rw [IteratorInt32.ext_iff] at hnend
  rw [iterator_int32_end_val] at hnend
  rw [dif_neg hnend]

theorem iterator_int32_next_val_toInt {P : IteratorInt32Params}
  (iter : IteratorInt32 P)
  (hnend : ¬iter = iterator_int32_end _) :
  (iterator_int32_next iter).val.toInt = iter.val.toInt + P.inc.toInt := by
  rw [iterator_int32_next_val iter hnend]
  rw [IteratorInt32.ext_iff, iterator_int32_end_val] at hnend
  rwa [iterator_int32_toInt_val_inc]

-- Equation for the value of an IteratorInt32 after iterating 'n' times
theorem iterator_int32_iterate_val {P : IteratorInt32Params}
  (iter : IteratorInt32 P) (n : ℕ) :
  (iterator_int32_next^[n] iter).val.toInt =
    min P.finish.toInt (iter.val.toInt + n * P.inc.toInt) := by
  match n with
  | 0 =>
    rw [Function.iterate_zero_apply]
    rw [Int.ofNat_zero, zero_mul, add_zero]
    exact (min_eq_right (Int32.le_iff_toInt_le.mp iter.hvalle)).symm
  | Nat.succ n' =>
    rw [Function.iterate_succ_apply]
    rw [iterator_int32_iterate_val]
    unfold iterator_int32_next
    split_ifs with h
    · rw [h, min_eq_left, min_eq_left]
      repeat {
      · apply Int.le_add_of_nonneg_right (Int.mul_nonneg _ _ )
        · exact Int.natCast_nonneg _
        · exact le_of_lt (Int32.lt_iff_toInt_lt.mp P.incpos) }
    · dsimp
      rw [iterator_int32_toInt_val_inc _ h, add_assoc, add_comm P.inc.toInt]
      rw [add_mul, one_mul]

theorem iterator_int32_val_eq_finish_iff
  {P : IteratorInt32Params} (iter : IteratorInt32 P) :
  iter.val = P.finish ↔ iter = iterator_int32_end _ := by
  rw [iter.ext_iff, iterator_int32_end_val]

instance {P : IteratorInt32Params} : Iterator (IteratorInt32 P) where
  Begin := iterator_int32_begin _
  End := iterator_int32_end _
  next := iterator_int32_next
  hend := by
    unfold iterator_int32_next iterator_int32_end; simp
  hbegin := by
    intro iter
    let n := (iter.val.toInt - P.start.toInt) / P.inc.toInt
    by_cases h : P.start.toInt = iter.val.toInt
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
        exact Int32.lt_iff_toInt_lt.mp P.incpos
      · exact iter.hdvd
    use n.natAbs
    apply IteratorInt32.ext (Int32.toInt_inj.mp _)
    rw [iterator_int32_iterate_val]
    rw [iterator_int32_begin_val]
    rw [Int.ofNat_natAbs_of_nonneg (le_of_lt npos)]
    unfold n
    rw [mul_comm]
    rw [Int.mul_ediv_cancel_of_dvd iter.hdvd]
    rw [add_sub_cancel, min_eq_right]
    exact Int32.le_iff_toInt_le.mp iter.hvalle

@[simp] theorem iterator_begin_of_iterator_int32 {P : IteratorInt32Params} :
  Iterator.Begin = iterator_int32_begin P := rfl

@[simp] theorem iterator_end_of_iterator_int32 {P : IteratorInt32Params} :
  Iterator.End = iterator_int32_end P := rfl
