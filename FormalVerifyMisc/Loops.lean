import FormalVerifyMisc.Int32.Basic

class SimpleLoopState (α : Type) where
  -- Variable to track our progress through the loop
  cur : α → Int32
  -- Amount by which to increment 'cur' on each iteration
  inc : α → Int32
  -- Upper bound for the loop
  -- The loop will exit if 'cur' ever meets or exceeds 'finish'
  finish : α → Int32
  -- Function for advancing the state
  adv : (s : α) → (cur s < finish s) → α
  -- 'inc' must be positive
  hpos : ∀ (s : α), 0 < (inc s)
  -- A proof that the loop execution will not exceed the 32-bit limit
  hsafe : ∀ (s : α), (finish s).toInt + (inc s).toInt ≤ Int32.maxValue.toInt
  -- Proof that 'adv' increments 'cur' as long as 'cur' < 'finish'
  hadv : ∀ s hlt, cur (adv s hlt) = cur s + inc s
  -- Proof that advancing the state doesn't change 'inc'
  hinc : ∀ s hlt, inc (adv s hlt) = inc s
  -- Proof that advancing the state doesn't change 'finish'
  hfinish : ∀ s hlt, finish (adv s hlt) = finish s

-- Map the 32-bit integers to the natural numbers
-- for the purpose of proving termination
def int32_toNat_for_term (i : Int32) : ℕ := (i.toInt + 2 ^ 31).natAbs

-- Converting a 32-bit integer to ℤ and adding 2^31 results in a non-negative value
lemma int32_toInt_add_maxValue_nonneg (i : Int32) :
  0 ≤ i.toInt + 2 ^ 31 := by
  apply Int.le_add_of_sub_right_le
  exact int32_minval_le_toInt i

-- Prove that the mapping from Int32 to ℕ preserves order
lemma int32_toNat_for_term_lt_iff (i j : Int32) :
  i < j ↔ int32_toNat_for_term i < int32_toNat_for_term j := by
  unfold int32_toNat_for_term
  have hrwi := Int.ofNat_natAbs_of_nonneg (int32_toInt_add_maxValue_nonneg i)
  have hrwj := Int.ofNat_natAbs_of_nonneg (int32_toInt_add_maxValue_nonneg j)
  constructor
  · intro hlt
    apply Int.lt_of_ofNat_lt_ofNat
    rw [hrwi, hrwj]
    exact Int.add_lt_add_right (Int32.lt_iff_toInt_lt.mp hlt) (2 ^ 31)
  · intro hlt
    apply Int32.lt_iff_toInt_lt.mpr
    apply Int.ofNat_lt_ofNat_of_lt at hlt
    rw [hrwi, hrwj] at hlt
    exact Int.lt_of_add_lt_add_right hlt

-- This result will be useful for proving that the loop terminates,
-- but will also be useful for clients of this code in proving that
-- loop state constraints are maintained.
theorem simple_loop_state_toInt_cur_add_inc {α : Type} [SimpleLoopState α] (s : α)
  (hlt : SimpleLoopState.cur s < SimpleLoopState.finish s) :
  (SimpleLoopState.cur s + SimpleLoopState.inc s).toInt =
  (SimpleLoopState.cur s).toInt + (SimpleLoopState.inc s).toInt := by
  have hpos : (0 : ℤ) < _ := Int32.lt_iff_toInt_lt.mp (SimpleLoopState.hpos s)
  rw [int32_toInt_add_of_bounds]
  constructor
  · exact Int.add_le_add (int32_minval_le_toInt _) (le_of_lt hpos)
  · have hlt' := Int32.lt_iff_toInt_lt.mp hlt
    let inc := SimpleLoopState.inc s
    apply lt_of_lt_of_le (Int.add_lt_add_right hlt' inc.toInt)
    apply le_trans (SimpleLoopState.hsafe s)
    rw [Int32.maxValue]; simp

-- Prove termination for 'do_simple_loop'
lemma simple_loop_term {α : Type} [SimpleLoopState α] (s : α)
  (hlt : SimpleLoopState.cur s < SimpleLoopState.finish s) :
  int32_toNat_for_term (SimpleLoopState.finish (SimpleLoopState.adv s hlt)) -
  int32_toNat_for_term (SimpleLoopState.cur (SimpleLoopState.adv s hlt)) <
  int32_toNat_for_term (SimpleLoopState.finish s) -
  int32_toNat_for_term (SimpleLoopState.cur s) := by
  have hpos : (0 : ℤ) < _ := Int32.lt_iff_toInt_lt.mp (SimpleLoopState.hpos s)
  rw [SimpleLoopState.hfinish s]
  apply Nat.sub_lt_sub_left ((int32_toNat_for_term_lt_iff _ _).mp hlt)
  rw [SimpleLoopState.hadv s]
  apply Int.lt_of_ofNat_lt_ofNat
  unfold int32_toNat_for_term
  repeat rw [Int.ofNat_natAbs_of_nonneg (int32_toInt_add_maxValue_nonneg _)]
  apply Int.add_lt_add_right
  rw [simple_loop_state_toInt_cur_add_inc _ hlt]
  apply (Int.add_zero _) ▸ (Int.add_lt_add_left hpos _)

def do_simple_loop {α : Type} [SimpleLoopState α] (s : α) : α :=
  if hlt : SimpleLoopState.cur s < SimpleLoopState.finish s then
  do_simple_loop (SimpleLoopState.adv s hlt) else s
termination_by
  int32_toNat_for_term (SimpleLoopState.finish s) -
  int32_toNat_for_term (SimpleLoopState.cur s)
decreasing_by
  exact simple_loop_term s hlt

-- Once the loop is complete, 'finish' ≤ 'cur'
theorem simple_loop_index_ge {α : Type} [SimpleLoopState α] (s : α) :
  SimpleLoopState.finish s ≤ SimpleLoopState.cur (do_simple_loop s) := by
  unfold do_simple_loop
  split_ifs with h
  · convert simple_loop_index_ge (SimpleLoopState.adv s h) using 1
    exact (SimpleLoopState.hfinish s h).symm
  · apply Int32.le_iff_toInt_le.mpr (Int.le_of_not_gt _)
    contrapose! h
    exact Int32.lt_iff_toInt_lt.mpr h
termination_by
  int32_toNat_for_term (SimpleLoopState.finish s) -
  int32_toNat_for_term (SimpleLoopState.cur s)
decreasing_by
  exact simple_loop_term s h

-- Prove that a property is true for the result of the loop
-- given that it is invariant across the loop and true of the
-- initial state.
theorem simple_loop_prop_const {α : Type} [SimpleLoopState α] (s : α)
  (prop : α → Prop) (base : prop s)
  (step : ∀ t hlt, prop t → prop (SimpleLoopState.adv t hlt)) :
  prop (do_simple_loop s) := by
  unfold do_simple_loop
  split_ifs with h
  · exact simple_loop_prop_const _ prop (step s h base) step
  · exact base
termination_by
  int32_toNat_for_term (SimpleLoopState.finish s) -
  int32_toNat_for_term (SimpleLoopState.cur s)
decreasing_by
  exact simple_loop_term s h

-- Elements which are unmodified by advancing the loop
-- are unmodifed by the full execution of the loop
-- This is a special case of 'prop_const' (above)
theorem simple_loop_val_const {α β : Type} [SimpleLoopState α] (s : α)
  (f : α → β) (hconst : ∀ t hlt, f (SimpleLoopState.adv t hlt) = f t) :
  f (do_simple_loop s) = f s := by
  let prop (t : α) : Prop := f t = f s
  have base : f s = f s := rfl
  apply simple_loop_prop_const s prop base
  unfold prop
  exact fun t hlt ht ↦ Eq.trans (hconst t hlt) ht

-- Specifically, 'finish' is unmodified by the loop's execution
@[simp] theorem simple_loop_finish_const {α : Type} [SimpleLoopState α] (s : α) :
  SimpleLoopState.finish (do_simple_loop s) = SimpleLoopState.finish s :=
  simple_loop_val_const s SimpleLoopState.finish SimpleLoopState.hfinish

-- Specifically, 'inc' is unmodified by the loop's execution
@[simp] theorem simple_loop_inc_const {α : Type} [SimpleLoopState α] (s : α) :
  SimpleLoopState.inc (do_simple_loop s) = SimpleLoopState.inc s :=
  simple_loop_val_const s SimpleLoopState.inc SimpleLoopState.hinc
