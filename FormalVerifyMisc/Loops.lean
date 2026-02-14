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
  adv : α → α
  -- 'inc' must be positive
  hpos : ∀ (s : α), 0 < (inc s)
  -- A proof that the loop execution will not exceed the 32-bit limit
  hsafe : ∀ (s : α), (finish s).toInt + (inc s).toInt ≤ Int32.maxValue.toInt
  -- Proof that 'adv' increments 'cur' as expected
  hadv : ∀ (s : α), cur (adv s) = cur s + inc s
  -- Proof that advancing the state doesn't change 'finish'
  hconst : ∀ (s : α), finish (adv s) = finish s

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

def do_simple_loop {α : Type} [SimpleLoopState α] (s : α) : α :=
  if SimpleLoopState.cur s < SimpleLoopState.finish s then
  do_simple_loop (SimpleLoopState.adv s) else s
termination_by
  int32_toNat_for_term (SimpleLoopState.finish s) -
  int32_toNat_for_term (SimpleLoopState.cur s)
decreasing_by
  have hpos : (0 : ℤ) < _ := Int32.lt_iff_toInt_lt.mp (SimpleLoopState.hpos s)
  rename SimpleLoopState.cur s < _ => hlt
  rw [SimpleLoopState.hconst s]
  apply Nat.sub_lt_sub_left ((int32_toNat_for_term_lt_iff _ _).mp hlt)
  rw [SimpleLoopState.hadv s]
  apply Int.lt_of_ofNat_lt_ofNat
  unfold int32_toNat_for_term
  repeat rw [Int.ofNat_natAbs_of_nonneg (int32_toInt_add_maxValue_nonneg _)]
  apply Int.add_lt_add_right
  rw [int32_toInt_add_of_bounds]
  · apply (Int.add_zero _) ▸ (Int.add_lt_add_left hpos _)
  constructor
  · exact Int.add_le_add (int32_minval_le_toInt _) (le_of_lt hpos)
  · have hlt' := Int32.lt_iff_toInt_lt.mp hlt
    let inc := SimpleLoopState.inc s
    apply lt_of_lt_of_le (Int.add_lt_add_right hlt' inc.toInt)
    apply le_trans (SimpleLoopState.hsafe s)
    rw [Int32.maxValue]; simp
