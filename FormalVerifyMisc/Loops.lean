import Mathlib.Tactic.Linarith
import FormalVerifyMisc.Int32.Basic

-- A loop which proves termination by mapping its state to decreasing natural numbers
class LoopBase (α : Type) where
  -- Indicates whether the loop has reached its terminal state
  term : α → Bool
  -- Advance the loop, given its state is not terminal
  adv : (s : α) → ¬term s → α
  -- A function mapping from α to ℕ - used to prove termination
  fdec : α → ℕ
  -- Proof that the value of 'fdec' decreases as 'adv' is called repeatedly
  hdec : ∀ s, (h : ¬term s) → fdec (adv s h) < fdec s

def do_loop {α : Type} [LoopBase α] (s : α) :=
  if h : LoopBase.term s then s else do_loop (LoopBase.adv s h)
termination_by LoopBase.fdec s
decreasing_by
  exact LoopBase.hdec s h

alias LoopReverse := LoopBase

-- Loop which continues until some parameter (of type 'β') exceeds some upper bound
-- 'β' is typically of type Int32, Int64, UInt32, or UInt64
class LoopForward (α : Type) (β : outParam Type) [LE β] where
  -- Upper bound for loop execution
  bound : α → β
  -- A map from the current loop state to β - used to check for termination
  finc : α → β
  -- Function for advancing the loop state
  fadv : (s : α) → ¬bound s ≤ finc s → α
  -- Proof that 'finc' increases as 'fadv' is called repeatedly
  hinc : ∀ s, (h : ¬bound s ≤ finc s) → ¬finc (fadv s h) ≤ finc s
  -- Proof that the bound doesn't change as 'fadv' is called
  hbound : ∀ s, (h : ¬bound s ≤ finc s) → bound (fadv s h) = bound s

-- A mapping from a type 'β' to the natural numbers
-- Used in proving loop termination
class TerminationParam (β : Type) [LE β] where
  embed : OrderEmbedding β ℕ

-- Mapping used to embed Int32 into the natural numbers
def int32_embed_toFun (i : Int32) := (i.toInt + 2^31).natAbs

-- Proves the result of embedding an Int32 into ℕ and then casting to ℤ
lemma int32_embed_toFun_toInt (i : Int32) : (int32_embed_toFun i) = i.toInt + 2^31 := by
  unfold int32_embed_toFun
  rw [Int.ofNat_natAbs_of_nonneg]
  apply Int.le_add_of_sub_right_le
  rw [zero_sub]
  exact int32_minval_le_toInt _

-- Prove that Int32 satisfies the requirements of a termination parameter
instance : TerminationParam Int32 where
  embed := {
    toFun := int32_embed_toFun
    inj' := by
      intro i j h
      apply Int.ofNat_inj.mpr at h
      rw [int32_embed_toFun_toInt, int32_embed_toFun_toInt] at h
      rwa [Int.add_left_inj, Int32.toInt_inj] at h
    map_rel_iff' := by
      intro a b; dsimp
      rw [← Int.ofNat_le]
      rw [int32_embed_toFun_toInt, int32_embed_toFun_toInt]
      rw [Int.add_le_add_iff_right, Int32.le_iff_toInt_le]
  }

-- Prove that a LoopForward' is also a 'LoopBase'
instance (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopForward α β] : LoopBase α where
  term := fun s ↦ decide (LoopForward.bound s ≤ LoopForward.finc s)
  adv := fun s h ↦ LoopForward.fadv s (by simp at h; assumption)
  fdec := fun s ↦
    TerminationParam.embed (LoopForward.bound s) -
    TerminationParam.embed (LoopForward.finc s)
  hdec := by
    intro s h
    simp only [decide_eq_true_eq] at h
    rw [LoopForward.hbound]
    by_contra! h'
    let embed : β ↪o ℕ := TerminationParam.embed
    by_cases hle :
      embed (LoopForward.finc (LoopForward.fadv s h)) ≤ embed (LoopForward.bound s)
    · apply LoopForward.hinc s h
      exact embed.map_rel_iff'.mp (Nat.le_of_sub_le_sub_left hle h')
    rename' hle => hlt; push_neg at hlt
    rw [Nat.sub_eq_zero_of_le (le_of_lt hlt)] at h'
    have hsubzero := Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero h')
    exact h (embed.map_rel_iff'.mp hsubzero)

-- A loop that advances by incrementing a 32-bit integer
class LoopIncI32 (α : Type) where
  -- Variable to track our progress through the loop
  cur : α → Int32
  -- Amount by which to increment 'cur' on each iteration
  inc : α → Int32
  -- Upper bound for the loop
  -- The loop will exit if 'cur' ever meets or exceeds 'finish'
  finish : α → Int32
  -- Function for advancing the state
  adv : (s : α) → cur s < finish s → α
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

-- 'i + inc' can be moved across the 'toInt' conversion if 'i' ≤ 'finish'
lemma loop_incI32_toInt_val_add_inc {α : Type} [LoopIncI32 α] (s : α)
  (i : Int32) (h : i ≤ LoopIncI32.finish s) :
  (i + LoopIncI32.inc s).toInt =
  i.toInt + (LoopIncI32.inc s).toInt := by
  have incpos := Int32.lt_iff_toInt_lt.mp (LoopIncI32.hpos s)
  apply int32_toInt_add_of_bounds
  constructor
  · exact Int.add_le_add (int32_minval_le_toInt _) (le_of_lt incpos)
  · apply Int.lt_of_le_sub_one
    rw [← Int32.toInt_maxValue]
    apply le_trans (Int.add_le_add_right _ _) (LoopIncI32.hsafe s)
    exact Int32.le_iff_toInt_le.mp h

-- In particular, 'cur + inc' can be moved across the 'toInt' conversion
lemma loop_incI32_toInt_cur_add_inc {α : Type} [LoopIncI32 α] (s : α)
  (h : ¬LoopIncI32.finish s ≤ LoopIncI32.cur s) :
  (LoopIncI32.cur s + LoopIncI32.inc s).toInt =
  (LoopIncI32.cur s).toInt + (LoopIncI32.inc s).toInt := by
  apply loop_incI32_toInt_val_add_inc
  exact Int32.le_of_lt (Int32.not_le.mp h)

-- In particular, 'finish + inc' can be moved across the 'toInt' conversion
lemma loop_incI32_toInt_finish_add_inc {α : Type} [LoopIncI32 α] (s : α) :
  (LoopIncI32.finish s + LoopIncI32.inc s).toInt =
  (LoopIncI32.finish s).toInt + (LoopIncI32.inc s).toInt := by
  apply loop_incI32_toInt_val_add_inc
  exact Int32.le_refl _

-- Prove that a 'LoopIncI32' is a 'LoopForward'
instance (α : Type) [LoopIncI32 α] : LoopForward α Int32 where
  bound := LoopIncI32.finish
  finc := LoopIncI32.cur
  fadv := fun s h ↦ LoopIncI32.adv s (Int32.not_le.mp h)
  hinc := by
    intro s h
    rw [LoopIncI32.hadv, Int32.not_le]
    have incpos := Int32.lt_iff_toInt_lt.mp (LoopIncI32.hpos s)
    have := Int.add_lt_add_left incpos (LoopIncI32.cur s).toInt
    rw [Int32.toInt_zero, add_zero] at this
    apply Int32.lt_iff_toInt_lt.mpr
    rwa [loop_incI32_toInt_cur_add_inc s h]
  hbound := fun s h ↦ LoopIncI32.hfinish s (Int32.not_le.mp h)

-- If a property of the loop state is constant across calls to 'adv'
-- it will be constant over the full execution of the loop
theorem loop_prop_const {α : Type} [LoopBase α] (s : α)
  (prop : α → Prop) (base : prop s)
  (step : ∀ t hlt, prop t → prop (LoopBase.adv t hlt)) :
  prop (do_loop s) := by
  unfold do_loop
  split_ifs with h
  · exact base
  · apply loop_prop_const _ _ _ step
    exact step s h base
termination_by LoopBase.fdec s
decreasing_by
  exact LoopBase.hdec s h

-- If a value in the loop state is constant across calls to 'adv'
-- it will be constant over the full execution of the loop
theorem loop_val_const {α β : Type} [LoopBase α] (s : α)
  (f : α → β) (hconst : ∀ t hlt, f (LoopBase.adv t hlt) = f t) :
  f (do_loop s) = f s := by
  -- Prove this as a special case of 'loop_prop_const'
  let prop : α → Prop := fun t ↦ f t = f s
  have base : prop s := rfl
  have step : ∀ t hlt, prop t → prop (LoopBase.adv t hlt) := by
    intro t hlt
    unfold prop
    rw [hconst t hlt]
    exact id
  exact loop_prop_const s prop base step

-- After loop execution is complete,
-- the termination requirement has been met
theorem loop_term {α : Type} [LoopBase α] (s : α) :
  LoopBase.term (do_loop s) := by
  unfold do_loop
  split_ifs with h
  · assumption
  · apply loop_term
termination_by LoopBase.fdec s
decreasing_by
  exact LoopBase.hdec s h

-- The upper bound for a forward loop does not change over its execution
@[simp] theorem loop_forward_bound_const (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopForward α β] (s : α) :
  LoopForward.bound (do_loop s) = LoopForward.bound s := by
  apply loop_val_const
  intro t h
  simp only [LoopBase.term, decide_eq_true_eq] at h
  exact LoopForward.hbound t h

-- After the execution of a forward loop,
-- the termination parameter will have exceeded the bound
theorem loop_forward_bound_le (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopForward α β] (s : α) :
  LoopForward.bound s ≤ LoopForward.finc (do_loop s) := by
  have := loop_term s
  simp only [LoopBase.term, decide_eq_true_eq] at this
  rwa [loop_forward_bound_const] at this

-- 'finish' is unmodified by the loop's execution
@[simp] theorem loop_incI32_finish_const {α : Type} [LoopIncI32 α] (s : α) :
  LoopIncI32.finish (do_loop s) = LoopIncI32.finish s := by
  apply loop_val_const; intros
  apply LoopIncI32.hfinish

-- 'inc' is unmodified by the loop's execution
@[simp] theorem loop_incI32_inc_const {α : Type} [LoopIncI32 α] (s : α) :
  LoopIncI32.inc (do_loop s) = LoopIncI32.inc s := by
  apply loop_val_const; intros
  apply LoopIncI32.hinc

-- After loop execution, cur < finish + inc,
-- if before loop execution cur < finish
theorem loop_incI32_term_param_lt_of_lt {α : Type} [LoopIncI32 α] (s : α)
  (curlt : LoopIncI32.cur s < LoopIncI32.finish s) :
  LoopIncI32.cur (do_loop s) < LoopIncI32.finish s + LoopIncI32.inc s := by
  have incpos := Int32.lt_iff_toInt_lt.mp (LoopIncI32.hpos s)
  let prop (t : α) : Prop :=
    LoopIncI32.cur t < LoopIncI32.finish t + LoopIncI32.inc t
  have base : prop s := by
    unfold prop
    apply Int32.lt_iff_toInt_lt.mpr
    rw [loop_incI32_toInt_finish_add_inc]
    apply lt_trans (Int32.lt_iff_toInt_lt.mp curlt)
    exact Int.lt_add_of_pos_right _ incpos
  have step : ∀ t h, prop t → prop (LoopIncI32.adv t h) := by
    unfold prop
    intro t hterm curlt'
    rw [LoopIncI32.hadv]
    apply Int32.lt_iff_toInt_lt.mpr
    rw [loop_incI32_toInt_finish_add_inc]
    rw [loop_incI32_toInt_cur_add_inc _ (Int32.not_le.mpr hterm)]
    rw [LoopIncI32.hfinish, LoopIncI32.hinc]
    exact Int.add_lt_add_right (Int32.lt_iff_toInt_lt.mp hterm) _
  rw [← loop_incI32_finish_const, ← loop_incI32_inc_const]
  apply loop_prop_const _ prop base _
  intro t hterm hpt
  simp only [LoopBase.term, decide_eq_true_eq] at hterm
  exact step t (Int32.not_le.mp hterm) hpt

/-class SimpleLoopState (α : Type) where
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

-- The addition of 'finish' and 'inc' can be carried across the 'toInt' conversion
theorem simple_loop_state_toInt_finish_add_inc {α : Type} [SimpleLoopState α] (s : α) :
  (SimpleLoopState.finish s + SimpleLoopState.inc s).toInt =
  (SimpleLoopState.finish s).toInt + (SimpleLoopState.inc s).toInt := by
  have hpos : (0 : ℤ) < _ := Int32.lt_iff_toInt_lt.mp (SimpleLoopState.hpos s)
  convert int32_toInt_add_of_bounds _ _ _
  constructor
  · have ltfin := int32_minval_le_toInt (SimpleLoopState.finish s)
    linarith [ltfin, hpos]
  · apply lt_of_le_of_lt (SimpleLoopState.hsafe s)
    unfold Int32.maxValue; simp

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

-- If the initial value of 'cur' is less than 'finish', the final
-- value will be less than 'finish' + 'inc'
theorem simple_loop_index_lt_of_lt {α : Type} [SimpleLoopState α] (s : α)
  (curlt : SimpleLoopState.cur s < SimpleLoopState.finish s) :
  (fun t ↦ SimpleLoopState.cur t < SimpleLoopState.finish t + SimpleLoopState.inc t)
    (do_simple_loop s) := by
  let prop : α → Prop :=
    fun t ↦ SimpleLoopState.cur t < SimpleLoopState.finish t + SimpleLoopState.inc t
  have base : prop s := by
    unfold prop
    apply Int32.lt_trans curlt
    apply Int32.lt_iff_toInt_lt.mpr
    rw [simple_loop_state_toInt_finish_add_inc]
    have hpos : (0 : ℤ) < _ := Int32.lt_iff_toInt_lt.mp (SimpleLoopState.hpos s)
    convert (Int.add_zero _) ▸ (Int.add_lt_add_left hpos _)
  have step : ∀ t hlt, prop t → prop (SimpleLoopState.adv t hlt) := by
    unfold prop
    intro t hlt h
    rw [SimpleLoopState.hadv, SimpleLoopState.hfinish, SimpleLoopState.hinc]
    apply Int32.lt_iff_toInt_lt.mpr
    rw [simple_loop_state_toInt_finish_add_inc]
    rw [simple_loop_state_toInt_cur_add_inc _ hlt]
    exact Int.add_lt_add_right (Int32.lt_iff_toInt_lt.mp hlt) _
  exact simple_loop_prop_const _ prop base step-/
