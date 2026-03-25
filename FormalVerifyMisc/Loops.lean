import FormalVerifyMisc.Int32.Basic
import FormalVerifyMisc.Iterator

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

-- Loop which proves termination based on some parameter (of type 'β')
-- which is always decreasing but never falls below some lower bound
-- 'β' is typically of type Int32, Int64, UInt32, or UInt64
class LoopReverse (α : Type) (β : outParam Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)] where
  -- A function to determine termination
  term : α → Bool
  -- A map from the current loop state to β - used to prove termination
  fdec : α → β
  -- Function for advancing the loop state
  fadv : (s : α) → ¬term s → α
  -- Proof that 'fdec' decreases as 'fadv' is called repeatedly
  hdec : ∀ s h, ¬fdec s ≤ fdec (fadv s h)

-- Loop which proves termination based on some parameter (of type 'β')
-- which is always increasing but never exceeds some upper bound
-- 'β' is typically of type Int32, Int64, UInt32, or UInt64
class LoopForward (α : Type) (β : outParam Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)] where
  -- Upper bound used to prove loop termination
  bound : α → β
  -- A function to determine termination
  term : α → Bool
  -- A map from the current loop state to β
  finc : α → β
  -- Function for advancing the loop state
  fadv : (s : α) → ¬term s = true → α
  -- Proof that 'finc' increases as 'fadv' is called repeatedly
  hinc : ∀ s h, ¬finc (fadv s h) ≤ finc s
  -- Proof that 'finc' never exceeds 'bound'
  hle : ∀ s, finc s ≤ bound s
  -- Proof that the bound doesn't change as 'fadv' is called
  hbound : ∀ s h, bound (fadv s h) = bound s

-- A mapping from a type 'β' to the natural numbers
-- Used in proving loop termination
class TerminationParam (β : Type) [LE β] where
  embed : OrderEmbedding β ℕ

theorem tp_le_refl {β : Type} [LE β] [TerminationParam β] {b : β} : b ≤ b := by
  apply TerminationParam.embed.map_rel_iff.mp
  exact le_refl _

-- Prove 'le_trans' for termination parameters based on the embedding in ℕ
theorem tp_le_trans {β : Type} [LE β] [TerminationParam β] {a b c : β} :
  a ≤ b → b ≤ c → a ≤ c := by
  intro h₀ h₁
  apply TerminationParam.embed.map_rel_iff.mp
  apply le_trans (TerminationParam.embed.map_rel_iff.mpr h₀)
  exact TerminationParam.embed.map_rel_iff.mpr h₁

-- Prove 'le_antisymm' for termination parameters based on the embedding in ℕ
theorem tp_le_antisymm {β : Type} [LE β] [TerminationParam β] {a b : β} :
  a ≤ b → b ≤ a → a = b := by
  intro h₀ h₁
  apply TerminationParam.embed.inj.mp
  apply le_antisymm (TerminationParam.embed.map_rel_iff.mpr h₀)
  exact TerminationParam.embed.map_rel_iff.mpr h₁

-- Prove a variant of 'lt_of_le_of_ne' for termination parameters
-- based on the embedding in ℕ
theorem tp_lt_of_le_of_ne {β : Type} [LE β] [TerminationParam β] {a b : β} :
  a ≤ b → a ≠ b → ¬b ≤ a := by
  intro h₀ h₁
  contrapose h₁
  exact tp_le_antisymm h₀ h₁

-- This theorem has no analogue in the natural numbers but is useful
-- for termination parameters because we only assume '≤' is defined but not '<'
-- Proof is based on the embedding in ℕ
theorem tp_ge_of_not_le {β : Type} [LE β] [TerminationParam β] {a b : β} :
  ¬a ≤ b → b ≤ a := by
  intro nle
  apply TerminationParam.embed.map_rel_iff.mp
  contrapose! nle
  apply TerminationParam.embed.map_rel_iff.mp
  exact le_of_lt nle

-- A termination parameter with an increment function
class TermParamInc (β : Type) [LE β] extends TerminationParam β where
  -- Function for incrementing the parameter
  adv : β → β
  -- Maximum value of β - calling 'adv' on this value is not well-behaved
  -- TODO: This seems to rule out non-finite parameter types
  -- (such as a BigInt), but for now I don't see a way to get
  -- that to work within the existing class hierarchy.
  maxVal : β
  -- Proof that the increment carries across the embedding to ℕ
  hadv (b : β) (hnle : ¬maxVal ≤ b) : embed (adv b) = embed b + 1
  -- All elements of type β are less than or equal to 'maxVal'
  hlemv : ∀ b, b ≤ maxVal

-- Prove a variant of 'lt_of_add_one_le' for termination parameters
-- based on the embedding in ℕ
theorem tpi_lt_of_add_one_le {β : Type} [LE β] [TermParamInc β] {a b : β}
  (hltmax : ¬TermParamInc.maxVal ≤ a) :
  TermParamInc.adv a ≤ b → ¬b ≤ a := by
  intro h
  apply TerminationParam.embed.map_rel_iff.mpr at h
  rw [TermParamInc.hadv _ hltmax] at h
  apply Nat.lt_of_add_one_le at h
  contrapose! h
  exact TerminationParam.embed.map_rel_iff.mpr h

-- Prove a variant of 'add_one_le_of_lt' for termination parameters
-- based on the embedding in ℕ
theorem tpi_add_one_le_of_lt {β : Type} [LE β] [TermParamInc β] {a b : β}
  (hltmax : ¬TermParamInc.maxVal ≤ a) :
  ¬b ≤ a → TermParamInc.adv a ≤ b := by
  intro h
  apply TerminationParam.embed.map_rel_iff.mp
  rw [TermParamInc.hadv _ hltmax]
  apply Nat.add_one_le_of_lt
  contrapose! h
  exact TerminationParam.embed.map_rel_iff.mp h

-- Prove a variant of 'lt_add_one' for termination parameters
-- based on the embedding in ℕ
theorem tpi_lt_add_one {β : Type} [LE β] [TermParamInc β] {a : β}
  (hltmax : ¬TermParamInc.maxVal ≤ a) : ¬TermParamInc.adv a ≤ a := by
  rw [← TerminationParam.embed.map_rel_iff, TermParamInc.hadv _ hltmax]
  push_neg
  exact Nat.lt_add_one _

-- Prove that a LoopReverse' is also a 'LoopBase'
instance (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopReverse α β] : LoopBase α where
  term := LoopReverse.term
  adv := LoopReverse.fadv
  fdec := fun s ↦ TerminationParam.embed (LoopReverse.fdec s)
  hdec := by
    intro s h
    by_contra! h'
    exact LoopReverse.hdec s h (TerminationParam.embed.map_rel_iff'.mp h')

-- Prove that a LoopForward' is also a 'LoopBase'
instance (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopForward α β] : LoopBase α where
  term := LoopForward.term
  adv := LoopForward.fadv
  fdec := fun s ↦
    TerminationParam.embed (LoopForward.bound s) -
    TerminationParam.embed (LoopForward.finc s)
  hdec := by
    intro s h
    rw [LoopForward.hbound]
    by_contra! h'
    let embed : β ↪o ℕ := TerminationParam.embed
    apply LoopForward.hinc s h
    apply embed.map_rel_iff.mp (Nat.le_of_sub_le_sub_left _ h')
    convert embed.map_rel_iff.mpr (LoopForward.hle (LoopForward.fadv s h)) using 1
    rw [LoopForward.hbound]

-- The upper bound for a forward loop does not change over its execution
@[simp] theorem loop_forward_bound_const (α β : Type)
  [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
  [TerminationParam β] [LoopForward α β] (s : α) :
  LoopForward.bound (do_loop s) = LoopForward.bound s := by
  apply loop_val_const
  exact LoopForward.hbound

-- Parameters for a search loop
-- The loop will find the first value of type α which satisfies 'f'
structure LoopSearchParams (α : Type) [LE α] [TermParamInc α] where
  start : α
  finish : α
  f : α → Bool
  hsle : start ≤ finish
  hfle : finish ≤ TermParamInc.maxVal
  hsat : f finish

-- Current state of a search loop
structure LoopSearch {α : Type} [LE α] [TermParamInc α]
  (P : LoopSearchParams α) where
  cur : α
  hle : cur ≤ P.finish

-- 'LoopSearch' corresponding to the start of the search
def init_search {α : Type} [LE α] [TermParamInc α]
  (P : LoopSearchParams α) : LoopSearch P where
  cur := P.start
  hle := P.hsle

-- Prove that the current search state satisfies the search requirements
-- assuming the termination parameter has reached 'finish'
lemma loop_search_sat_of_finish_le {α : Type} [LE α]
  [TermParamInc α] {P : LoopSearchParams α}
  {s : LoopSearch P} (h : P.finish ≤ s.cur) : P.f s.cur = true := by
  rw [tp_le_antisymm s.hle h]
  exact P.hsat

-- Prove that the current search state satisfies the search requirements
-- assuming the termination parameter has reached its maximum value
lemma loop_search_sat_of_maxval_le {α : Type} [LE α]
  [TermParamInc α] {P : LoopSearchParams α}
  {s : LoopSearch P} (h : TermParamInc.maxVal ≤ s.cur) : P.f s.cur = true := by
  apply loop_search_sat_of_finish_le
  exact tp_le_trans P.hfle h

lemma term_param_lt_max_of_not_term {α : Type} [LE α]
  [TermParamInc α] {P : LoopSearchParams α}
  {s : LoopSearch P} (hterm : ¬P.f s.cur = true) :
  ¬TermParamInc.maxVal ≤ s.cur := by
  contrapose! hterm
  exact loop_search_sat_of_maxval_le hterm

-- Prove that we can advance the termination parameter
-- based on its embedding into the natural numbers
lemma term_param_inc_adv_of_loop_search {α : Type} [LE α]
  [TermParamInc α] {P : LoopSearchParams α}
  {s : LoopSearch P} (hterm : ¬P.f s.cur = true) :
  TerminationParam.embed (TermParamInc.adv s.cur) =
  TerminationParam.embed (s.cur) + 1 :=
  TermParamInc.hadv _ (term_param_lt_max_of_not_term hterm)

-- Define the advancement function for 'LoopSearch'
def loop_search_advance {α : Type} [LE α]
  [DecidableRel (· ≤ · : α → α → Prop)] [TermParamInc α] {P : LoopSearchParams α}
  (s : LoopSearch P) (hterm : ¬P.f s.cur = true) : LoopSearch P where
  cur := TermParamInc.adv s.cur
  -- Use the embedding into ℕ to prove that the termination bound is not exceeded
  hle := by
    apply tpi_add_one_le_of_lt <;> contrapose! hterm
    · exact loop_search_sat_of_maxval_le hterm
    · exact loop_search_sat_of_finish_le hterm

lemma loop_search_advance_cur {α : Type} [LE α]
  [DecidableRel (· ≤ · : α → α → Prop)] [TermParamInc α] {P : LoopSearchParams α}
  (s : LoopSearch P) (hterm : ¬P.f s.cur = true) :
  (loop_search_advance s hterm).cur = TermParamInc.adv s.cur := rfl

-- Prove that 'LoopSearch' is a ForwardLoop
instance (α : Type)
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {P : LoopSearchParams α} : LoopForward (LoopSearch P) α where
  bound := fun _ ↦ P.finish
  term := fun s ↦ P.f s.cur
  finc := LoopSearch.cur
  fadv := loop_search_advance
  hinc := by
    intro s hterm
    rw [loop_search_advance_cur]
    apply tpi_lt_add_one
    contrapose! hterm
    exact loop_search_sat_of_maxval_le hterm
  hle := LoopSearch.hle
  hbound := fun _ _ ↦ rfl

-- Perform a search, given the search parameters
def do_search {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  (P : LoopSearchParams α) : α :=
  (do_loop (init_search P)).cur

-- The result of the search will satisfy P.f
theorem loop_search_sat {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  (P : LoopSearchParams α) :
  P.f (do_search P) := loop_term (init_search P)

-- The result of the search will be the first after P.start to satisfy P.f
theorem loop_search_first {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  (P : LoopSearchParams α) :
  ∀ a : α, P.f a → P.start ≤ a → do_search P ≤ a := by
  intro a hsat lea
  by_contra h
  let prop (s : LoopSearch P) : Prop :=
    ∀ a : α, P.start ≤ a → ¬s.cur ≤ a → ¬P.f a
  have base : prop (init_search P) := by
    intro a lea alt
    contradiction
  have step : ∀ t hterm, prop t → prop (LoopBase.adv t hterm) := by
    intro t hterm hprop a lea alt
    change ¬P.f t.cur at hterm
    change ¬TermParamInc.adv t.cur ≤ a at alt
    let embed : α ↪o ℕ := TerminationParam.embed
    contrapose! alt
    apply tpi_add_one_le_of_lt
    · contrapose! hterm
      exact loop_search_sat_of_maxval_le hterm
    have nea : t.cur ≠ a := by
      contrapose! hterm
      rwa [hterm]
    apply tp_lt_of_le_of_ne _ nea
    by_contra! h
    exact False.elim (hprop a lea h alt)
  have := loop_prop_const (init_search P) prop base step
  exact False.elim (this a lea h hsat)

-- The termination parameter returned by the search will be
-- greater than or equal to the starting point of the search
theorem loop_search_ge {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  (P : LoopSearchParams α) :
  P.start ≤ do_search P := by
  let prop (s : LoopSearch P) : Prop :=
    P.start ≤ s.cur
  have base : prop (init_search P) := tp_le_refl
  have step : ∀ t hterm, prop t → prop (LoopBase.adv t hterm) := by
    unfold prop
    intro t hterm hprop
    change ¬P.f t.cur at hterm
    change P.start ≤ TermParamInc.adv t.cur
    have ltmax := term_param_lt_max_of_not_term hterm
    exact tp_le_trans hprop (tp_ge_of_not_le (tpi_lt_add_one ltmax))
  exact loop_prop_const (init_search P) prop base step

-- The termination parameter returned by the search will be
-- less than or equal to the ending point of the search
theorem loop_search_le {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  (P : LoopSearchParams α) :
  do_search P ≤ P.finish := by
  let prop (s : LoopSearch P) : Prop :=
    s.cur ≤ P.finish
  have base : prop (init_search P) := P.hsle
  have step : ∀ t hterm, prop t → prop (LoopBase.adv t hterm) := by
    unfold prop
    intro t hterm hprop
    change ¬P.f t.cur at hterm
    change TermParamInc.adv t.cur ≤ P.finish
    have ltmax := term_param_lt_max_of_not_term hterm
    apply tpi_add_one_le_of_lt ltmax
    contrapose! hterm
    rw [tp_le_antisymm hprop hterm]
    exact P.hsat
  exact loop_prop_const (init_search P) prop base step

-- Define the parameters for a search based on an existential statement
def search_ex_params {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) : LoopSearchParams α where
  start := start
  finish := finish
  f := fun b ↦ decide (f b = true ∨ finish ≤ b)
  hsle := by
    rcases h with ⟨a, sle, lef, h⟩
    exact tp_le_trans sle lef
  hfle := TermParamInc.hlemv finish
  hsat := by
    simp only [decide_eq_true_eq]
    exact Or.inr tp_le_refl

-- Search for the first instance of α in a range that satisfies
-- some f : α → Bool, given a statement that such an α exists
def do_search_ex {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) : α :=
  do_search (search_ex_params h)

-- Prove that the result of the search satisfies the search
theorem loop_search_ex_sat {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) :
  f (do_search_ex h) = true := by
  let P := search_ex_params h
  have : P.f (do_search_ex h) = true := loop_search_sat _
  unfold P search_ex_params at this; dsimp at this
  unfold do_search_ex
  unfold do_search_ex at this
  simp only [decide_eq_true_eq] at this
  rcases this with lhs | rhs
  · assumption
  rcases h with ⟨a, lea, ale, ha⟩
  have ha' : P.f a = true := by
    unfold P search_ex_params; dsimp
    rw [decide_eq_true_eq]
    exact Or.inl ha
  convert ha
  apply tp_le_antisymm (loop_search_first P a ha' lea)
  exact tp_le_trans ale rhs

-- The result of the search will be the first value after 'start' to satisfy 'f'
theorem loop_search_ex_first {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) :
  ∀ a : α, f a → start ≤ a → do_search_ex h ≤ a := by
  intro a ha lea
  unfold do_search_ex
  unfold search_ex_params
  apply loop_search_first <;> dsimp
  · simp only [decide_eq_true_eq]
    exact Or.inl ha
  · exact lea

-- The termination parameter returned by the search will be
-- greater than or equal to the starting point of the search
theorem loop_search_ex_ge {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) :
  start ≤ do_search_ex h := by
  unfold do_search_ex
  convert loop_search_ge (search_ex_params h)

-- The termination parameter returned by the search will be
-- less than or equal to the ending point of the search
theorem loop_search_ex_le {α : Type}
  [LE α] [TermParamInc α] [DecidableRel (· ≤ · : α → α → Prop)]
  {start finish : α} {f : α → Bool}
  (h : ∃ a, start ≤ a ∧ a ≤ finish ∧ f a = true) :
  do_search_ex h ≤ finish := by
  unfold do_search_ex
  convert loop_search_le (search_ex_params h)

-- Define a loop which uses an iterator
class LoopIterator (α : Type) (β : outParam Type) [DecidableEq β] [Iterator β] where
  iter : α → β
  adv : (s : α) → (¬iter s = Iterator.End) → α
  hadv : ∀ s h, iter (adv s h) = Iterator.next (iter s)

-- Prove that 'LoopIterator' meets the requirements of LoopBase
instance (α β : Type) [DecidableEq β] [Iterator β] [LoopIterator α β] : LoopBase α where
  term := fun s ↦ (LoopIterator.iter s) = Iterator.End
  adv := fun s h ↦ LoopIterator.adv s (by rwa [decide_eq_true_eq] at h)
  fdec := fun s ↦ Nat.find (iterate_eq_end (LoopIterator.iter s))
  hdec := by
    intro s h
    rw [decide_eq_true_eq] at h
    rw [← Nat.add_one_lt_add_one_iff]
    convert Nat.lt_add_one _
    convert Nat.find_comp_succ _ _ _ using 1
    · rw [Nat.add_one_inj]
      apply Nat.find_congr'
      intro n
      rw [LoopIterator.hadv, Function.iterate_succ_apply]
    · rcases iterate_eq_end (LoopIterator.iter s) with ⟨n, hn⟩
      use n;
      rw [Function.iterate_succ_apply', hn, Iterator.hend]
    · rwa [Function.iterate_zero, id]

@[simp] theorem loop_base_term_of_loop_iterator
  (α β : Type) [DecidableEq β] [Iterator β] [LoopIterator α β] (s : α) :
  LoopBase.term s = decide (LoopIterator.iter s = Iterator.End) := rfl

@[simp] theorem loop_base_adv_of_loop_iterator
  (α β : Type) [DecidableEq β] [Iterator β] [LoopIterator α β]
  (s : α) (hterm : ¬LoopBase.term s) :
  LoopBase.adv s hterm = LoopIterator.adv s (by
    simp only [loop_base_term_of_loop_iterator, decide_eq_true_eq] at hterm
    assumption
  ) := rfl

-- Mapping used to embed Int32 into the natural numbers
def int32_embed_toFun (i : Int32) := (i.toInt + 2^31).natAbs

-- Proves the result of embedding an Int32 into ℕ and then casting to ℤ
lemma int32_embed_toFun_toInt (i : Int32) : (int32_embed_toFun i) = i.toInt + 2^31 := by
  unfold int32_embed_toFun
  rw [Int.ofNat_natAbs_of_nonneg]
  apply Int.le_add_of_sub_right_le
  rw [zero_sub]
  exact int32_minval_le_toInt _

-- Prove that Int32 satisfies the requirements of a termination parameter with increment
instance : TermParamInc Int32 where
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
  adv := fun i ↦ i + 1
  maxVal := Int32.maxValue
  hadv := by
    intro i h; dsimp
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.ofNat_one]
    rw [int32_embed_toFun_toInt, int32_embed_toFun_toInt]
    rw [add_right_comm, int32_toInt_succ]
    exact Int32.not_le.mp h
  hlemv := Int32.le_maxValue

-- A loop that advances by incrementing a 32-bit integer
-- TODO: This seems obsolete. Consider removing it
class LoopIncI32 (α : Type) where
  -- Variable to track our progress through the loop
  cur : α → Int32
  -- Amount by which to increment 'cur' on each iteration
  inc : α → Int32
  -- Upper bound for the loop
  -- The loop will exit if 'cur' ever meets or exceeds 'finish'
  finish : α → Int32
  -- Function for advancing the state
  adv : (s : α) → ¬decide (finish s ≤ cur s) = true → α
  -- 'inc' must be positive
  hpos : ∀ (s : α), 0 < (inc s)
  -- 'cur' must be no greater than 'finish' + 'inc'
  hle : ∀ s, cur s ≤ finish s + inc s
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
  (h : LoopIncI32.cur s < LoopIncI32.finish s) :
  (LoopIncI32.cur s + LoopIncI32.inc s).toInt =
  (LoopIncI32.cur s).toInt + (LoopIncI32.inc s).toInt := by
  apply loop_incI32_toInt_val_add_inc
  exact Int32.le_of_lt h

-- In particular, 'finish + inc' can be moved across the 'toInt' conversion
lemma loop_incI32_toInt_finish_add_inc {α : Type} [LoopIncI32 α] (s : α) :
  (LoopIncI32.finish s + LoopIncI32.inc s).toInt =
  (LoopIncI32.finish s).toInt + (LoopIncI32.inc s).toInt := by
  apply loop_incI32_toInt_val_add_inc
  exact Int32.le_refl _

-- Prove that a 'LoopIncI32' is a 'LoopForward'
instance (α : Type) [LoopIncI32 α] : LoopForward α Int32 where
  bound := fun s ↦ LoopIncI32.finish s + LoopIncI32.inc s
  term := fun s ↦ LoopIncI32.finish s ≤ LoopIncI32.cur s
  finc := LoopIncI32.cur
  fadv := fun s h ↦ LoopIncI32.adv s h
  hinc := by
    intro s h
    simp only [decide_eq_true_eq, Int32.not_le] at h
    rw [LoopIncI32.hadv, Int32.not_le]
    have incpos := Int32.lt_iff_toInt_lt.mp (LoopIncI32.hpos s)
    have := Int.add_lt_add_left incpos (LoopIncI32.cur s).toInt
    rw [Int32.toInt_zero, add_zero] at this
    apply Int32.lt_iff_toInt_lt.mpr
    rwa [loop_incI32_toInt_cur_add_inc s h]
  hle := LoopIncI32.hle
  hbound := by
    intro s h
    rw [LoopIncI32.hfinish, LoopIncI32.hinc]

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
    simp only [decide_eq_true_eq, Int32.not_le] at hterm
    rw [LoopIncI32.hadv]
    apply Int32.lt_iff_toInt_lt.mpr
    rw [loop_incI32_toInt_finish_add_inc]
    rw [loop_incI32_toInt_cur_add_inc _ hterm]
    rw [LoopIncI32.hfinish, LoopIncI32.hinc]
    exact Int.add_lt_add_right (Int32.lt_iff_toInt_lt.mp hterm) _
  rw [← loop_incI32_finish_const, ← loop_incI32_inc_const]
  exact loop_prop_const _ prop base step
