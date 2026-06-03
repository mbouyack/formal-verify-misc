import Mathlib.Data.Vector.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.Defs
import FormalVerifyMisc.Loops

-- codechef.com/problems/BINCON

/-
  The problem solution is defined by 'do_solve' which takes P, a 'SolveParams' as an argument.
  The correctness of this solution is proven in 'do_solve_size', which proves the resulting
  string has length N as required, and 'f_solve_card_is_max', which proves that f(S) has the
  maximum possible cardinality (where 'S' is our solution string).
-/

def f {N : ℕ} (S : Vector Bool N) : Set ℕ :=
  {n : ℕ | ∃ (i j : Fin N), S[i] ≠ S[j] ∧ (i.val + 1) + (j.val + 1) = n}

-- Prove that all elements of 'f' are less than or equal to 2N - 1
theorem f_mem_le {N : ℕ} (S : Vector Bool N) :
  ∀ a ∈ f S, a ≤ 2 * N - 1 := by
  unfold f; dsimp
  intro a h
  rcases h with ⟨i, j, hne, rfl⟩
  push_neg at hne
  by_cases hij : i = j
  · absurd hne
    subst hij; rfl
  omega

theorem f_mem_ge {N : ℕ} (S : Vector Bool N) :
  ∀ a ∈ f S, 3 ≤ a := by
  unfold f; dsimp
  intro a h
  rcases h with ⟨i, j, hne, rfl⟩
  push_neg at hne
  by_cases hij : i = j
  · absurd hne
    subst hij; rfl
  omega

-- Problem inputs and contraints
structure SolveParams where
  -- The main argument to the problem - indicates the length of the boolean string
  N : Int32
  -- These are the bounds given in the problem statement
  hleN : 2 ≤ N
  hNle : N ≤ 100

-- Function to construct an iterator for the main loop
def solve_iter_params (P : SolveParams) : IteratorInt32Params where
  start := 0
  finish := P.N
  inc := 1
  incpos := by decide
  hle := Int32.le_trans (by decide) P.hleN
  hdvd := Int.one_dvd _

@[simp] theorem solve_iter_params_inc (P : SolveParams) :
  (solve_iter_params P).inc = 1 := rfl

@[simp] theorem solve_iter_params_start (P : SolveParams) :
  (solve_iter_params P).start = 0 := rfl

@[simp] theorem solve_iter_params_finish (P : SolveParams) :
  (solve_iter_params P).finish = P.N := rfl

-- The element should be '1' if it is the first or last element
-- If the solution has exactly two elements then the first will be '0' instead
def get_solve_elem (i N : Int32) : Bool :=
  decide (i = 0 ∧ N ≠ 2 ∨ i + 1 = N)

structure Solve (P : SolveParams) where
  A : Array Bool
  iter : IteratorInt32 (solve_iter_params P)
  hsize : A.size = iter.val.toInt
  helem : ∀ i, (h : i < A.size) → A[i] = get_solve_elem (Int32.ofNat i) P.N

def advance_solve {P : SolveParams} (S : Solve P)
  (hnend : ¬S.iter = iterator_int32_end _) : Solve P where
  A := S.A.push (get_solve_elem S.iter.val P.N)
  iter := iterator_int32_next S.iter
  hsize := by
    rw [Array.size_push, Int.natCast_add]
    rw [iterator_int32_next_val_toInt _ hnend, S.hsize]
    simp only [Nat.cast_one, solve_iter_params_inc, Int32.reduceToInt]
  helem := by
    intro i ilt
    rw [Array.size_push] at ilt
    by_cases hi : i = S.A.size
    · subst hi
      rw [Array.getElem_push_eq]; congr
      apply Int32.toInt_inj.mp
      rw [Int32.toInt_ofNat_of_lt, S.hsize]
      apply Int.lt_of_ofNat_lt_ofNat
      rw [S.hsize]
      apply lt_of_le_of_lt (Int32.le_iff_toInt_le.mp S.iter.hvalle)
      rw [solve_iter_params_finish]
      apply lt_of_le_of_lt (Int32.le_iff_toInt_le.mp P.hNle)
      decide
    rename' hi => ine; push_neg at ine
    have ilt' := lt_of_le_of_ne (Nat.le_of_lt_add_one ilt) ine
    rw [Array.getElem_push_lt ilt']
    exact S.helem i ilt'

-- Prove that 'Solve' implements an iterator loop
instance {P : SolveParams} :
  LoopIterator (Solve P) (IteratorInt32 (solve_iter_params P)) where
  iter := fun S ↦ S.iter
  adv := advance_solve
  hadv := fun _ _ ↦ rfl

def init_solve (P : SolveParams) : Solve P where
  A := #[]
  iter := iterator_int32_begin _
  hsize := by
    rw [Array.size_empty, iterator_int32_begin_val]
    rw [solve_iter_params_start]
    rfl
  helem := by
    intro _ h
    absurd h; push_neg
    rw [Array.size_empty]
    exact Nat.zero_le _

def do_solve (P : SolveParams) : Array Bool :=
  (do_loop (init_solve P)).A

theorem solve_size {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  (do_solve P).size = N := by
  unfold do_solve
  apply Int.natCast_inj.mp
  rw [Solve.hsize, ← hn, ← solve_iter_params_finish]
  rw [← iterator_int32_end_val]; congr
  exact decide_eq_true_iff.mp (loop_term (init_solve P))

theorem solve_size_ge {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  2 ≤ (do_solve P).size := by
  rw [solve_size P hn]
  apply Int.le_of_ofNat_le_ofNat
  rw [← hn]
  convert Int32.le_iff_toInt_le.mp P.hleN

theorem solve_size_pos {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  0 < (do_solve P).size := lt_of_lt_of_le (by simp) (solve_size_ge P hn)

theorem solve_getElem_zero_of_size_eq_two
  (P : SolveParams) (hn : P.N.toInt = 2) :
  (do_solve P)[0]'(solve_size_pos P hn) = false := by
  unfold do_solve
  rw [(do_loop (init_solve P)).helem 0 (solve_size_pos P hn)]
  unfold get_solve_elem
  have h2 : P.N = 2 := by
    apply Int32.toInt_inj.mp
    rw [hn]
    rfl
  rw [h2]
  simp

-- The first element is always 'true' unless N = 2
theorem solve_getElem_zero_of_size_ne_two {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hne2 : N ≠ 2) :
  (do_solve P)[0]'(solve_size_pos P hn) = true := by
  unfold do_solve
  rw [(do_loop (init_solve P)).helem 0 (solve_size_pos P hn)]
  unfold get_solve_elem
  simp only [Int32.reduceOfNat, ne_eq, true_and, Int32.zero_add, Bool.decide_or, decide_not,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq]; left
  contrapose! hne2
  apply Int.natCast_inj.mp
  rw [← hn, hne2]
  rfl

-- The last element is always true
theorem solve_getElem_last {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  (do_solve P)[N-1]'(by
    rw [solve_size P hn]
    apply Nat.sub_one_lt
    apply Nat.ne_zero_of_lt
    convert solve_size_pos P hn
    rw [solve_size P hn]
  ) = true := by
  unfold do_solve
  rw [(do_loop (init_solve P)).helem (N - 1)]
  unfold get_solve_elem
  simp only [Bool.decide_or, Bool.or_eq_true]; right
  simp only [decide_eq_true_eq]
  apply Int32.toInt_inj.mp
  rw [hn]
  have leN : 1 ≤ N := by
    apply Int.le_of_ofNat_le_ofNat
    rw [← hn]
    exact le_trans (by decide) (Int32.le_iff_toInt_le.mp P.hleN)
  have Nlt : N < 2 ^ 31 := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← hn]
    exact lt_of_le_of_lt (Int32.le_iff_toInt_le.mp P.hNle) (by decide)
  have h : ↑(N - 1) = (N : ℤ) - 1 := by
    rwa [Int.ofNat_sub, Nat.cast_one]
  have h' : (Int32.ofNat (N - 1)).toInt = N - 1 := by
    rw [← h]
    apply Int32.toInt_ofNat_of_lt
    apply Nat.sub_lt_right_of_lt_add leN
    exact lt_trans Nlt (by decide)
  have h'' : (Int32.ofNat (N - 1)).toInt < 2 ^ 31 - 1 := by
    rw [h', ← hn]
    apply Int.sub_lt_sub_right
    exact Int.lt_of_le_of_lt (Int32.le_iff_toInt_le.mp P.hNle) (by decide)
  rw [int32_toInt_succ' _ h'', h', Int.sub_add_cancel]

theorem solve_getElem_eq_false {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  ∀ i, (ilt : i < N - 1) → (i ≠ 0 ∨ N = 2) →
  (do_solve P)[i]'(by
    rw [solve_size P hn]
    exact lt_of_lt_of_le ilt (Nat.sub_le _ _)
  ) = false := by
  intro i ilt h
  have leN : 1 ≤ N := by
    apply Int.le_of_ofNat_le_ofNat
    rw [← hn]
    exact le_trans (by decide) (Int32.le_iff_toInt_le.mp P.hleN)
  have Nlt : N < 2 ^ 31 := by
    apply Int.lt_of_ofNat_lt_ofNat
    rw [← hn]
    exact lt_of_le_of_lt (Int32.le_iff_toInt_le.mp P.hNle) (by decide)
  have : (Int32.ofNat i).toInt = ↑i := by
      apply Int32.toInt_ofNat_of_lt (lt_trans ilt (lt_of_le_of_lt _ Nlt))
      exact Nat.sub_le _ _
  have ilt' : (i : ℤ) < N - 1 := by
    convert Int.ofNat_lt_ofNat_of_lt ilt; symm
    exact Int.ofNat_sub leN
  unfold do_solve
  rw [(do_loop (init_solve P)).helem i]
  unfold get_solve_elem
  simp only [Bool.decide_or, Bool.or_eq_false_iff]
  constructor
  · simp only [Bool.decide_and, Bool.and_eq_false_imp, decide_eq_true_eq]
    intro h'
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
    rw [← Int32.toInt_inj] at h'
    simp only [Int32.reduceToInt] at h'
    rcases h with lhs | rhs
    · absurd lhs
      apply Int.ofNat_inj.mp
      rw [Nat.cast_zero, ← this, ← h']
    · apply Int32.toInt_inj.mp
      rw [hn, rhs]; rfl
  · simp only [decide_eq_false_iff_not]
    intro h'
    apply Nat.ne_of_lt ilt (Int.ofNat_inj.mp _)
    rw [Int.ofNat_sub leN]
    simp only [Nat.cast_one]
    rw [← hn, ← h']
    rw [int32_toInt_succ', this, Int.add_sub_cancel]
    rw [this]
    exact lt_trans ilt' (Int.sub_lt_sub_right (Int.ofNat_lt_ofNat_of_lt Nlt) _)

-- If an element of 'do_solve P' is true,
-- it must be the first or last element.
theorem solve_idx_of_getElem_eq_true {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) :
  ∀ i : (Fin (do_solve P).size),
  (do_solve P)[i] = true → i.val = 0 ∨ i.val = N - 1 := by
  intro i h
  contrapose h
  push_neg at h
  rw [Bool.not_eq_true]
  have ilt : i.val < N := by
    rw [← solve_size P hn]
    exact i.2
  have ilt' : i.val < N - 1 :=
    lt_of_le_of_ne (Nat.le_sub_one_of_lt ilt) h.2
  exact solve_getElem_eq_false P hn i.val ilt' (Or.inl h.1)

-- If an element of 'do_solve P' is false,
-- it must be any element other than the first or last
-- (given that N > 2)
theorem solve_idx_of_getElem_eq_false {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hgt : 2 < N) :
  ∀ i : (Fin (do_solve P).size),
  (do_solve P)[i] = false → 0 < i.val ∧ i.val < N - 1 := by
  intro i h
  contrapose h
  rw [not_and_or] at h
  rw [Bool.not_eq_false]
  have ilt : i.val < N := by
    rw [← solve_size P hn]
    exact i.2
  change (do_solve P)[i.val] = true
  rcases h with lhs | rhs
  · have hiz := Nat.le_zero.mp (not_lt.mp lhs)
    rw [getElem_congr_idx hiz]
    exact solve_getElem_zero_of_size_ne_two P hn (ne_of_lt hgt).symm
  · push_neg at rhs
    rw [getElem_congr_idx (le_antisymm (Nat.le_sub_one_of_lt ilt) rhs)]
    exact solve_getElem_last P hn

-- If N = 2, f S = {3} (where 'S' is the solution string)
theorem f_solve_of_size_eq_two
  (P : SolveParams) (hn : P.N.toInt = 2) :
  f (do_solve P).toVector = {3} := by
  unfold f
  ext n
  constructor
  · intro nmem
    simp only [Fin.getElem_fin, Vector.getElem_mk, ne_eq, Set.mem_setOf_eq] at nmem
    rcases nmem with ⟨j, k, hjk⟩
    have hne : j ≠ k := by
      intro h
      absurd hjk.1
      congr
    rw [← hjk.2, Set.mem_singleton_iff]
    clear hjk n
    wlog jlek : j < k
    · rw [add_comm]
      exact this P hn k j hne.symm (by omega)
    have klt : k.val < 2 := by
      convert k.2
      exact (solve_size P hn).symm
    omega
  · intro nmem
    have n3 : n = 3 := Set.mem_singleton_iff.mp nmem
    subst n3
    simp only [Fin.getElem_fin, Vector.getElem_mk, ne_eq, Set.mem_setOf_eq]
    have sgt : 0 < (do_solve P).size := by rw [solve_size P hn]; decide
    have sgt' : 1 < (do_solve P).size := by rw [solve_size P hn]; decide
    use ⟨0, sgt⟩, ⟨1, sgt'⟩
    simp only [zero_add, Nat.reduceAdd, and_true]
    rw [solve_getElem_zero_of_size_eq_two P hn]
    simp only [Bool.false_eq, Bool.not_eq_false]
    convert solve_getElem_last P hn

theorem f_solve_mem_iff {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hgt : 2 < N) :
  ∀ n, n ∈ f (do_solve P).toVector ↔
  2 < n ∧ n < 2 * N ∧ n ≠ N + 1 := by
  intro n
  constructor
  · intro h
    have nle := f_mem_ge _ _ h
    have len := f_mem_le _ _ h
    rw [solve_size P hn] at len
    use Nat.lt_of_add_one_le nle, by omega
    unfold f at h; dsimp at h
    rcases h with ⟨i, j, hne, h⟩
    change ¬(do_solve P)[i] = (do_solve P)[j] at hne
    -- Show that either element 'i' or element 'j' must be true
    have htrue : (do_solve P)[i] = true ∨ (do_solve P)[j] = true := by
      contrapose hne
      rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at hne
      rw [hne.1, hne.2]
    -- Without loss of generality, assume element 'i' is true
    wlog hit : (do_solve P)[i] = true
    · push_neg at hne
      rw [add_comm] at h
      rw [or_comm] at htrue
      exact this P hn hgt n nle len j i h hne.symm htrue (Or.resolve_right htrue hit)
    have hjf : (do_solve P)[j] = false := by
      rwa [hit, Bool.true_eq, Bool.not_eq_true] at hne
    obtain ⟨ltj, jlt⟩ := solve_idx_of_getElem_eq_false P hn hgt j hjf
    rw [← h]
    rcases solve_idx_of_getElem_eq_true P hn i hit with lhs | rhs
    · rw [lhs, zero_add, add_comm]
      contrapose! jlt
      rw [← Nat.add_left_inj.mp jlt, Nat.add_sub_cancel]
    · rw [rhs]
      contrapose! ltj
      have len : 1 ≤ N :=
        Nat.le_of_lt (lt_of_le_of_lt (by decide) hgt)
      rw [Nat.sub_add_cancel len] at ltj
      rw [Nat.add_left_inj.mp (Nat.add_right_inj.mp ltj)]
  · intro ⟨ltn, nlt, nne⟩
    unfold f; dsimp
    by_cases nle : n ≤ N + 1
    · have nlt' := lt_of_le_of_ne nle nne
      have ns2lt : n - 2 < N - 1 := by
        apply lt_of_lt_of_eq (Nat.sub_lt_sub_right (le_of_lt ltn) nlt')
        simp only [Nat.reduceSubDiff]
      let i : Fin (do_solve P).size := ⟨0, by
        rw [solve_size P hn]
        exact lt_trans (by decide) hgt
      ⟩
      let j : Fin (do_solve P).size := ⟨n - 2, by
        rw [solve_size P hn]
        exact lt_of_lt_of_le ns2lt (Nat.sub_le _ _)
      ⟩
      have hi : i.val = 0 := rfl
      have hj : j.val = n - 2 := rfl
      use i, j
      rw [getElem_congr_idx hi, getElem_congr_idx hj]
      rw [solve_getElem_zero_of_size_ne_two P hn (ne_of_lt hgt).symm]
      rw [solve_getElem_eq_false P hn (n - 2) ns2lt (Or.inl (Nat.sub_ne_zero_of_lt ltn))]
      simp only [Bool.true_eq_false, not_false_eq_true, true_and]
      rw [hi, hj, zero_add, add_comm, add_assoc, one_add_one_eq_two]
      exact Nat.sub_add_cancel (le_of_lt ltn)
    · push_neg at nle; rename' nle => ltn'
      have Nge1 : 1 ≤ N :=
        le_trans (by decide) (le_of_lt hgt)
      have Nle : N ≤ n - 1 :=
        Nat.le_sub_one_of_lt (lt_trans (Nat.lt_add_one _) ltn')
      let i : Fin (do_solve P).size := ⟨N - 1, by
        rw [solve_size P hn]
        exact Nat.sub_lt (Nat.zero_lt_of_lt hgt) (by decide)
      ⟩
      let j : Fin (do_solve P).size := ⟨n - N - 1, by
        rw [solve_size P hn, Nat.sub_right_comm]
        apply Nat.sub_lt_right_of_lt_add Nle
        rw [← two_mul]
        exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) nlt
      ⟩
      have hi : i.val = N - 1 := rfl
      have hj : j.val = n - N - 1 := rfl
      use i, j
      rw [getElem_congr_idx hi, solve_getElem_last P hn]
      have jlt : j.val < N - 1 := by
        rw [hj, ← Nat.sub_add_eq]
        apply Nat.sub_lt_right_of_lt_add (le_of_lt ltn')
        rw [← add_assoc, ← Nat.sub_add_comm Nge1]
        rw [Nat.sub_add_cancel (le_trans Nge1 (Nat.le_add_right _ _))]
        rwa [← two_mul]
      have jnz : j.val ≠ 0 := by
        rw [hj, ← Nat.sub_add_eq]
        exact Nat.sub_ne_zero_of_lt ltn'
      rw [solve_getElem_eq_false P hn j jlt (Or.inl jnz)]
      simp only [Bool.true_eq_false, not_false_eq_true, true_and]
      rw [hj, hi, Nat.sub_add_cancel Nge1]
      have lensN : 1 ≤ n - N := by
        apply Nat.le_sub_of_add_le
        rw [add_comm]
        exact le_of_lt ltn'
      rw [Nat.sub_add_cancel lensN]
      rw [← Nat.add_sub_assoc (le_trans Nle (Nat.sub_le _ _))]
      rw [add_comm, Nat.add_sub_cancel]

def F_lower (N : ℕ) := Finset.Icc 3 N
def F_upper (N : ℕ) := Finset.Icc (N + 2) (2 * N - 1)
def F (N : ℕ) : Finset ℕ := F_lower N ∪ F_upper N

theorem F_lower_upper_disjoint (N : ℕ) : Disjoint (F_lower N) (F_upper N) := by
  rw [Finset.disjoint_iff_ne]
  unfold F_lower F_upper
  intro a meml b memu h
  subst h
  have ale := (Finset.mem_Icc.mp meml).2
  have lea := (Finset.mem_Icc.mp memu).1
  omega

theorem F_lower_card (N : ℕ) : (F_lower N).card = N - 2 := by
  unfold F_lower
  rw [Nat.card_Icc]; omega

theorem F_upper_card (N : ℕ) : (F_upper N).card = N - 2 := by
  unfold F_upper
  rw [Nat.card_Icc]; omega

theorem F_card (N : ℕ) : (F N).card = 2 * N - 4 := by
  unfold F
  rw [Finset.card_union_of_disjoint (F_lower_upper_disjoint N)]
  rw [F_lower_card, F_upper_card]
  omega

def solve_equiv_of_gt' {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hgt : 2 < N) :
  f (do_solve P).toVector ≃ F N where
  toFun := fun ⟨a, amem⟩ ↦ ⟨a, by
    obtain ⟨lta, alt, ane⟩ := (f_solve_mem_iff P hn hgt a).mp amem
    unfold F
    rw [Finset.mem_union]
    by_cases ale : a ≤ N
    · exact Or.inl (Finset.mem_Icc.mpr ⟨by omega, ale⟩)
    · exact Or.inr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  ⟩
  invFun := fun ⟨n, nmem⟩ ↦ ⟨n, by
    apply (f_solve_mem_iff P hn hgt n).mpr
    rcases Finset.mem_union.mp nmem with lhs | rhs
    · obtain ⟨len, nle⟩ := Finset.mem_Icc.mp lhs; omega
    · obtain ⟨len, nle⟩ := Finset.mem_Icc.mp rhs; omega
  ⟩

theorem solve_card_of_gt {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hgt : 2 < N) :
  (f (do_solve P).toVector).ncard = 2 * N - 4 := by
  rw [Set.ncard_congr' (solve_equiv_of_gt' P hn hgt)]
  rw [Set.ncard_coe_finset, F_card]

lemma bool_eq_of_ne_of_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  by_cases ha : a = true
  · subst ha
    simp only [ne_eq, Bool.true_eq, Bool.not_eq_true] at hab
    subst hab
    simp only [ne_eq, Bool.false_eq, Bool.not_eq_false] at hbc
    symm; assumption
  · simp only [Bool.not_eq_true] at ha
    subst ha
    simp only [ne_eq, Bool.false_eq, Bool.not_eq_false] at hab
    subst hab
    simp only [ne_eq, Bool.true_eq, Bool.not_eq_true] at hbc
    symm; assumption

-- For every S, a vector of boolean values of length N,
-- f S is missing at least one value on the range [3, 2N - 1]
theorem f_exists_not_mem {N : ℕ} (hgt : 2 < N) :
  ∀ (S : Vector Bool N), ∃ n,
  2 < n ∧ n < 2 * N ∧ n ∉ f S := by
  intro S
  -- Handle the case where S = "0111..." or S = "1000..."
  by_cases h : ∀ (i : Fin N), i.val ≠ 0 → S[0] ≠ S[i]
  · use (2 * N - 1), (by omega), (by omega)
    unfold f
    dsimp; push_neg; intro j k h'
    by_cases jnz : j.val = 0
    · omega
    by_cases knz : k.val = 0
    · omega
    push_neg at jnz knz
    absurd h'
    exact bool_eq_of_ne_of_ne (h j jnz).symm (h k knz)
  push_neg at h
  let Q (x : Fin N) : Prop := x.val ≠ 0 ∧ S[0] = S[x]
  -- Let 'i' by the first element after S[0] that matches S[0]
  let i := Fin.find Q h
  have isat : i.val ≠ 0 ∧ S[0] = S[i] := Fin.find_spec h
  have ile : ∀ (i' : Fin N), Q i' → i ≤ i' :=
    fun _ hi' ↦ Fin.find_le hi'
  -- From the definition of 'i', no other prior element can
  -- by equal to S[0] (other than S[0] itself)
  have hne : ∀ (l : Fin N), l.val ≠ 0 ∧ l.val < i.val → S[0] ≠ S[l] := by
    intro l hl hS0Sl
    absurd ile l (And.intro hl.1 hS0Sl); push_neg
    exact Fin.val_fin_lt.mp hl.2
  use i.val + 2, by omega, by omega
  unfold f; dsimp; push_neg
  intro j k SjneSk
  have jnek : j ≠ k := by
    contrapose! SjneSk; congr
  -- Without loss of generality assume j < k
  wlog jltk : j < k
  · have kltj : k < j := by omega
    rw [add_comm (j.val + 1)]
    exact this hgt S h isat ile hne k j SjneSk.symm jnek.symm kltj
  by_cases hjz : j.val = 0
  · rw [hjz, zero_add, add_comm, add_assoc, one_add_one_eq_two]
    contrapose! SjneSk
    rw [getElem_congr_idx hjz]
    rw [getElem_congr_idx (Nat.add_left_inj.mp SjneSk)]
    exact isat.2
  rename' hjz => hjnz; push_neg at hjnz
  have hknz : k.val ≠ 0 := by omega
  contrapose! SjneSk
  have klti : k.val < i.val := by omega
  have jlti : j.val < i.val :=
    lt_trans (Fin.val_fin_lt.mpr jltk) klti
  have S0neSj := hne j (And.intro hjnz jlti)
  have S0neSk := hne k (And.intro hknz klti)
  exact bool_eq_of_ne_of_ne S0neSj.symm S0neSk

-- Prove that for all S, f S ⊆ [3, 2N-1]
theorem f_subset {N : ℕ} :
  ∀ (S : Vector Bool N), f S ⊆ Finset.Icc 3 (2 * N - 1) := by
  intro S a amem
  simp only [Finset.coe_Icc, Set.mem_Icc]
  rcases amem with ⟨j, k, hne, ha⟩
  contrapose! hne; congr;
  omega

-- Prove that
theorem f_ncard_le₀ {N : ℕ} :
  ∀ (S : Vector Bool N), (f S).ncard ≤ 2 * N - 3 := by
  intro S
  apply le_trans (Set.ncard_le_ncard (f_subset S))
  rw [Set.ncard_coe_finset, Nat.card_Icc]
  omega

-- Prove that if 2 < N, then for all S, f S ⊂ [3, 2N-1]
theorem f_subset_proper {N : ℕ} (hgt : 2 < N) :
  ∀ (S : Vector Bool N), f S ⊂ Finset.Icc 3 (2 * N - 1) := by
  intro S
  apply And.intro (f_subset S)
  rcases f_exists_not_mem hgt S with ⟨n, ltn, nlt, hn⟩
  contrapose! hn
  apply hn
  simp only [Finset.coe_Icc, Set.mem_Icc]; omega

theorem f_ncard_le₁ {N : ℕ} (hgt : 2 < N) :
  ∀ (S : Vector Bool N), (f S).ncard ≤ 2 * N - 4 := by
  intro S
  apply Nat.le_of_lt_add_one
  have hfin := (Finset.Icc 3 (2 * N - 1)).finite_toSet
  convert Set.ncard_lt_ncard (f_subset_proper hgt S) hfin
  rw [Set.ncard_coe_finset, Nat.card_Icc]; omega

-- Prove the correctness of 'do_solve'
-- That is, there is no string S which results in a larger f S
theorem f_solve_card_is_max {N : ℕ}
  (P : SolveParams) (hn : P.N.toInt = N) (hge : 2 ≤ N) :
  ∀ (S : Vector Bool N),
  (f S).ncard ≤ (f (do_solve P).toVector).ncard := by
  intro S
  by_cases hN : N = 2
  · subst hN
    rw [f_solve_of_size_eq_two P hn, Set.ncard_singleton]
    convert f_ncard_le₀ S
  have hgt : 2 < N := by omega
  rw [solve_card_of_gt P hn hgt]
  exact f_ncard_le₁ hgt S
