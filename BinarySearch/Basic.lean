import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Aesop

abbrev Pair := ℕ × ℕ

abbrev Proper (pair : Pair) := pair.1 < pair.2
abbrev Between (pair : Pair) m := pair.1 < m ∧ m < pair.2

def size : Pair → ℕ := fun p => p.2 - p.1

variable (pred : ℕ → Bool)

def searchStep (pair : Pair) (h : pair.fst < m ∧ m < pair.snd) : { p : Pair // size p < size pair } :=
  if pred m
    then ⟨(pair.fst, m), let ⟨a, b⟩ := h; tsub_lt_tsub_right_of_le (Nat.le_of_lt a) b⟩
    else ⟨(m, pair.snd), let ⟨a, b⟩ := h; Nat.sub_lt_sub_left (a.trans b) a⟩

variable (mid' : (p : Pair) → Option { m // Between p m })

def binarySearch (pair : Pair) : Pair :=
  match mid' pair with
  | none => pair
  | some ⟨_, hm⟩ =>
      let ⟨new, _⟩ := searchStep pred pair hm
      binarySearch new
termination_by pair.snd - pair.fst

def mid'_spec_converse := ∀ p, mid' p = none → p.2 ≤ p.1 + 1

theorem searchStep_lt_of_lt {pred pair between} (h : Proper pair) : Proper (searchStep pred pair between (m := m)) := by
  unfold searchStep; aesop

theorem adjacent (hmid : mid'_spec_converse mid') (pair : Pair) (lt : Proper pair) : ∃ n, binarySearch pred mid' pair = (n, n + 1) := by
  revert lt
  have size_wf := InvImage.wf size WellFoundedRelation.wf
  induction pair using WellFounded.induction
  . exact size_wf
  . rename_i pair h
    intro lt
    unfold binarySearch
    cases hm : mid' pair with
    | none => exact ⟨pair.1, by simp only [← Nat.le_antisymm (hmid _ hm) lt]⟩
    | some new =>  apply h _ (searchStep _ _ new.property).property (searchStep_lt_of_lt lt)

abbrev Invariant (pred : ℕ → Bool) (pair : Pair) := ¬pred pair.fst ∧ pred pair.snd

theorem invariant (inv : Invariant pred pair) : Invariant pred (binarySearch pred mid' pair) := by
  revert inv
  have size_wf := InvImage.wf size WellFoundedRelation.wf

  induction pair using WellFounded.induction
  . exact size_wf
  . rename_i pair h
    unfold binarySearch
    cases hm : mid' pair with
    | none => intro; assumption
    | some m =>
      simp only [hm]
      intro inv
      apply h
      -- decreasing_tactic
      . exact (searchStep pred pair m.property).property
      . unfold searchStep
        split <;> dsimp only
        . rename_i pred_m
          exact ⟨inv.left, pred_m⟩
        . rename_i not_pred_m
          exact ⟨not_pred_m, inv.right⟩

-- searching for target x, using predicate y > x, first elem of returned pair is last value <= x, second elem is virst val > x
def searchPred [LinearOrder α] (arr : List α) (target : α) (i : ℕ) : Bool :=
  match i with
  | 0 => false
  | j + 1 => if h: j < arr.length then arr[j]'h > target else true


lemma sum_div {a b c : ℕ} : a/c + b/c ≤ (a + b) / c  := sorry -- TODO: find in mathlib or prove manually (as an exercise)

def searchMid (p : Pair) : Option { m // Between p m } := if h : p.snd - p.fst > 1 then some ⟨p.fst + (p.snd - p.fst) / 2, by
    unfold Between
    simp
    apply And.intro
    . have ⟨n, hn⟩: ∃n, p.snd - p.fst = 2 + n := sorry
      rw [hn]
      have := @sum_div 2 n 2
      rw [Nat.div_self] at this
      . calc
          0 < 1 := by simp
          _ ≤ 1 + n /2 := by simp
          1 + n / 2 ≤ (2 + n) / 2 := this
        done
      . simp
      done
    . sorry
  ⟩ else none

inductive SearchPosition
| before
| index (i : ℕ)
| after

def returnIndex [LinearOrder α] (arr : List α) (target : α) :=
  (binarySearch (searchPred arr target) searchMid (0, arr.length + 1)).fst

variable [LinearOrder α] (arr : List α) (target : α)

def returnIndex' : SearchPosition :=
  let encoded := (binarySearch (searchPred arr target) searchMid (0, arr.length + 1)).fst
  match encoded with
  | 0 => .before
  | i + 1 => if i < arr.length then .index i else .after

lemma eq_arg (h: SearchPosition.index a = SearchPosition.index b) : b = a := by cases h; rfl
#print eq_arg

lemma index_i_imp_i_lt_length (ret_index_is_index : returnIndex' arr target = .index i) : i < arr.length := by
  unfold returnIndex' at ret_index_is_index
  simp at ret_index_is_index
  split at ret_index_is_index
  case h_1 j _ => contradiction
  case h_2 j _ =>
    split at ret_index_is_index
    case inl h' => exact calc
      i = j := eq_arg ret_index_is_index
      j < arr.length := h'
    case inr h' => contradiction
  done


lemma inv_true_at_start : Invariant (searchPred arr target) (0, List.length arr + 1) := by
  apply And.intro
  repeat (unfold searchPred; simp)
  done

#check (inv_true_at_start arr target).left
lemma index_i_imp_arr_i_le_target (ret_index_is_index : returnIndex' arr target = .index i) : arr[i]'(index_i_imp_i_lt_length arr target ret_index_is_index) ≤ target := by
  unfold returnIndex' at ret_index_is_index
  simp at ret_index_is_index
  have false_on_fst : ¬searchPred arr target (binarySearch _ _ (0, List.length arr + 1)).fst := (invariant _ searchMid (inv_true_at_start _ _)).left
  have h : i + 1 = (binarySearch (searchPred arr target) searchMid (0, List.length arr + 1)).fst := by
    split at ret_index_is_index
    . contradiction
    . split at ret_index_is_index
      . cases ret_index_is_index
        simp [*]
      . contradiction
  -- The predicate is false on i + 1. if i < arr.length, searchPred is only false on i + 1 if ¬(arr[i] > target)
  rw [←h] at false_on_fst
  simp [searchPred] at false_on_fst
  cases false_on_fst
  assumption
  done


abbrev Sorted (arr : List α) : Prop :=
  ∀(i j : Nat) (h : i < arr.length ∧ j < arr.length), arr[i]'h.left ≤ arr[j]'h.right

lemma inv_ret_pair : Invariant (searchPred arr target) (binarySearch (searchPred arr target) searchMid (0, List.length arr + 1)) := by
  have inv_in : Invariant (searchPred arr target) (0, List.length arr + 1) := by
    unfold Invariant
    apply And.intro
    . simp only [Bool.not_eq_true]
      rfl
    . unfold searchPred
      simp only [Nat.add_eq, add_zero, lt_self_iff_false, List.getElem_eq_get, gt_iff_lt, dite_false]
  exact @invariant (searchPred arr target) (searchMid) (0, List.length arr + 1) inv_in


def containsTargetAt (arr : List α) (target : α) (i : ℕ) : Prop :=
  ∃ (hi : i < arr.length), arr[i]'hi = target

def containsTarget (arr : List α) (target : α) : Prop :=
  ∃ (i : ℕ), containsTargetAt arr target i

lemma arr_ret_index_le_target (is_index : returnIndex' arr target = .index i) (in_bounds : i < arr.length): arr[i]'in_bounds ≤ target := by
  cases pos : returnIndex' arr target with
  | before => sorry
  | index j => sorry
  | after => sorry
  done

lemma arr_succ_ret_index_gt_target (is_index : returnIndex' arr target = .index i) (succ_in_bounds : i + 1 < arr.length) : arr[i + 1] > target := by
  sorry

lemma ret_index_index_in_bounds (is_index : returnIndex' arr target = .index i) : i < arr.length := by
  unfold returnIndex' at is_index
  simp at is_index
  split at is_index
  . contradiction
  . split at is_index
    . sorry
    . contradiction

lemma foo : returnIndex' arr target = .index i → (_ : i + 1 < arr.length) → target < arr[i+1] := by
  sorry

lemma bar (i : ℕ): returnIndex' arr target = .before → ∀(h : i < arr.length), target < arr[i]'h := by sorry

theorem bsearch_finds_target_if_target_exists
    (sorted : Sorted arr) (contains : containsTarget arr target) :
    ∃j, containsTargetAt arr target j ∧ returnIndex' arr target = .index j := by
    revert contains
    contrapose
    intro h
    simp only [not_exists] at h
    unfold containsTarget
    simp
    -- We want to show that for every nat, the array does not contain the target at that index. So we introduce i.
    intro i
    /- Now we consider the value of returnIndex' arr target. It is either SearchPosition.before,
    SearchPosition.index j for some j, or SearchPosition.after -/
    cases ret_index_eq : returnIndex' arr target with
    | before => -- If returnIndex' is before, that means the target is less than everything in the array.
      have := bar _ _ i ret_index_eq -- bar means target is less than everything
      -- Start golf section. Try to make one line
      unfold containsTargetAt
      simp only [not_exists]
      intro h
      have arr_i_ne_target := ne_of_lt (this h)
      intro
      have := arr_i_ne_target.symm
      contradiction
      -- End golf section
    | index j =>
      -- Either the array does not contain the target at j or the return index does not use the index constructor with j
      have := h j
      have j_in_bounds := (ret_index_index_in_bounds arr target ret_index_eq)
      rw [not_and_or] at this
      cases this with
      /- If the target is not at j, we consider three cases: i < j, i = j, and i > j. -/
      | inl target_not_at_j =>
          obtain lt | eq | gt := Nat.lt_trichotomy i j
          -- This is the subcase where i < j, i.e., our arbitrary nat is less than the returned index.
          . have arr_j_le_target : arr[j] ≤ target := arr_ret_index_le_target arr target ret_index_eq _
            have arr_j_ne_target : arr[j] ≠ target := by
              unfold containsTargetAt at target_not_at_j
              simp only [not_exists] at target_not_at_j
              exact target_not_at_j j_in_bounds
            -- TODO: put these in the calc proof
            have arr_j_lt_target : arr[j] < target := lt_of_le_of_ne arr_j_le_target arr_j_ne_target
            have arr_i_le_arr_j : arr[i] ≤ arr[j] := sorted i j ⟨by linarith, j_in_bounds⟩
            have arr_i_lt_target : arr[i] < target := -- We tried to use linarith instead of calc, but we don't know why it failed.
              calc
              arr[i] ≤ arr[j] := arr_i_le_arr_j
              arr[j] < target := arr_j_lt_target
            have arr_i_ne_target := ne_of_lt arr_i_lt_target
            unfold containsTargetAt
            simp only [not_exists]
            intro h
            assumption
          -- This is the subcase where i = j, i.e., our arbitrary nat is equal to the returned index.
          . rwa [eq]
          -- This is the subcase where i > j, i.e., our arbitrary nat is greater than the returned index.
          . have i_ge_succ_j : j + 1 ≤ i := by linarith
            by_cases h : i < arr.length
            -- If i is in bounds, then j + 1 is also in bounds. arr[j+1] > target by foo. Since arr is sorted, arr[i] > arr[j+1]. So arr[i] > target
            have arr_i_ge_target : target < arr[i] :=
              calc
              target < arr[j+1] := foo _ _ ret_index_eq (by linarith)
              arr[j+1] ≤ arr[i] := sorted (j + 1) i ⟨by linarith, by assumption⟩
            unfold containsTargetAt
            simp only [not_exists]
            intro h
            exact ne_of_gt arr_i_ge_target
            -- If i >= length, then of course arr[i] is not target. You can't index arr at i
            . unfold containsTargetAt
              by_contra arr_i_eq_target
              cases arr_i_eq_target
              contradiction
      /- This is the case where the returned index is not j. But that contradicts our earlier assumption
         that defined this case in the first place. -/
      | inr _ => contradiction
    | after => sorry -- This is impossible. returnIndex' always corresponds to binary search's first returned item, which the searchPred should be false on
    done
