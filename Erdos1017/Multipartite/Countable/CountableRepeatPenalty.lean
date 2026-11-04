module

public import Erdos1017.Multipartite.Countable.CountableRepeatTests

/-!
# Least full-repeat penalty

`repeatPenalty` is the least nonnegative full-repeat penalty over every finite
exterior and dust count, bounded by any penalty passing all repeat tests; above
one half it equals the two-copy penalty under the coefficient bounds of the
head-count argument.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- Normalized threshold for repeating one head in one anchored exterior. -/
def repeatThreshold {i : ℕ} (D : Coefficients) (S : RepeatContext i) (r : ℕ) : ℝ :=
  ((r : ℝ) * S.row D + S.charge D - 1) / ((r : ℝ) * ((r : ℝ) - 1) / 2)

def repeatValues (D : Coefficients) (i : ℕ) : Set ℝ :=
  insert 0 {a | ∃ (S : RepeatContext i) (r : ℕ), 2 ≤ r ∧ a = repeatThreshold D S r}

/-- The least nonnegative full-repeat penalty over every finite exterior and
every old dust count. -/
def repeatPenalty (D : Coefficients) (i : ℕ) : ℝ := sSup (repeatValues D i)

def twoRepeatValues (D : Coefficients) (i : ℕ) : Set ℝ :=
  insert 0 (Set.range (fun S : RepeatContext i => 2 * S.row D + S.charge D - 1))

def twoRepeatPenalty (D : Coefficients) (i : ℕ) : ℝ := sSup (twoRepeatValues D i)

theorem repeat_denominator_pos {r : ℕ} (hr : 2 ≤ r) :
    0 < (r : ℝ) * ((r : ℝ) - 1) / 2 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)

theorem repeatThreshold_le_iff {i : ℕ} (D : Coefficients) (S : RepeatContext i)
    {r : ℕ} (hr : 2 ≤ r) (P : ℝ) :
    repeatThreshold D S r ≤ P ↔
      (r : ℝ) * S.row D + S.charge D - P * r * ((r : ℝ) - 1) / 2 ≤ 1 := by
  rw [repeatThreshold, div_le_iff₀ (repeat_denominator_pos hr)]
  constructor <;> intro h <;> nlinarith

theorem repeatValues_bddAbove {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    BddAbove (repeatValues D i) := by
  refine ⟨head D i, ?_⟩
  intro a ha
  rcases ha with rfl | ⟨S, r, hr, rfl⟩
  · exact hD.1.1 _
  · exact (repeatThreshold_le_iff D S hr _).mpr (S.default_test hD r)

theorem repeatPenalty_nonneg {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    0 ≤ repeatPenalty D i :=
  le_csSup (repeatValues_bddAbove hD i) (Set.mem_insert 0 _)

theorem repeatPenalty_le_head {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    repeatPenalty D i ≤ head D i := by
  apply csSup_le ⟨0, Set.mem_insert 0 _⟩
  intro a ha
  rcases ha with rfl | ⟨S, r, hr, rfl⟩
  · exact hD.1.1 _
  · exact (repeatThreshold_le_iff D S hr _).mpr (S.default_test hD r)

/-- The supremum penalty itself passes every actual anchored repeat test. -/
theorem repeatPenalty_test {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (S : RepeatContext i) (r : ℕ) :
    (r : ℝ) * S.row D + S.charge D - repeatPenalty D i * r * ((r : ℝ) - 1) / 2 ≤ 1 := by
  by_cases hr : 2 ≤ r
  · apply (repeatThreshold_le_iff D S hr _).mp
    exact le_csSup (repeatValues_bddAbove hD i) (Or.inr ⟨S, r, hr, rfl⟩)
  · have hsmall : r = 0 ∨ r = 1 := by omega
    rcases hsmall with rfl | rfl
    · simpa using S.zero_test hD
    · simpa using S.one_test hD

/-- Any nonnegative penalty passing every actual repeat test bounds the least
full-repeat penalty. -/
theorem repeatPenalty_le_of_tests (D : Coefficients) (i : ℕ) (P : ℝ) (hP : 0 ≤ P)
    (htest : ∀ (S : RepeatContext i) (r : ℕ),
      (r : ℝ) * S.row D + S.charge D - P * r * ((r : ℝ) - 1) / 2 ≤ 1) :
    repeatPenalty D i ≤ P := by
  apply csSup_le ⟨0, Set.mem_insert 0 _⟩
  intro a ha
  rcases ha with rfl | ⟨S, r, hr, rfl⟩
  · exact hP
  · exact (repeatThreshold_le_iff D S hr P).mpr (htest S r)

theorem twoRepeatValues_bddAbove {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    BddAbove (twoRepeatValues D i) := by
  refine ⟨head D i, ?_⟩
  intro a ha
  rcases ha with rfl | ⟨S, rfl⟩
  · exact hD.1.1 _
  · linarith [S.one_test hD, S.row_le_head hD]

theorem twoRepeatPenalty_nonneg {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    0 ≤ twoRepeatPenalty D i :=
  le_csSup (twoRepeatValues_bddAbove hD i) (Set.mem_insert 0 _)

theorem twoRepeatPenalty_le_head {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    twoRepeatPenalty D i ≤ head D i := by
  apply csSup_le ⟨0, Set.mem_insert 0 _⟩
  intro a ha
  rcases ha with rfl | ⟨S, rfl⟩
  · exact hD.1.1 _
  · linarith [S.one_test hD, S.row_le_head hD]

theorem twoRepeatPenalty_test {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (S : RepeatContext i) :
    2 * S.row D + S.charge D - twoRepeatPenalty D i ≤ 1 := by
  have h : 2 * S.row D + S.charge D - 1 ≤ twoRepeatPenalty D i :=
    le_csSup (twoRepeatValues_bddAbove hD i) (Or.inr ⟨S, rfl⟩)
  linarith

theorem twoRepeatPenalty_le_repeatPenalty {D : Coefficients} (hD : D ∈ feasible) (i : ℕ) :
    twoRepeatPenalty D i ≤ repeatPenalty D i := by
  apply csSup_le ⟨0, Set.mem_insert 0 _⟩
  intro a ha
  rcases ha with rfl | ⟨S, rfl⟩
  · exact repeatPenalty_nonneg hD i
  · have h := repeatPenalty_test hD S 2
    norm_num at h
    linarith

/-- Above one half, two-copy feasibility and a strict head bound control
every larger repeat count. -/
theorem twoRepeatPenalty_all_tests {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (hi : head D i < 1) (hhalf : 1 / 2 < twoRepeatPenalty D i)
    (S : RepeatContext i) (r : ℕ) :
    (r : ℝ) * S.row D + S.charge D - twoRepeatPenalty D i * r * ((r : ℝ) - 1) / 2 ≤ 1 := by
  by_cases hr : r ≤ 2
  · have hsmall : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hsmall with rfl | rfl | rfl
    · simpa using S.zero_test hD
    · simpa using S.one_test hD
    · have htwo := twoRepeatPenalty_test hD S
      norm_num at ⊢
      nlinarith
  · have hr' : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
    have hrow : S.row D < 1 := (S.row_le_head hD).trans_lt hi
    have hK : 0 ≤ twoRepeatPenalty D i := twoRepeatPenalty_nonneg hD i
    have hprod := mul_nonneg hK (show 0 ≤ (r : ℝ) - 3 by linarith)
    have hnegative : S.row D - twoRepeatPenalty D i * ((r : ℝ) + 1) / 2 ≤ 0 := by
      nlinarith
    have hinc := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (r : ℝ) - 2 by linarith) hnegative
    have htwo := twoRepeatPenalty_test hD S
    nlinarith

/-- The least full penalty equals the two-copy penalty under the actual
coefficient bounds used in the head-count argument. -/
theorem repeatPenalty_eq_twoRepeatPenalty {D : Coefficients} (hD : D ∈ feasible) {i : ℕ}
    (hi : head D i < 1) (hhalf : 1 / 2 < twoRepeatPenalty D i) :
    repeatPenalty D i = twoRepeatPenalty D i := by
  apply le_antisymm
  · exact repeatPenalty_le_of_tests D i _ (twoRepeatPenalty_nonneg hD i)
      (twoRepeatPenalty_all_tests hD hi hhalf)
  · exact twoRepeatPenalty_le_repeatPenalty hD i

end Erdos1017.MultipartiteCountableDual
