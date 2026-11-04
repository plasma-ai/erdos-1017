module

public import Erdos1017.Multipartite.MultipartiteDustFloors
public import Erdos1017.Multipartite.Countable.CountableDualMask

/-!
# Dust-count witnesses for the two-copy penalty

Every exterior either has a small threshold from another positive head or is an
anchor-and-dust threshold, so the two-copy supremum is attained by a finite
anchor-and-dust count once it exceeds one half with positive internal dust
penalty, and with unused dust coefficients erased it is witnessed at count zero.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The two-copy threshold for an exterior containing only the anchor and
an arbitrary old-dust count. -/
def dustThreshold (D : Coefficients) (i k : ℕ) : ℝ :=
  2 * (head D i - (k : ℝ) * incident D i) + (k : ℝ) * linear D -
    penalty D * k * ((k : ℝ) - 1) / 2 - 1

def dustContext (i k : ℕ) : RepeatContext i := ⟨i + 1, by omega, fun _ => false, rfl, k⟩

theorem dustThreshold_le_twoRepeatPenalty {D : Coefficients} (hD : D ∈ feasible) (i k : ℕ) :
    dustThreshold D i k ≤ twoRepeatPenalty D i := by
  have h := twoRepeatPenalty_test hD (dustContext i k)
  simp only [RepeatContext.row, RepeatContext.charge, dustContext, MultipartiteDust.charge,
    Selector.bit, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero, add_zero,
    sub_zero, MultipartiteDust.head, MultipartiteDust.incident, MultipartiteDust.linear,
    MultipartiteDust.penalty, restrict] at h
  unfold dustThreshold head incident linear penalty
  simp only [head, incident] at h
  nlinarith

/-- If an exterior selects another positive head, the old anchored triangle
uniformly bounds its two-copy threshold below the selected multiplier. -/
theorem RepeatContext.row_le_one_sub_head {D : Coefficients} (hD : D ∈ feasible)
    {i : ℕ} (S : RepeatContext i) (j : Fin S.size) (hj : S.selection j = true) :
    S.row D ≤ 1 - head D j.val := by
  have hij : i ≠ j.val := by
    intro hij
    have hfin : (⟨i, S.head_lt⟩ : Fin S.size) = j := Fin.ext hij
    have h := S.head_absent
    rw [hfin, hj] at h
    contradiction
  have hC := restrict_mem_feasible hD S.size
  have hsum : (∑ k, (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ k *
      Selector.bit (S.selection k)) ≤
        (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j := by
    calc
      _ ≤ ∑ k, if k = j then
          (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j else 0 := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k = j
        · subst k
          simp [Selector.bit, hj]
        · simp only [hk, ↓reduceIte]
          apply mul_nonpos_of_nonpos_of_nonneg (MultipartiteDust.head_pair_nonpos _ hC _ _)
          cases S.selection k <;> norm_num [Selector.bit]
      _ = _ := by simp
  have hk : (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j =
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j.val)) :=
    (MultipartiteCountableMeasure.kernel_embed D S.size
      (.inl (some ⟨i, S.head_lt⟩)) (.inl (some j))).symm
  have hdust : 0 ≤ (S.dustCount : ℝ) * incident D i :=
    mul_nonneg (Nat.cast_nonneg _) (hD.1.1 _)
  have htriangle := anchored_head_pair_test hD i j.val hij
  unfold RepeatContext.row
  change head D i + _ - (S.dustCount : ℝ) * incident D i ≤ _
  rw [hk] at hsum
  linarith

/-- When every selected head is a zero-mass slot whose coefficients were
erased, the exterior is exactly the anchor-and-dust context. -/
theorem RepeatContext.threshold_eq_dust_of_zero_selected {D : Coefficients} {p : ℕ → ℝ}
    (hzero : ∀ j, p j = 0 → head D j = 0 ∧ incident D j = 0 ∧
      ∀ k, pair D j k = 0 ∧ pair D k j = 0)
    {i : ℕ} (S : RepeatContext i)
    (hselected : ∀ j : Fin S.size, S.selection j = true → p j.val = 0) :
    2 * S.row D + S.charge D - 1 = dustThreshold D i S.dustCount := by
  have hh : (∑ j, MultipartiteDust.head (restrict S.size D) j * Selector.bit (S.selection j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    cases hX : S.selection j
    · simp [Selector.bit]
    · change head D j.val * Selector.bit true = 0
      rw [(hzero j.val (hselected j hX)).1]
      simp
  have hinc : (∑ j, MultipartiteDust.incident (restrict S.size D) j * Selector.bit (S.selection j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    cases hX : S.selection j
    · simp [Selector.bit]
    · change incident D j.val * Selector.bit true = 0
      rw [(hzero j.val (hselected j hX)).2.1]
      simp
  have hpair : (∑ j, ∑ k, MultipartiteDust.pair (restrict S.size D) j k *
      (if j < k then 1 else 0) * Selector.bit (S.selection j) * Selector.bit (S.selection k)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    cases hX : S.selection j
    · simp [Selector.bit]
    · change pair D j.val k.val * _ * _ * _ = 0
      rw [((hzero j.val (hselected j hX)).2.2 k.val).1]
      simp
  have hrow : (∑ j, (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j *
      Selector.bit (S.selection j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    cases hX : S.selection j
    · simp [Selector.bit]
    · have hz := (hzero j.val (hselected j hX)).2.2 i
      have hk : (DustCellRestriction.headDual (restrict S.size D)).beta ⟨i, S.head_lt⟩ j = 0 := by
        dsimp only [DustCellRestriction.headDual]
        split_ifs
        · change -pair D i j.val = 0
          rw [hz.2]
          simp
        · change -pair D j.val i = 0
          rw [hz.1]
          simp
        · norm_num
      rw [hk]
      simp
  simp only [RepeatContext.row, RepeatContext.charge]
  rw [hrow]
  unfold MultipartiteDust.charge
  rw [hh, hpair, hinc]
  unfold dustThreshold
  change 2 * (head D i + 0 - (S.dustCount : ℝ) * incident D i) +
    (0 - 0 + (S.dustCount : ℝ) * (linear D - 0) -
      penalty D * S.dustCount * ((S.dustCount : ℝ) - 1) / 2) - 1 = _
  ring

/-- Every actual exterior either has a uniformly small threshold from
another positive head, or is exactly an anchor-and-dust threshold. -/
theorem RepeatContext.threshold_alternative {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hzero : ∀ j, p j = 0 → head D j = 0 ∧ incident D j = 0 ∧
      ∀ k, pair D j k = 0 ∧ pair D k j = 0)
    (ℓ : ℝ) (hhead : ∀ j, 0 < p j → ℓ ≤ head D j) {i : ℕ} (S : RepeatContext i) :
    2 * S.row D + S.charge D - 1 ≤ 1 - ℓ ∨
      2 * S.row D + S.charge D - 1 = dustThreshold D i S.dustCount := by
  by_cases hex : ∃ j : Fin S.size, S.selection j = true ∧ 0 < p j.val
  · obtain ⟨j, hj, hpj⟩ := hex
    have hrow := S.row_le_one_sub_head hD j hj
    have hsingle := S.one_test hD
    have hheadj := hhead j.val hpj
    left
    linarith
  · right
    apply S.threshold_eq_dust_of_zero_selected hzero
    intro j hj
    have hnot : ¬ 0 < p j.val := fun hpos => hex ⟨j, hj, hpos⟩
    exact le_antisymm (le_of_not_gt hnot) (hp j.val)

/-- A positive internal dust penalty bounds all large dust-only thresholds
by zero, with an explicit finite-cutoff argument. -/
theorem exists_dustThreshold_cutoff {D : Coefficients} (hD : D ∈ feasible)
    (hpen : 0 < penalty D) (i : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, N ≤ k → dustThreshold D i k ≤ 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / penalty D + 3)
  have hN3 : (3 : ℝ) < N := by
    have hdiv : 0 ≤ 4 / penalty D := by positivity
    linarith
  have hN0 : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  refine ⟨N, hN0, ?_⟩
  intro k hk
  have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (3 : ℝ) < k := hN3.trans_le hkN
  have hdiv : 4 / penalty D < (k : ℝ) - 1 := by linarith
  have hpk := (div_lt_iff₀ hpen).mp hdiv
  have hprod := mul_le_mul_of_nonneg_right hpk.le (Nat.cast_nonneg k)
  have ht : head D i ≤ 1 := hD.1.2 _
  have hv : linear D ≤ 1 := hD.1.2 _
  have hci : 0 ≤ incident D i := hD.1.1 _
  have hlinear := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg k)
  have hinc := mul_nonneg (Nat.cast_nonneg k) hci
  unfold dustThreshold
  nlinarith

/-- The actual two-copy supremum is attained by a finite anchor-and-dust
count once it lies above one half and the internal dust penalty is positive. -/
theorem exists_dust_witness {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hzero : ∀ j, p j = 0 → head D j = 0 ∧ incident D j = 0 ∧
      ∀ k, pair D j k = 0 ∧ pair D k j = 0)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ) (hhead : ∀ j, 0 < p j → ℓ ≤ head D j)
    (hpen : 0 < penalty D) (i : ℕ) (hti : head D i < 1) (hK : ℓ ≤ twoRepeatPenalty D i) :
    ∃ k : ℕ, twoRepeatPenalty D i = dustThreshold D i k ∧ ℓ ≤ dustThreshold D i k := by
  have hℓ1 : ℓ < 1 := hK.trans_lt ((twoRepeatPenalty_le_head hD i).trans_lt hti)
  obtain ⟨N, hN, hcut⟩ := exists_dustThreshold_cutoff hD hpen i
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range N) (dustThreshold D i)
    ⟨0, by simpa using hN⟩
  have hupper : twoRepeatPenalty D i ≤ max (dustThreshold D i k) (1 - ℓ) := by
    apply csSup_le ⟨0, Set.mem_insert 0 _⟩
    intro a ha
    rcases ha with rfl | ⟨S, rfl⟩
    · exact (show (0 : ℝ) ≤ 1 - ℓ by linarith).trans (le_max_right _ _)
    · change 2 * S.row D + S.charge D - 1 ≤ max (dustThreshold D i k) (1 - ℓ)
      rcases S.threshold_alternative hD p hp hzero ℓ hhead with hsmall | hdust
      · exact hsmall.trans (le_max_right _ _)
      · rw [hdust]
        by_cases hcount : S.dustCount < N
        · exact (hmax S.dustCount (Finset.mem_range.mpr hcount)).trans (le_max_left _ _)
        · exact (hcut S.dustCount (by omega)).trans
            ((show (0 : ℝ) ≤ 1 - ℓ by linarith).trans (le_max_right _ _))
  have hthreshold : ℓ ≤ dustThreshold D i k := by
    by_contra h
    have hmaxlt : max (dustThreshold D i k) (1 - ℓ) < ℓ :=
      max_lt (lt_of_not_ge h) (by linarith)
    exact (not_lt_of_ge (hK.trans hupper)) hmaxlt
  have hKupper : twoRepeatPenalty D i ≤ dustThreshold D i k := by
    rwa [max_eq_left (by linarith)] at hupper
  exact ⟨k, le_antisymm hKupper (dustThreshold_le_twoRepeatPenalty hD i k), hthreshold⟩

/-- With unused dust coefficients erased, every high two-copy penalty is
already witnessed by the sole dust-free exterior count zero. -/
theorem twoRepeatPenalty_eq_zero_dust_threshold {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hzero : ∀ j, p j = 0 → head D j = 0 ∧ incident D j = 0 ∧
      ∀ k, pair D j k = 0 ∧ pair D k j = 0)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ) (hhead : ∀ j, 0 < p j → ℓ ≤ head D j)
    (hv : linear D = 0) (hc : ∀ j, incident D j = 0) (hpD : penalty D = 0)
    (i : ℕ) (hti : head D i < 1) (hK : ℓ ≤ twoRepeatPenalty D i) :
    twoRepeatPenalty D i = dustThreshold D i 0 := by
  have hℓ1 : ℓ < 1 := hK.trans_lt ((twoRepeatPenalty_le_head hD i).trans_lt hti)
  have hconstant (k : ℕ) : dustThreshold D i k = dustThreshold D i 0 := by
    simp [dustThreshold, hv, hc, hpD]
  have hupper : twoRepeatPenalty D i ≤ max (dustThreshold D i 0) (1 - ℓ) := by
    apply csSup_le ⟨0, Set.mem_insert 0 _⟩
    intro a ha
    rcases ha with rfl | ⟨S, rfl⟩
    · exact (show (0 : ℝ) ≤ 1 - ℓ by linarith).trans (le_max_right _ _)
    · change 2 * S.row D + S.charge D - 1 ≤ max (dustThreshold D i 0) (1 - ℓ)
      rcases S.threshold_alternative hD p hp hzero ℓ hhead with hsmall | hdust
      · exact hsmall.trans (le_max_right _ _)
      · rw [hdust, hconstant]
        exact le_max_left _ _
  have hthreshold : ℓ ≤ dustThreshold D i 0 := by
    by_contra h
    have hmaxlt : max (dustThreshold D i 0) (1 - ℓ) < ℓ :=
      max_lt (lt_of_not_ge h) (by linarith)
    exact (not_lt_of_ge (hK.trans hupper)) hmaxlt
  rw [max_eq_left (by linarith)] at hupper
  exact le_antisymm hupper (dustThreshold_le_twoRepeatPenalty hD i 0)

end Erdos1017.MultipartiteCountableDual
