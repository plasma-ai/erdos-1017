module

public import Erdos1017.Exclusions.Common.FiniteReceiverSquareReserve
public import Erdos1017.Exclusions.Common.SelectedFiniteLowReceivers

/-!
# Class masses after a finite flow redirection

The kept atomic mass `keptAtomMass` outside the low region is defined, every
non-low whole fiber has endpoint class mass equal to its original mass plus its
receipt, and a finite redirected endpoint retains the countable non-low square
reserve plus every atomic-assigned source square.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual receipt into a cell contains all masses assigned to recipients
inside it. Other source columns and other recipients have nonnegative receipt. -/
theorem integral_receipt_finiteRedirect_ge_assigned {ι : Type*} {n : ℕ}
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C P : Fin n → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (hP : ∀ i, MeasurableSet (P i))
    (hpos : ∀ i, 0 < μ.real (C i)) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (κ : Fin n → Option ι) (k : ι) (T : Set Ω)
    (hCT : ∀ i, κ i = some k → C i ⊆ T) :
    (∑ i, if κ i = some k then θ i * μ.real (P i) else 0) ≤
      ∫ x in T, receipt μ (finiteRedirect μ q C P θ) x ∂μ := by
  let f : Fin n → Ω → ℝ := fun i x =>
    if κ i = some k then (θ i * μ.real (P i)) * (C i).indicator (fun _ => 1 / μ.real (C i)) x
    else 0
  have hf (i : Fin n) : Integrable (f i) μ := by
    dsimp only [f]
    split_ifs
    · exact ((integrable_const _).indicator (hC i)).const_mul _
    · exact integrable_const (0 : ℝ)
  have hle : ∀ᵐ x ∂μ, (∑ i, f i x) ≤ receipt μ (finiteRedirect μ q C P θ) x := by
    have hr0 := (nonnegative_marginals
      ((retainedFiniteSources_bounds q hq0 P θ hdis hθ).mono (fun _ hp => hp.1))).1
    filter_upwards [receipt_finiteRedirect q hq C P hC hP θ, hr0] with x he hr
    rw [he]
    refine le_trans ?_ (le_add_of_nonneg_left hr)
    apply Finset.sum_le_sum
    intro i _
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (hθ i).1 measureReal_nonneg)
        (indicator_nonneg (fun _ _ => by positivity) x)
  have hb := integral_mono_ae (μ := μ.restrict T)
    (integrable_finsetSum _ (fun i _ => (hf i).restrict))
    ((integrable_marginals (integrable_finiteRedirect q hq C P hC hP θ)).1.restrict)
    (ae_restrict_of_ae hle)
  rw [integral_finsetSum _ (fun i _ => (hf i).restrict)] at hb
  have he (i : Fin n) : (∫ x in T, f i x ∂μ) =
      if κ i = some k then θ i * μ.real (P i) else 0 := by
    by_cases hi : κ i = some k
    · have hzero : ∀ x, x ∉ T → f i x = 0 := by
        intro x hx
        have hc : x ∉ C i := fun hc => hx (hCT i hi hc)
        simp only [f, hi, ↓reduceIte, indicator_of_notMem hc, mul_zero]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      simp only [f, hi, ↓reduceIte]
      rw [integral_const_mul, integral_indicator (hC i), setIntegral_const,
        smul_eq_mul, mul_one_div, div_self (hpos i).ne', mul_one]
    · simp only [f, hi, ↓reduceIte, integral_zero]
  simpa only [he] using hb

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The original atomic mass retained outside LOW. This uses the actual
whole-fiber classification and does not assume a multipartite original model. -/
def keptAtomMass (S : SelectedHighLowStructure W m) (k : S.I) : ℝ :=
  if (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L) then 0 else S.originalAtomMass k

theorem keptAtomMass_nonnegative (S : SelectedHighLowStructure W m) (k : S.I) :
    0 ≤ S.keptAtomMass k := by
  unfold keptAtomMass
  split_ifs
  · exact le_rfl
  · exact S.originalAtomMass_summable.1 k

theorem keptAtomMass_le_original (S : SelectedHighLowStructure W m) (k : S.I) :
    S.keptAtomMass k ≤ S.originalAtomMass k := by
  unfold keptAtomMass
  split_ifs
  · exact S.originalAtomMass_summable.1 k
  · exact le_rfl

theorem keptAtomMass_sq_summable (S : SelectedHighLowStructure W m) :
    Summable (fun k => (S.keptAtomMass k) ^ 2) := by
  have hle (k : S.I) : (S.keptAtomMass k) ^ 2 ≤ S.originalAtomMass k := by
    have hnonneg := S.keptAtomMass_nonnegative k
    have hbound := S.keptAtomMass_le_original k
    have hmass : S.originalAtomMass k ≤ 1 := measureReal_le_one
    nlinarith
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle S.originalAtomMass_summable.2

namespace IsFullForwardFlow

variable {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Every actual nonLOW whole fiber has zero supply, and hence its true
endpoint class mass is its original mass plus its actual receipt. -/
theorem classMass_eq_original_add_receipt_nonlow (hq : S.IsFullForwardFlow q) (k : S.I)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∉ S.L) :
    S.forwardClassMass q k = S.originalAtomMass k +
      ∫ x in {x | S.ρ x = k}, MissingFlow.receipt μ q x ∂μ := by
  rw [S.forwardClassMass_eq_fiber]
  apply MissingFlow.endpoint_real_set_eq_add_receipt q hq.integrable hq.nonnegative
    hq.supply_le_one _ (S.hfibers k k.property).1
  filter_upwards [hq.supply, (ae_restrict_iff' (S.hfibers k k.property).1).mp hnonlow]
    with x hs hn hx
  rw [hs, indicator_of_notMem (hn hx)]

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual redirected class mass retains its original nonLOW mass and
receives every assigned source mass. Coinciding recipients remain one class. -/
theorem finite_classMass_ge_kept_add_sources (hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (hpos : ∀ i, 0 < μ.real (C i))
    (θ : Fin n → ℝ) (hdis : Pairwise (Disjoint on P))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (κ : Fin n → Option S.I)
    (hκ : ∀ i k, κ i = some k → θ i = 1 ∧ C i ⊆ {x | S.ρ x = k} ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H)) (k : S.I) :
    S.keptAtomMass k + (∑ i, if κ i = some k then μ.real (P i) else 0) ≤
      S.forwardClassMass (MissingFlow.finiteRedirect μ q C P θ) k := by
  by_cases hkL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L
  · have hnone (i : Fin n) : κ i ≠ some k := by
      intro hi
      have hkH := (hκ i k hi).2.2
      obtain ⟨x, _, hxH, hxL⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (S.hfibers k k.property).2.1.ne' (hkH.and hkL)
      exact Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxH hxL
    simp only [keptAtomMass, hkL, ↓reduceIte, hnone, Finset.sum_const_zero, add_zero]
    exact (ht.classMass_properties.1 k).1
  · have hnL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∉ S.L := by
      rcases S.hfiberClass k k.property with hH | hL | hN
      · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
      · exact False.elim (hkL hL)
      · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
    rw [ht.classMass_eq_original_add_receipt_nonlow k hnL]
    simp only [keptAtomMass, hkL, ↓reduceIte]
    have hreceipt := MissingFlow.integral_receipt_finiteRedirect_ge_assigned q hq.integrable
      hq.nonnegative C P hC hP hpos θ hdis hθ κ k {x | S.ρ x = k}
      (fun i hi => (hκ i k hi).2.1)
    have hb : (∑ i, if κ i = some k then μ.real (P i) else 0) ≤
        ∫ x in {x | S.ρ x = k}, MissingFlow.receipt μ
          (MissingFlow.finiteRedirect μ q C P θ) x ∂μ := by
      convert hreceipt using 1
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · rw [(hκ i k hi).1, one_mul]
      · rfl
    linarith

/-- One actual finite redirected endpoint retains the entire countable
original nonLOW square reserve and every atomic-assigned source square. -/
theorem finite_endpoint_square_reserve (hq : S.IsFullForwardFlow q) {n : ℕ}
    (C P : Fin n → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hP : ∀ i, MeasurableSet (P i)) (hpos : ∀ i, 0 < μ.real (C i))
    (θ : Fin n → ℝ) (hdis : Pairwise (Disjoint on P))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (ht : S.IsFullForwardFlow (MissingFlow.finiteRedirect μ q C P θ))
    (κ : Fin n → Option S.I)
    (hκ : ∀ i k, κ i = some k → θ i = 1 ∧ C i ⊆ {x | S.ρ x = k} ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H)) :
    (∑' k, (S.keptAtomMass k) ^ 2) +
        (∑ i, if κ i = none then 0 else (μ.real (P i)) ^ 2) ≤
      ∑' k, (S.forwardClassMass (MissingFlow.finiteRedirect μ q C P θ) k) ^ 2 := by
  have hbSum : Summable (fun k =>
      (S.forwardClassMass (MissingFlow.finiteRedirect μ q C P θ) k) ^ 2) := by
    have hp := ht.classMass_properties
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hp.2.1
    intro k
    have hk := hp.1 k
    nlinarith [hk.1, hk.2]
  apply FiniteReceiverReserve.tsum_square_ge_base_add_optional_sources
    S.keptAtomMass (S.forwardClassMass (MissingFlow.finiteRedirect μ q C P θ)) κ
    (fun i => μ.real (P i)) S.keptAtomMass_nonnegative (fun _ => measureReal_nonneg)
    S.keptAtomMass_sq_summable hbSum
  intro k
  convert hq.finite_classMass_ge_kept_add_sources C P hC hP hpos θ hdis hθ ht κ hκ k using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

end IsFullForwardFlow
end Erdos1017.CappedModel.SelectedHighLowStructure
