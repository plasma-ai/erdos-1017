module

public import Erdos1017.Exclusions.Common.Physical.PhysicalCountMeasure

/-!
# Residual count measure after removing parents

The measure `withoutRegion` keeps the joint parents avoiding a region, its count
law satisfies an exact additive identity with the original, and removing the
saturated-head parents subtracts exactly the root-to-head pair mass from the
cost and the head-to-`R` pair mass from the first `R` moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Retain the actual joint parents that avoid the specified region.
No rerouting or replacement of a singular parent is performed. -/
def withoutRegion (η : Laws Ω) (A : Set Ω) : Laws Ω :=
  fun n => (η n).restrict {v | ∀ i, v i ∉ A}

theorem measurableSet_avoidsRegion {n : ℕ} (A : Set Ω) (hA : MeasurableSet A) :
    MeasurableSet {v : Fin n → Ω | ∀ i, v i ∉ A} := by
  have h := MeasurableSet.iInter (fun i : Fin n => (hA.preimage (measurable_pi_apply i)).compl)
  convert h using 1
  ext v
  simp

instance withoutRegion_finite (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (A : Set Ω) (n : ℕ) :
    IsFiniteMeasure (withoutRegion η A n) := by
  unfold withoutRegion
  infer_instance

theorem withoutRegion_cap (N : ℕ) (η : Laws Ω) (A : Set Ω)
    (hcap : ∀ n, N < n → η n = 0) (n : ℕ) (hn : N < n) : withoutRegion η A n = 0 := by
  simp [withoutRegion, hcap n hn]

private theorem integral_withoutRegion_countMeasure
    (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (A R E : Set Ω) (hA : MeasurableSet A) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (F : ℕ × ℕ → ℝ) :
    (∫ z, F z ∂countMeasure N (withoutRegion η A) R E) =
      ∑ n ∈ Finset.range (N + 1), ∫ v,
        {v : Fin n → Ω | ∀ i, v i ∉ A}.indicator
          (fun v => F (tupleCount R v, tupleCount E v)) v ∂η n := by
  rw [integral_countMeasure N (withoutRegion η A) R E hR hE F]
  apply Finset.sum_congr rfl
  intro n _
  exact (integral_indicator (measurableSet_avoidsRegion A hA)).symm

/-- A literal identity on each original parent gives an exact additive
identity for the residual count law. All three measures are constructed
pushforwards of the actual original laws. -/
theorem integral_residual_add (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (A R E : Set Ω) (hA : MeasurableSet A) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (F G : ℕ × ℕ → ℝ)
    (hsplit : ∀ n, ∀ᵐ v ∂η n,
      (if ∃ i, v i ∈ A then 0 else F (tupleCount R v, tupleCount E v)) +
        G (tupleCount A v, tupleCount R v) = F (tupleCount R v, tupleCount E v)) :
    (∫ z, F z ∂countMeasure N (withoutRegion η A) R E) +
      (∫ z, G z ∂countMeasure N η A R) = ∫ z, F z ∂countMeasure N η R E := by
  rw [integral_withoutRegion_countMeasure N η A R E hA hR hE F,
    integral_countMeasure N η A R hA hR G, integral_countMeasure N η R E hR hE F,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← integral_add ((integrable_count_function (η n) R E hR hE F).indicator
    (measurableSet_avoidsRegion A hA)) (integrable_count_function (η n) A R hA hR G)]
  apply integral_congr_ae
  filter_upwards [hsplit n] with v hv
  by_cases hh : ∃ i, v i ∈ A
  · have hn : ¬∀ i, v i ∉ A := by simpa only [not_forall, not_not] using hh
    change v ∉ {v : Fin n → Ω | ∀ i, v i ∉ A} at hn
    rw [Set.indicator_of_notMem hn]
    simpa only [hh, ↓reduceIte] using hv
  · have hn : ∀ i, v i ∉ A := by simpa only [not_exists] using hh
    change v ∈ {v : Fin n → Ω | ∀ i, v i ∉ A} at hn
    rw [Set.indicator_of_mem hn]
    simpa only [hh, ↓reduceIte] using hv

/-- A count statistic that vanishes on every removed parent has exactly
the same integral on the residual and original count measures. -/
theorem integral_residual_eq (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (A R E : Set Ω) (hA : MeasurableSet A) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (F : ℕ × ℕ → ℝ)
    (hzero : ∀ n, ∀ᵐ v ∂η n, (∃ i, v i ∈ A) → F (tupleCount R v, tupleCount E v) = 0) :
    (∫ z, F z ∂countMeasure N (withoutRegion η A) R E) = ∫ z, F z ∂countMeasure N η R E := by
  have he := integral_residual_add N η A R E hA hR hE F (fun _ => 0) (by
    intro n
    filter_upwards [hzero n] with v hv
    by_cases hh : ∃ i, v i ∈ A
    · simp [hh, hv hh]
    · simp [hh])
  simpa using he

omit [MeasurableSpace Ω] in
private theorem tupleCount_zero_of_no_mem {n : ℕ} (A : Set Ω) (v : Fin n → Ω)
    (h : ¬∃ i, v i ∈ A) : tupleCount A v = 0 := by
  simp only [not_exists] at h
  simp [tupleCount, h]

/-- Removing the actual saturated-head parents subtracts precisely the
root-to-head pair mass from cost and the head-to-R pair mass from the
first R moment. The other four moments are unchanged. -/
theorem residual_count_moments (N : ℕ) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I A R E : Set Ω) (hI : MeasurableSet I) (hA : MeasurableSet A)
    (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hIA : Disjoint I A) (hIR : Disjoint I R) (hIE : Disjoint I E)
    (hAR : Disjoint A R) (hRE : Disjoint R E)
    (hroot : ∀ n, ∀ᵐ v ∂η n, ∃! i, v i ∈ I)
    (hshape : ∀ n, ∀ᵐ v ∂η n, (∃ i, v i ∈ A) →
      tupleCount A v = 1 ∧ tupleCount E v = 0 ∧ tupleCount R v ≤ 1)
    (hcap : ∀ n, N < n → η n = 0) (demand : Measure (Ω × Ω)) [IsFiniteMeasure demand]
    (hbalance : occupation η = demand) :
    let θ := countMeasure N (withoutRegion η A) R E
    θ.real univ = cost η - demand.real (I ×ˢ A) ∧
      (∫ z, (z.1 : ℝ) ∂θ) = demand.real (I ×ˢ R) - demand.real (A ×ˢ R) ∧
      (∫ z, (z.2 : ℝ) ∂θ) = demand.real (I ×ˢ E) ∧
      (∫ z, (z.1 : ℝ) * ((z.1 : ℝ) - 1) ∂θ) = demand.real (R ×ˢ R) ∧
      (∫ z, (z.2 : ℝ) * ((z.2 : ℝ) - 1) ∂θ) = demand.real (E ×ˢ E) ∧
      (∫ z, (z.1 : ℝ) * (z.2 : ℝ) ∂θ) = demand.real (R ×ˢ E) := by
  have hmass := integral_residual_add N η A R E hA hR hE (fun _ => 1) (fun z => z.1) (by
    intro n
    filter_upwards [hshape n] with v hv
    by_cases hh : ∃ i, v i ∈ A
    · simp [hh, (hv hh).1]
    · simp [hh, tupleCount_zero_of_no_mem A v hh])
  simp only [integral_const, smul_eq_mul, mul_one] at hmass
  rw [countMeasure_first_moment N η I A R hI hA hR hIA hroot hcap demand hbalance,
    countMeasure_mass N η R E hR hE hcap] at hmass
  have hfirst := integral_residual_add N η A R E hA hR hE (fun z => z.1)
    (fun z => (z.1 : ℝ) * (z.2 : ℝ)) (by
      intro n
      filter_upwards [hshape n] with v hv
      by_cases hh : ∃ i, v i ∈ A
      · simp [hh, (hv hh).1]
      · simp [hh, tupleCount_zero_of_no_mem A v hh])
  rw [countMeasure_cross_moment N η A R hA hR hAR hcap demand hbalance,
    countMeasure_first_moment N η I R E hI hR hE hIR hroot hcap demand hbalance] at hfirst
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [integral_residual_eq N η A R E hA hR hE (fun z => (z.2 : ℝ)) (by
      intro n
      filter_upwards [hshape n] with v hv hh
      simp [(hv hh).2.1])]
    exact countMeasure_second_moment N η I R E hI hR hE hIE hroot hcap demand hbalance
  · rw [integral_residual_eq N η A R E hA hR hE
      (fun z => (z.1 : ℝ) * ((z.1 : ℝ) - 1)) (by
        intro n
        filter_upwards [hshape n] with v hv hh
        have hk := (hv hh).2.2
        interval_cases h : tupleCount R v <;> norm_num)]
    exact countMeasure_factorial_moment N η R E hR hE hcap demand hbalance
  · rw [integral_residual_eq N η A R E hA hR hE
      (fun z => (z.2 : ℝ) * ((z.2 : ℝ) - 1)) (by
        intro n
        filter_upwards [hshape n] with v hv hh
        simp [(hv hh).2.1])]
    exact countMeasure_second_factorial_moment N η R E hR hE hcap demand hbalance
  · rw [integral_residual_eq N η A R E hA hR hE
      (fun z => (z.1 : ℝ) * (z.2 : ℝ)) (by
        intro n
        filter_upwards [hshape n] with v hv hh
        simp [(hv hh).2.1])]
    exact countMeasure_cross_moment N η R E hR hE hRE hcap demand hbalance

end Erdos1017.PhysicalPrimal
