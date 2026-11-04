module

public import Erdos1017.Exclusions.Cusp.SelectedNeighborhoodCopyBody
public import Erdos1017.Exclusions.Cusp.KernelSignedCopyTrace
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeGeometry

/-!
# Signed trace on the neighborhood body at the third cusp

The neighborhood missing square and the independent atom square contribute
disjointly to the missing density, the signed trace holds on the neighborhood
body with a linear coefficient keeping the exterior missing-region mass, and
when that mass is at most gamma the neighborhood has zero positive-body energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original neighborhood missing square and original independent
atom square are disjoint contributions to the same missing density. -/
theorem neighborhood_missing_body_square_le (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood r)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) ≤
        1 - 2 * d - (S.originalAtomMass r) ^ 2 := by
  let G := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = r.val}
  let D := S.rootNeighborhood r
  let J := IndependentAtomCopy.missingBody G Dᶜ
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hD : MeasurableSet D := S.measurableSet_rootNeighborhood r
  have hJ := IndependentAtomCopy.measurable_missingBody G
    (PhysicalRepresentative.measurable_adjacency W m) Dᶜ hD.compl
  have hJsq : Integrable (fun p : Ω × Ω => (J p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hJ.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        dsimp [J, IndependentAtomCopy.missingBody]
        split_ifs <;> norm_num))
  have hII := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hI.prod hI)
  have hG : Integrable (fun p : Ω × Ω => if G p.1 p.2 = true then (1 : ℝ) else 0)
      (μ.prod μ) := Integrable.of_bound
    (Measurable.ite ((PhysicalRepresentative.measurable_adjacency W m)
      (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by split_ifs <;> norm_num))
  have hpoint : ∀ᵐ p ∂μ.prod μ, (J p.1 p.2) ^ 2 +
      (I ×ˢ I).indicator (fun _ => (1 : ℝ)) p ≤
      1 - (if G p.1 p.2 = true then (1 : ℝ) else 0) := by
    filter_upwards [S.ae_root_fiber_physical_independent r hW hd hgap] with p hp
    by_cases hxi : p.1 ∈ I
    · by_cases hyi : p.2 ∈ I
      · have hxd : p.1 ∉ D := fun h => Set.disjoint_left.mp (S.rootNeighborhood_disjoint r) hxi h
        have hzero : G p.1 p.2 = false := hp hxi hyi
        simp [J, IndependentAtomCopy.missingBody, hxi, hyi, hxd, hzero]
      · cases hxy : G p.1 p.2 <;> by_cases hxd : p.1 ∈ D <;>
          by_cases hyd : p.2 ∈ D <;>
          simp [J, IndependentAtomCopy.missingBody, hxi, hyi, hxd, hyd, hxy]
    · cases hxy : G p.1 p.2 <;> by_cases hxd : p.1 ∈ D <;>
        by_cases hyd : p.2 ∈ D <;>
        simp [J, IndependentAtomCopy.missingBody, hxi, hxd, hyd, hxy]
  have hbound := integral_mono_ae (hJsq.add hII) ((integrable_const 1).sub hG) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  rw [integral_add hJsq hII, integral_indicator (hI.prod hI), setIntegral_const,
    smul_eq_mul, mul_one, measureReal_prod_prod,
    integral_sub (integrable_const 1) hG, integral_const, probReal_univ, smul_eq_mul, mul_one]
    at hbound
  have hdensity := PhysicalRepresentative.density_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  rw [hW.density_eq] at hdensity
  unfold FiniteCappedSamplingCost.physicalDensity at hdensity
  change (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) ≤ 1 - 2 * d - (μ.real I) ^ 2
  dsimp only [G] at hbound
  nlinarith only [hbound, hdensity]

/-- The signed trace is proved on the original neighborhood body; its
linear coefficient retains the entire exterior missing-region mass. -/
theorem neighborhood_positive_body_signed_trace (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        (S.rootNeighborhood r)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) :
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      (S.rootNeighborhood r)ᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood r)ᶜ
    (S.originalAtomMass r - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion r)) *
        (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤ 0 := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let D := S.rootNeighborhood r
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => IndependentAtomCopy.missingBody_positiveBody_mul
          G Y Dᶜ (PhysicalRepresentative.charge_zero_of_nonedge W m) p.1 p.2)
      _ = 0 := integral_zero _ _
  exact KernelOperator.signed_copy_row_trace_bound K J
    (IndependentAtomCopy.measurable_positiveBody Y (PhysicalRepresentative.measurable_charge W m)
      Dᶜ (S.measurableSet_rootNeighborhood r).compl)
    (IndependentAtomCopy.measurable_missingBody G (PhysicalRepresentative.measurable_adjacency W m)
      Dᶜ (S.measurableSet_rootNeighborhood r).compl)
    (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem G Dᶜ x y).1]
      exact (IndependentAtomCopy.missingBody_mem G Dᶜ x y).2)
    (IndependentAtomCopy.positiveBody_symm Y Dᶜ (PhysicalRepresentative.charge_symm W m))
    (S.originalAtomMass r) (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion r))
    hpositive horth (S.ae_neighborhood_positive_body_row r hW hd hgap)

/-- If the entire missing-region mass is at most gamma at the low-slope
third cusp, its original neighborhood has zero positive-body energy. -/
theorem cusp_three_small_missing_body_zero (S : SelectedHighLowStructure W m) (i : S.I)
    {d c : ℝ} (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hsmall : μ.real (S.cuspThreeMissingRegion i) ≤ 2 * (c - m * d) + m) :
    (∫ p : Ω × Ω, (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
      (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) = 0 := by
  let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
    (S.rootNeighborhood i)ᶜ
  let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
    (S.rootNeighborhood i)ᶜ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨_, hA, hfloor⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  have hH := S.neighborhood_missing_body_square_le i hW hd hgap
  have hH0 : 0 ≤ ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun p => sq_nonneg _)
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH0)
  have hmargin : 0 < S.originalAtomMass i -
      Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ)) := by
    change (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      1 - 2 * d - (S.originalAtomMass i) ^ 2 at hH
    rw [hdk] at hH
    nlinarith only [hH, hfloor, hA, hsqrt, Real.sqrt_nonneg
      (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))]
  apply le_antisymm _ (integral_nonneg (fun p => sq_nonneg _))
  by_contra hn
  have hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ := lt_of_not_ge hn
  have htrace := S.neighborhood_positive_body_signed_trace i hW hd hgap hpositive
  have hlinear := mul_nonneg (sub_nonneg.mpr hsmall)
    (integral_nonneg (μ := μ.prod μ) (fun p : Ω × Ω => (IndependentAtomCopy.positiveBody_mem
      (PhysicalRepresentative.charge W m) (S.rootNeighborhood i)ᶜ
      (fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2) p.1 p.2).1))
  have hstrict := mul_pos hmargin hpositive
  change _ + _ ≤ 0 at htrace
  linarith only [htrace, hlinear, hstrict]

/-- The same small-missing-region case has no positive original physical
charge on its neighborhood square. This is the body sign used by marking. -/
theorem cusp_three_small_missing_body_nonpos (S : SelectedHighLowStructure W m) (i : S.I)
    {d c : ℝ} (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hsmall : μ.real (S.cuspThreeMissingRegion i) ≤ 2 * (c - m * d) + m) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood i → p.2 ∈ S.rootNeighborhood i →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ 0 := by
  let Y := PhysicalRepresentative.charge W m
  let D := S.rootNeighborhood i
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  have hzero := S.cusp_three_small_missing_body_zero i hdk hW hgap hglobal hell hpeak hsmall
  have hK := IndependentAtomCopy.measurable_positiveBody Y
    (PhysicalRepresentative.measurable_charge W m) Dᶜ (S.measurableSet_rootNeighborhood i).compl
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hi : Integrable (fun p : Ω × Ω => (K p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hK.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hmem := IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 p.1 p.2
        nlinarith only [hmem.1, hmem.2]))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun p : Ω × Ω => sq_nonneg (K p.1 p.2))) hi).mp hzero
  filter_upwards [hae] with p hp hx hy
  have hKzero : K p.1 p.2 = 0 := sq_eq_zero_iff.mp hp
  have hmax : max (Y p.1 p.2) 0 = 0 := by
    simpa [K, IndependentAtomCopy.positiveBody, D, hx, hy] using hKzero
  exact (le_max_left _ _).trans_eq hmax

end Erdos1017.CappedModel.SelectedHighLowStructure
