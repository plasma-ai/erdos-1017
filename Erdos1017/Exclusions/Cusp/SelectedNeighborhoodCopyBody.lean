module

public import Erdos1017.Exclusions.Cusp.SelectedCommonNeighborhoodCopy
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyBody

/-!
# Copied-row bound on the neighborhood body

The two signed missing rows are paid by the original neighborhood body and one
copy of the entire exterior missing-region mass, and the positive neighborhood
body satisfies the copied-row bound with that region paid once.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The two signed missing rows are paid by the original neighborhood
body and one copy of the entire exterior missing-region mass. -/
theorem missing_pair_integral_le_neighborhood (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I D : Set Ω)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hdisj : Disjoint I D)
    (hYB : ∀ x y, ‖Y x y‖ ≤ 3) (hY1 : ∀ x y, Y x y ≤ 1)
    (hzero : ∀ x y, G x y = false → Y x y = 0)
    (hsym : ∀ x y, Y x y = Y y x) (x y : Ω) (hx : x ∈ D) (hy : y ∈ D)
    (hcommon : ∀ᵐ z ∂μ, z ∈ I → G x z = true ∧ G y z = true) :
    (∫ z in missingSection G x, Y y z ∂μ) +
      (∫ z in missingSection G y, Y x z ∂μ) ≤
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) x y +
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) y x +
      μ.real (Iᶜ \ D) := by
  let K := positiveBody Y Dᶜ
  let J := missingBody G Dᶜ
  have hK := measurable_positiveBody Y hY Dᶜ hD.compl
  have hJ := measurable_missingBody G hG Dᶜ hD.compl
  have hrow (u : Ω) : Integrable (Y u) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hYB u))
  have hprod (u v : Ω) : Integrable (fun z => J u z * K z v) μ :=
    Integrable.of_bound
      ((hJ.comp (measurable_const.prodMk measurable_id)).mul
        (hK.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (missingBody_mem G Dᶜ u z).1,
          abs_of_nonneg (positiveBody_mem Y Dᶜ hY1 z v).1]
        exact (mul_le_mul (missingBody_mem G Dᶜ u z).2
          (positiveBody_mem Y Dᶜ hY1 z v).2
          (positiveBody_mem Y Dᶜ hY1 z v).1 zero_le_one).trans_eq (mul_one 1)))
  have hmissingX := measurableSet_missingSection G hG x
  have hmissingY := measurableSet_missingSection G hG y
  have htax := (integrable_const (1 : ℝ) (μ := μ)).indicator (hI.compl.diff hD)
  have hprodAdd : Integrable (fun z => J x z * K z y + J y z * K z x) μ :=
    (hprod x y).add (hprod y x)
  have hbound : (∫ z, (missingSection G x).indicator (Y y) z +
      (missingSection G y).indicator (Y x) z ∂μ) ≤
      ∫ z, J x z * K z y + J y z * K z x +
        (Iᶜ \ D).indicator (fun _ => (1 : ℝ)) z ∂μ := by
    apply integral_mono_ae ((hrow y).indicator hmissingX |>.add ((hrow x).indicator hmissingY))
      (((hprod x y).add (hprod y x)).add htax)
    filter_upwards [hcommon] with z hz
    by_cases hzi : z ∈ I
    · have hzd : z ∉ D := fun h => Set.disjoint_left.mp hdisj hzi h
      obtain ⟨hGx, hGy⟩ := hz hzi
      simp [J, K, missingSection, missingBody, positiveBody, hzi, hzd, hGx, hGy]
    · by_cases hzd : z ∈ D
      · cases hGx : G x z <;> cases hGy : G y z <;>
          simp [J, K, missingSection, missingBody, positiveBody, hx, hy, hzi, hzd,
            hGx, hGy, hsym z x, hsym z y]
        exact add_le_add (le_max_left _ _) (le_max_left _ _)
      · simpa [J, K, missingBody, positiveBody, hzi, hzd] using
          missing_row_tax_le_one G Y hzero hY1 x y z
  rw [integral_add ((hrow y).indicator hmissingX) ((hrow x).indicator hmissingY),
    integral_indicator hmissingX, integral_indicator hmissingY,
    integral_add hprodAdd htax,
    integral_add (hprod x y) (hprod y x), integral_indicator (hI.compl.diff hD),
    setIntegral_const, smul_eq_mul, mul_one] at hbound
  exact hbound

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original positive neighborhood body satisfies the copied-row
bound with the entire outside missing region paid once. The coefficient
gamma minus its mass may have either sign. -/
theorem ae_neighborhood_positive_body_row (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let D := S.rootNeighborhood r
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
    ∀ᵐ p ∂μ.prod μ, μ.real {x | S.ρ x = r.val} * (K p.1 p.2) ^ 2 +
      (2 * (c - m * d) + m - μ.real ({x | S.ρ x = r.val}ᶜ \ D)) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let D := S.rootNeighborhood r
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency r hW hd hgap)
  have hrows : ∀ᵐ x ∂μ, x ∈ D → ∀ᵐ z ∂μ, z ∈ I → G x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxn
    filter_upwards [hx] with z hz hzi
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzi).mpr hxn
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_common_neighborhood_copy_inequality r hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hrows, Measure.quasiMeasurePreserving_snd.ae hrows]
    with p hp hx hy
  change μ.real I * (K p.1 p.2) ^ 2 +
    (2 * (c - m * d) + m - μ.real (Iᶜ \ D)) * K p.1 p.2 ≤
    K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
      KernelOperator.composedKernel (μ := μ) J K p.2 p.1)
  by_cases hpos : 0 < K p.1 p.2
  · have hout : p.1 ∈ D ∧ p.2 ∈ D := by
      by_contra h
      simp [K, IndependentAtomCopy.positiveBody, h] at hpos
    have hKeq : K p.1 p.2 = Y p.1 p.2 := by
      have hmax : 0 < max (Y p.1 p.2) 0 := by
        simpa [K, IndependentAtomCopy.positiveBody, hout] using hpos
      have hypos : 0 < Y p.1 p.2 := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmax
      simp [K, IndependentAtomCopy.positiveBody, hout, max_eq_left hypos.le]
    have hypos : 0 < Y p.1 p.2 := by rwa [hKeq] at hpos
    have hc := hp hout.1 hout.2 hypos
    have hcommon : ∀ᵐ z ∂μ, z ∈ I → G p.1 z = true ∧ G p.2 z = true := by
      filter_upwards [hx hout.1, hy hout.2] with z hx hy hi
      exact ⟨hx hi, hy hi⟩
    have hpair := IndependentAtomCopy.missing_pair_integral_le_neighborhood G
      (PhysicalRepresentative.measurable_adjacency W m) Y
      (PhysicalRepresentative.measurable_charge W m) I D (S.hfibers r.val r.property).1
      (S.measurableSet_rootNeighborhood r) (S.rootNeighborhood_disjoint r)
      (PhysicalRepresentative.charge_bound W m) hY1
      (PhysicalRepresentative.charge_zero_of_nonedge W m)
      (PhysicalRepresentative.charge_symm W m) p.1 p.2 hout.1 hout.2 hcommon
    have hmass : 0 ≤ μ.real (IndependentAtomCopy.missingSection G p.1 ∩
        IndependentAtomCopy.missingSection G p.2) := measureReal_nonneg
    have hbound : μ.real I * K p.1 p.2 + (2 * (c - m * d) + m - μ.real (Iᶜ \ D)) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 := by
      change μ.real I * Y p.1 p.2 + _ - m * μ.real _ ≤ _ at hc
      rw [hKeq]
      dsimp only [J, K] at *
      nlinarith only [hc, hpair, mul_nonpos_of_nonpos_of_nonneg hm.le hmass]
    have h := mul_le_mul_of_nonneg_right hbound hpos.le
    nlinarith only [h]
  · have hzero : K p.1 p.2 = 0 := le_antisymm (le_of_not_gt hpos)
      (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 p.1 p.2).1
    rw [hzero]
    simp

end Erdos1017.CappedModel.SelectedHighLowStructure
