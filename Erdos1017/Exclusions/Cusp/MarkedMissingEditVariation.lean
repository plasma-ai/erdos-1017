module

public import Erdos1017.Exclusions.Cusp.MarkedMissingEditValues
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeMissingReturn
public import Erdos1017.Exclusions.Cusp.FullSplitCuspContact

/-!
# Variation of the marked missing edit at the third cusp

A quadratic marked edit with positive density derivative is controlled by the
right benchmark derivative at a global maximum, and the independently marked
missing region is compared at its changed density to the same selected global
excess maximum (`cusp_three_missing_edit_sign`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical Topology

namespace Erdos1017.MarkedMissingEdit

/-- A genuine quadratic marked edit with positive density derivative is
controlled by the actual right benchmark derivative at a global maximum. -/
theorem quadratic_right_variation {B : ℝ → ℝ} {d c a z y q beta : ℝ}
    (ha : 0 < a) (hz : 0 ≤ z)
    (hB : HasDerivWithinAt B beta (Ici d) d)
    (hmax : ∀ alpha ∈ Icc (0 : ℝ) 1,
      c + alpha * y + alpha ^ 2 * q - B (d + alpha * a + alpha ^ 2 * z) ≤ c - B d) :
    y - beta * a ≤ 0 := by
  let D := fun alpha : ℝ => d + alpha * a + alpha ^ 2 * z
  let Y := fun alpha : ℝ => c + alpha * y + alpha ^ 2 * q
  let H := fun alpha : ℝ => Y alpha - B (D alpha)
  have hD0 : D 0 = d := by simp [D]
  have hD : HasDerivAt D a 0 := by
    convert ((hasDerivAt_const (0 : ℝ) d).add ((hasDerivAt_id 0).mul_const a)).add
      (((hasDerivAt_id 0).pow 2).mul_const z) using 1
    · rfl
    · simp
  have hY : HasDerivAt Y y 0 := by
    convert ((hasDerivAt_const (0 : ℝ) c).add ((hasDerivAt_id 0).mul_const y)).add
      (((hasDerivAt_id 0).pow 2).mul_const q) using 1
    · rfl
    · simp
  have hstrict {alpha : ℝ} (halpha : 0 < alpha) : d < D alpha := by
    have hfirst := mul_pos halpha ha
    have hsecond := mul_nonneg (sq_nonneg alpha) hz
    dsimp [D]
    linarith only [hfirst, hsecond]
  have hmaps : MapsTo D (Ici 0) (Ici d) := by
    intro alpha halpha
    rcases halpha.eq_or_lt with rfl | hpos
    · exact hD0.ge
    · exact (hstrict hpos).le
  have hcomp := hB.comp_of_eq 0 hD.hasDerivWithinAt hmaps hD0.symm
  have hH : HasDerivWithinAt H (y - beta * a) (Ici 0) 0 := hY.hasDerivWithinAt.sub hcomp
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hH.Ioi_of_Ici
  apply le_of_tendsto ht
  have hsmall0 : ∀ᶠ alpha : ℝ in 𝓝 0, alpha < 1 := Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hsmall : ∀ᶠ alpha : ℝ in 𝓝[>] 0, alpha < 1 := hsmall0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with alpha hsmall hpositive
  rw [slope_def_field]
  have hbound : H alpha ≤ H 0 := by
    simpa only [H, Y, D, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      hmax alpha ⟨hpositive.le, hsmall.le⟩
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbound) (by simpa using hpositive.le)

end Erdos1017.MarkedMissingEdit

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- The literal independently marked entire missing region is compared at
its actual changed density to the same selected global excess maximum.
No edit derivative sign, edited test, or corrected competitor is supplied. -/
theorem cusp_three_missing_edit_sign (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1))
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood i → p.2 ∈ S.rootNeighborhood i →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ 0) :
    let J := S.cuspThreeMissingRegion i
    let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
    let v := ∫ p in J ×ˢ S.rootNeighborhood i, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    let FJ := ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ
    (5 / 6) * v - FJ + (-2 * m - 5 / 3) * z ≤ 0 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let FJ := ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ
  let YJJ := ∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hstructure := hW.strict_gap_structure hd hgap
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood i
  have hdis : Disjoint J N := disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  have hAsym := PhysicalRepresentative.adjacency_symm W m
  have hYsym := PhysicalRepresentative.charge_symm W m
  have hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (S.ae_root_adjacency i hW hd hgap)] with p hp hx hy
    have hi : S.ρ p.2 = i.val := by
      by_contra hi
      exact hy (Or.inl ⟨hi, fun hn => hy (Or.inr hn)⟩)
    apply Bool.eq_false_iff.mpr
    intro ha
    have ha' : A p.2 p.1 = true := (hAsym _ _).trans ha
    exact hx.2 ((hp hi).mp ha')
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hstructure.strict_support hW.deterministic
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hC : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (chargeKernel_measurable W)
      (chargeKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hArep := PhysicalRepresentative.adjacency_moment_ae_eq W m hstructure.strict_support
  have hYrep := PhysicalRepresentative.charge_ae_eq W m hstructure.strict_support
  let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  have hGphys : Integrable G (μ.prod μ) := hG.congr hArep
  have hJN := ((integrable_const 1).sub hGphys).indicator (hJ.prod hN)
  have hJJ := hGphys.indicator (hJ.prod hJ)
  have hcross : (∫ p in J ×ˢ N, 1 - G p ∂μ.prod μ) = v := by
    apply integral_congr_ae
    exact (ae_restrict_of_ae hArep).mono (fun _ hp => congrArg (fun x : ℝ => 1 - x) hp.symm)
  have hsquare : (∫ p in J ×ˢ J, G p ∂μ.prod μ) = 2 * z := by
    have he : (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
        ∫ p in J ×ˢ J, G p ∂μ.prod μ := integral_congr_ae (ae_restrict_of_ae hArep)
    dsimp [z]
    linarith only [he]
  have hlinear : (∫ p : Ω × Ω, MarkedMissingEdit.densityLinear A J N p.1 p.2 ∂μ.prod μ) = v - 2 * z := by
    have he := integral_sub hJN hJJ
    rw [integral_indicator (hJ.prod hN), integral_indicator (hJ.prod hJ)] at he
    simp only [Pi.sub_apply] at he
    rw [hcross, hsquare] at he
    exact he
  have hquadratic : (∫ p : Ω × Ω, MarkedMissingEdit.densityQuadratic A J p.1 p.2 ∂μ.prod μ) = z := by
    have he : (∫ p : Ω × Ω, MarkedMissingEdit.densityQuadratic A J p.1 p.2 ∂μ.prod μ) =
        (∫ p in J ×ˢ J, G p ∂μ.prod μ) / 2 := by
      rw [← integral_indicator (hJ.prod hJ), ← integral_div]
      rfl
    rw [he, hsquare]
    ring
  have hobjective : (∫ p : Ω × Ω, MarkedMissingEdit.objectiveLinear Y J p.1 p.2 ∂μ.prod μ) = -YJJ := by
    change (∫ p, -(J ×ˢ J).indicator (Function.uncurry Y) p ∂μ.prod μ) = _
    rw [integral_neg, integral_indicator (hJ.prod hJ)]
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae hYrep)
  have hFJ : FJ = YJJ - m * (2 * z) := by
    have he : (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) =
        fun p => chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 := by
      funext p
      exact shiftedMoment_eq W m p
    dsimp [FJ, YJJ, z]
    rw [he, integral_sub hC.integrableOn (hG.integrableOn.const_mul m), integral_const_mul]
    ring
  obtain ⟨hz, _, hL, _, _, _⟩ := S.cusp_three_missing_return i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 ≤ z at hz
  change 0 < v - 2 * z at hL
  have hright : HasDerivWithinAt benchmark (-(5 / 6 : ℝ)) (Ici d) d := by
    have he := (Benchmark.split_cusp_right_hasDerivAt 3 (by norm_num)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      (Benchmark.benchmark_split_cusp_right_eventually 3 (by norm_num)) le_rfl
    norm_num at he
    simpa only [hdk] using he
  have hdold := (PhysicalRepresentative.density_eq W m hstructure.strict_support).trans hW.density_eq
  have hcold := (PhysicalRepresentative.objective_eq W m hstructure.strict_support).trans hW.objective_eq
  have hsign : -YJJ - (-(5 / 6 : ℝ)) * (v - 2 * z) ≤ 0 := by
    apply MarkedMissingEdit.quadratic_right_variation (q := YJJ / 2) hL hz hright
    intro alpha halpha
    let alpha' : unitInterval := ⟨alpha, halpha⟩
    have hden := MarkedMissingEdit.density_marked (μ := μ) alpha' A J N hA hJ hN hdis hAsym
    have hcost := MarkedMissingEdit.objective_marked (μ := μ) alpha' Y J hY hJ 3 (by norm_num)
      (PhysicalRepresentative.charge_bound W m)
    rw [hdold, hlinear, hquadratic] at hden
    rw [hcold, hobjective] at hcost
    have hcost' : FiniteCappedSamplingCost.physicalObjective (universalMeasure μ alpha')
        (MarkedMissingEdit.charge Y J) = c + alpha * -YJJ + alpha ^ 2 * (YJJ / 2) := by
      linarith only [hcost]
    have hcomp := MarkedMissingEdit.objective_le_densityLimit_ac A Y J N hA hY hJ hN hdis hAsym hYsym
      3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
      (PhysicalRepresentative.charge_zero_of_nonedge W m) hmiss hbody hfull μ Measure.AbsolutelyContinuous.rfl alpha'
    have hdenmem := FiniteCappedSamplingCost.physicalDensity_mem_Icc
      (μ := universalMeasure μ alpha') (MarkedMissingEdit.adjacency A J N)
      (MarkedMissingEdit.adjacency_symm A J N hAsym) (MarkedMissingEdit.measurable_adjacency A J N hA hJ hN)
    obtain ⟨V, hV, hdV, hcV⟩ := exists_fullFeasible_at_density (μ := μ) _ hdenmem
    have hbound := hglobal μ V hV
    rw [hcV, hdV, hW.objective_eq, hW.density_eq] at hbound
    rw [hcost'] at hcomp
    rw [hden] at hcomp hbound
    change c + alpha * -YJJ + alpha ^ 2 * (YJJ / 2) -
      benchmark (d + alpha * (v - 2 * z) + alpha ^ 2 * z) ≤ c - benchmark d
    linarith only [hcomp, hbound]
  change (5 / 6) * v - FJ + (-2 * m - 5 / 3) * z ≤ 0
  nlinarith only [hsign, hFJ]

end Erdos1017.CappedModel.SelectedHighLowStructure
