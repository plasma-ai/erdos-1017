module

public import Erdos1017.Exclusions.E2.Lower.SelectedLowerE2UniversalExclusion

/-!
# No universal saturated peak on the small parameters

The `E₂` deficit-ratio ceiling stays below `8/25` on the closed small-parameter
range including its rational right endpoint, and at the selected `E₂` contact
with `0 < q ≤ 7/50` a universal saturated common peak is impossible, the empty
partner-hole boundary being excluded by the two-universal theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.LowerE2Scalar

/-- The actual E2 deficit-ratio ceiling remains below 8/25 throughout the
closed small-parameter range, including its rational right endpoint. -/
theorem universal_middle_small_parameter_ratio {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) (7 / 50)) :
    9 * q / (2 * denominator q) ≤ 1575 / 4999 ∧ (1575 / 4999 : ℝ) < 8 / 25 := by
  refine ⟨?_, by norm_num⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) (denominator_pos hq.1))).mpr
  have hproduct := mul_nonneg (sub_nonneg.mpr hq.2)
    (show (0 : ℝ) ≤ 50 / 7 - q by linarith only [hq.2])
  unfold denominator
  nlinarith only [hproduct]

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

private theorem partner_universal_of_empty_holes (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hnull : μ (S.universalPartnerHoleRegion r p) = 0) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = p.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = p.val then 0 else 1 := by
  have hnotH : ∀ᵐ x ∂μ, x ∉ S.universalPartnerHoleRegion r p :=
    compl_mem_ae_iff.mpr hnull
  have hSAT := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp hpair.symm.row_on_other
  have hmneg := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hsets : ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood p ↔ S.ρ x ≠ p.val := by
    filter_upwards [hnotH, hSAT] with x hn hs
    constructor
    · exact fun h => h.1
    · intro hxp
      by_cases hxr : S.ρ x = r.val
      · exact ⟨hxp, by rw [hs hxr]; linarith only [hmneg]⟩
      · by_contra hnot
        exact hn (by
          intro hh
          rcases hh with (hh | hh) | hh
          · exact hxr hh
          · exact hxp hh
          · exact hnot hh)
  filter_upwards [S.ae_root_adjacency p hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_snd.ae hsets] with z hz ha hs hzp
  change adjacencyKernel W z.1 z.2 =
    (if PhysicalRepresentative.adjacency W m z.1 z.2 = true then 1 else 0) at ha
  by_cases hy : S.ρ z.2 = p.val
  · have hf : PhysicalRepresentative.adjacency W m z.1 z.2 = false :=
      Bool.eq_false_iff.mpr (fun he => (hs.mp ((hz hzp).mp he)) hy)
    simpa only [hf, Bool.false_eq_true, ite_false, hy, ite_true] using ha
  · have ht := (hz hzp).mpr (hs.mpr hy)
    simpa only [ht, ite_true, hy, ite_false] using ha

/-- At the selected E2 contact with 0<q≤7/50, a universal saturated
common peak is impossible. The empty partner-hole boundary is excluded by
the actual two-universal theorem; a positive entire hole region contradicts
the original single-row square integration and its 8/25 ratio floor. -/
theorem no_universal_middle_small_parameter_saturated_peak
    (S : SelectedHighLowStructure W m) (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (7 / 50))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → adjacencyKernel W z.1 z.2 =
      if S.ρ z.2 = r.val then 0 else 1) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨hq.1, by linarith only [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ Benchmark.e2_density_mem hq'
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  by_cases hnull : μ (S.universalPartnerHoleRegion r p) = 0
  · exact hpair.not_both_universal_e2 hW hq' hdq hgap hglobal huniv
      (S.partner_universal_of_empty_holes r p hpair hW hd hgap hnull)
  have hholes : 0 < μ (S.universalPartnerHoleRegion r p) := bot_lt_iff_ne_bot.mpr hnull
  have hlower := S.saturated_ratio_ge_eight_twentyFifths r p hpair hW hd hgap hell.2 hN hpeak hholes
  have hdelta : 0 < 1 + m := by linarith only [hell.2]
  have hdef : 1 - m - 4 * (c - m * d) <
      (1 + m) * (9 * q / (2 * LowerE2Scalar.denominator q)) := by
    have href := LowerE2Scalar.deficit_eq_gap_mul_ratio hq.1.le
    rw [show LowerE2Scalar.multiplier q = -m by linarith only [hm]] at href
    nlinarith only [href, hgamma]
  have hupper : (1 - m - 4 * (c - m * d)) / (1 + m) <
      9 * q / (2 * LowerE2Scalar.denominator q) :=
    (div_lt_iff₀ hdelta).mpr (by nlinarith only [hdef])
  obtain ⟨hcap, hstrict⟩ := LowerE2Scalar.universal_middle_small_parameter_ratio ⟨hq.1.le, hq.2⟩
  linarith only [hlower, hupper, hcap, hstrict]

end Erdos1017.CappedModel.SelectedHighLowStructure
