module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedExclusion
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairCompulsory
public import Erdos1017.Exclusions.E2.Middle.SelectedUniversalE2SmallHead

/-!
# Saturated dichotomy for remaining middle `E₂` contacts

Every remaining middle `E₂` contact has a saturated pair and an original common
peak; a peak on the pair is universal and larger than one third, and the other
case is described as well (`exists_middle_saturated_dichotomy`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- Every remaining middle-E2 contact has an actual saturated pair and an
original common peak. A peak on the pair is universal and larger than one
third. Otherwise the pair can be oriented so that the peak belongs to the
first head's entire compulsory source and has the literal private row.
All alternatives and numerical guards concern the same original model. -/
theorem exists_middle_saturated_dichotomy (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ i : S.I, S.IsCommonForwardPeak d c i ∧
      ((∃ p : S.I, S.IsSaturatedAtomPair i p ∧
        1 / 3 < S.originalAtomMass i ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N) ∧
        ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val → adjacencyKernel W z.1 z.2 =
          if S.ρ z.2 = i.val then 0 else 1) ∨
      ∃ p u : S.I, S.IsSaturatedAtomPair p u ∧ i ≠ p ∧ i ≠ u ∧
        19 / 160 < q ∧ S.originalAtomMass i ∈ Ioo (1 / 4 : ℝ) (1 / 3) ∧
        S.originalAtomMass i ≤ (1 - m - 2 * (2 * (c - m * d))) / (1 + m) ∧
        (1 - m - 2 * (2 * (c - m * d))) / (1 + m) < MiddleE2OffPair.ratioCap q ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p}) ∧
        ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val → adjacencyKernel W z.1 z.2 =
          if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hqclosed : q ∈ Icc (1 / 10 : ℝ) (1 / 5) := ⟨hq.1.le, hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  have hsat : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} ≠ 0 := by
    intro hnull
    exact S.no_middle_unsaturated_contact hW hq hdq hvalue hderiv hgap hglobal hnull
  obtain ⟨r, u, hpair⟩ := S.exists_saturated_atom_pair_of_positive_mass hW hd hgap hell
    (ENNReal.toReal_pos hsat (measure_ne_top _ _))
  obtain ⟨_, i, _, hside, hpeak, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  refine ⟨i, hpeak, ?_⟩
  by_cases hhead : i = r ∨ i = u
  · obtain ⟨p, hip⟩ : ∃ p : S.I, S.IsSaturatedAtomPair i p := by
      rcases hhead with hir | hiu
      · exact ⟨u, hir ▸ hpair⟩
      · exact ⟨r, hiu ▸ hpair.symm⟩
    have hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N := by
      rcases hside with hH | hN
      · have hnotH : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.H := by
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
            (hip.high_head_null hW hd hgap hell)),
            ae_restrict_mem (S.hfibers i.val i.property).1] with x hx hi hHx
          exact hx ⟨hi, hHx⟩
        obtain ⟨x, _, hxH, hxnot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
          (S.hfibers i.val i.property).2.1.ne' (hH.and hnotH)
        exact False.elim (hxnot hxH)
      · exact hN
    have huniv := S.neutral_atom_adjacency i hW hd hgap hN
    have hlarge : 1 / 3 < S.originalAtomMass i := by
      by_contra hn
      exact S.no_universal_e2_small_head_saturated_peak i p hip hW
        ⟨hq'.1, hq.2.le⟩ hdq hgap hglobal hpeak huniv (le_of_not_gt hn)
    exact Or.inl ⟨p, hip, hlarge, hN, huniv⟩
  · push Not at hhead
    obtain ⟨hir, hiu⟩ := hhead
    have hcut : 19 / 160 < q := by
      by_contra hn
      rcases S.middle_e2_common_peak_mem_saturated_pair i r u hpair hW
          ⟨hq.1.le, le_of_not_gt hn⟩ hdq hvalue hderiv hgap hglobal hpeak with hr | hu
      · exact hir hr
      · exact hiu hu
    have hthird := S.middle_e2_off_pair_peak_lt_third i r u hir hiu hpair hW hq
      hdq hvalue hderiv hgap hglobal hpeak
    have hratio := S.middle_e2_off_pair_peak_bounds i r u hir hiu hpair hW hqclosed
      hdq hvalue hderiv hgap hglobal hpeak
    obtain ⟨p, hp, hsource, hprivate⟩ := S.middle_e2_off_pair_private_row i r u hir hiu
      hpair hW hq hdq hvalue hderiv hgap hglobal hpeak
    have hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H :=
      hsource.mono (fun _ hx => hx.1)
    have hquarter := S.middle_e2_high_common_peak_quarter i hW hqclosed hdq hgap
      hglobal hpeak hhigh
    apply Or.inr
    rcases hp with hpr | hpu
    · subst p
      exact ⟨r, u, hpair, hir, hiu, hcut, ⟨hquarter, hthird⟩, hratio.1, hratio.2,
        hhigh, hsource, hprivate⟩
    · subst p
      exact ⟨u, r, hpair.symm, hiu, hir, hcut, ⟨hquarter, hthird⟩, hratio.1, hratio.2,
        hhigh, hsource, hprivate⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
