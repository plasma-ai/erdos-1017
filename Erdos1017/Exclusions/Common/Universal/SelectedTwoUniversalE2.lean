module

public import Erdos1017.Exclusions.Common.Universal.SelectedTwoUniversalGeometry
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairIncidence
public import Erdos1017.Exclusions.Common.Universal.TwoUniversalE2Scalar
public import Erdos1017.Exclusions.Common.Flows.FullForwardQuarterFloor

/-!
# No two universal atoms at a global `E₂` contact

At a global `E₂` excess contact two saturated atoms cannot both be neutral, and
hence cannot both be universal, since their neutral positions follow from their
adjacency rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

attribute [local instance] Classical.propDecidable

private theorem no_ordered_two_universal_e2 {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c) (hm : m = -LowerE2Scalar.multiplier q) (hell : -m < 1)
    (hNr : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hNu : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, x ∈ S.N)
    (horder : μ.real {x | S.ρ x = u.val} ≤ μ.real {x | S.ρ x = r.val}) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  let s := μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val}
  let v := μ.real {x | S.ρ x = r.val} - μ.real {x | S.ρ x = u.val}
  let T := (1 + m) * s - 2 * (2 * c + m * (1 - 2 * d))
  have hgeometry := hpair.two_universal_support_geometry hW hd hgap hell hNr hNu horder
  change s < 1 ∧ 0 ≤ v ∧ s ^ 2 + v ^ 2 ≤ 2 * (1 - 2 * d) ∧ 0 ≤ T ∧
    (1 + m) * (s - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * s - 1) * T -
      (1 - s) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - s) / 12) 0 ^ 2 ≤ 0
    at hgeometry
  obtain ⟨hs1, hv, hcircle, hT, hupper⟩ := hgeometry
  have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by
    rw [hdq]
    ring
  have hdelta : 0 < 1 - LowerE2Scalar.multiplier q := by
    rw [hm, neg_neg] at hell
    linarith
  have hcorrelation : T = (1 - LowerE2Scalar.multiplier q) *
      (s - TwoUniversalE2Scalar.width q c) := by
    dsimp only [T]
    rw [hm, hmissing]
    unfold TwoUniversalE2Scalar.width
    field_simp [hdelta.ne']
    ring
  have hs : TwoUniversalE2Scalar.width q c ≤ s := by
    rw [hcorrelation] at hT
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hdelta).mp hT)
  have hc : benchmark ((1 - LowerE2Scalar.missingMass q) / 2) < c := by
    simpa only [hdq] using hgap
  rw [hmissing] at hcircle
  have hpositive := TwoUniversalE2Scalar.supportPolynomial_pos hq hc hs hs1 hv hcircle
    hcorrelation
  have hnonpositive : TwoUniversalE2Scalar.supportPolynomial q s v T ≤ 0 := by
    unfold TwoUniversalE2Scalar.supportPolynomial
    rw [hm, hmissing] at hupper
    have harg : (1 - -LowerE2Scalar.multiplier q) * v - T - (1 - s) / 12 =
        (1 + LowerE2Scalar.multiplier q) * v - T - (1 - s) / 12 := by ring
    rw [harg] at hupper
    nlinarith only [hupper]
  exact (not_lt_of_ge hnonpositive) hpositive

/-- At an actual global E2 excess contact, two original saturated atoms
cannot both be neutral. The original multiplier, all support estimates
and the correlated scalar guards are derived in the same model. -/
theorem IsSaturatedAtomPair.not_both_neutral_e2
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hNr : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hNu : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, x ∈ S.N) : False := by
  obtain ⟨hm, hell, _⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  rcases le_total (μ.real {x | S.ρ x = u.val}) (μ.real {x | S.ρ x = r.val}) with horder | horder
  · exact no_ordered_two_universal_e2 hpair hW hq hdq hgap hm hell.2 hNr hNu horder
  · exact no_ordered_two_universal_e2 (IsSaturatedAtomPair.symm hpair)
      hW hq hdq hgap hm hell.2 hNu hNr horder

/-- Two actual universal original saturated atoms are impossible at the
same global E2 excess contact. Their neutral positions are derived from
their original adjacency rows and actual strict support. -/
theorem IsSaturatedAtomPair.not_both_universal_e2
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val then 0 else 1)
    (hu : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = u.val then 0 else 1) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  exact hpair.not_both_neutral_e2 hW hq hdq hgap hglobal
    (S.universal_atom_neutral r hW hd hgap hr) (S.universal_atom_neutral u hW hd hgap hu)

end Erdos1017.CappedModel.SelectedHighLowStructure
