module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PeakThird
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateMargin
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovarianceGeometry
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateRootless
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateSaturatedBill

/-!
# No private hole for the upper `E₂` peak

At an upper-`E₂` contact an original common peak cannot have one distinct whole
private hole (`no_upper_e2_private_common_peak`), so the internally chosen
selected upper-`E₂` peak has no single distinct whole private hole, with contact
value and derivative kept explicit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.UpperE2PrivateScalar

private theorem reduced_saturated_bill {A k E δ η Δ u v V0 K0 : ℝ}
    (hAk : k ≤ A) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hu : 0 ≤ u)
    (hw : 0 < V0 + k) (hvw : v ≤ V0 + k)
    (hE : k < E)
    (hbill : E + δ * k + (A - k) * η + min δ η * u + 2 * K0 ≤ δ * v)
    (htangent : Δ * k ≤ η * v) :
    k + 2 * K0 + ((A - k) * k / (V0 + k)) * Δ < δ * V0 := by
  have hmin : 0 ≤ min δ η * u := mul_nonneg (le_min hδ hη) hu
  have hηv := mul_le_mul_of_nonneg_left hvw hη
  have hηw : Δ * k / (V0 + k) ≤ η :=
    (div_le_iff₀ hw).mpr (htangent.trans hηv)
  have hmul := mul_le_mul_of_nonneg_left hηw (sub_nonneg.mpr hAk)
  have hδv := mul_le_mul_of_nonneg_left hvw hδ
  have heq : (A - k) * (Δ * k / (V0 + k)) =
      ((A - k) * k / (V0 + k)) * Δ := by ring
  rw [heq] at hmul
  nlinarith only [hE, hbill, hmin, hmul, hδv]

private theorem private_hole_lt_first_mass
    (A b k m ν gP : ℝ)
    (hA : 1 / 3 < A) (hb : 0 ≤ b)
    (hell : 1 / 2 < -m) (hν : 0 < ν + m)
    (hbound : ν ≤ (1 - m) * gP)
    (hgP : gP = 1 - A - b - k) :
    1 / 3 < gP ∧ k < A := by
  have hm : m < -(1 / 2 : ℝ) := by linarith
  have hν' : -m < ν := by linarith
  have hden : 0 < 1 - m := by linarith
  have hgPpos : 0 < gP := by nlinarith
  have hthird : 1 / 3 < gP := by
    nlinarith [mul_nonneg (show 0 ≤ -m - (1 / 2 : ℝ) by linarith)
      (show 0 ≤ gP by linarith)]
  constructor
  · exact hthird
  · linarith

end Erdos1017.UpperE2PrivateScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem private_common_peak_gt_third_high
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    1 / 3 < μ.real {x | S.ρ x = i.val} ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) := by
  obtain ⟨hΔ, j, hA, hside, hj, _, _, _⟩ :=
    S.exists_original_upper_e2_peak_gt_third hW hq hdq hvalue hderiv hgap hglobal
  have heq : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  have hmass : S.originalAtomMass i = μ.real {x | S.ρ x = i.val} := by
    rfl
  rw [hmass] at hA
  refine ⟨hA, ?_⟩
  rcases hside with hH | hN
  · exact hH
  · have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
      have hmass := UpperE2Parameter.missingMass_mem hq
      rw [hdq]
      constructor <;> linarith [hmass.1, hmass.2]
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hP : MeasurableSet P := (S.hfibers p.val p.property).1
    have hprob : 0 < (μ.restrict I).prod (μ.restrict P) Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      have hi : 0 < μ I := (S.hfibers i.val i.property).2.1
      have hp : 0 < μ P := (S.hfibers p.val p.property).2.1
      simpa only [Measure.restrict_apply_univ, show (⊥ : ENNReal) = 0 from rfl] using
        (mul_ne_zero hi.ne' hp.ne').bot_lt
    have hneutral := S.neutral_atom_adjacency i hW hd hgap hN
    have hboth : ∀ᵐ z ∂(μ.restrict I).prod (μ.restrict P), False := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          hprivate,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          hneutral,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with z hp hn hi hj
      have hzero := hp hi
      have hone := hn hi
      have hpi : S.ρ z.2 = p.val := hj
      have hneq : S.ρ z.2 ≠ i.val := by
        intro he
        exact hip (Subtype.ext (he.symm.trans hpi))
      simp only [hpi, or_true, ite_true] at hzero
      simp only [hneq, ite_false] at hone
      exact zero_ne_one (hzero.symm.trans hone)
    have hzero : (μ.restrict I).prod (μ.restrict P) Set.univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using hboth
    exact False.elim ((ne_of_gt hprob) hzero)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

private theorem upper_e2_private_large_high_false
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = i.val}) : False := by
  have hh := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hh.1, hh.2]
  have hs := hW.strict_gap_structure hd hgap
  have hderivW : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) (density W) := by
    rw [hW.density_eq]
    exact hderiv
  have hm : m = -LowerE2Scalar.multiplier q :=
    full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal hderivW
      m _ hW.stationary hs.nonconstant_degree
  have hellq := UpperE2Parameter.multiplier_mem hq
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hm, hellq.1, hellq.2]
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let K := (I ∪ Pset)ᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let b := μ.real Pset
  let k := μ.real K
  let h := LowerE2Scalar.missingMass q
  let ell := LowerE2Scalar.multiplier q
  let ν := 2 * (c - m * d)
  let γ := ν + m
  let E := ∫ x in K, (i.val : Ω → ℝ) x ∂μ
  have hmissing : 1 - 2 * d = h := by dsimp [h]; linarith [hdq]
  have hγeq : γ = 2 * c - ell * h := by
    dsimp [γ, ν, ell, h]
    rw [hm, hdq]
    ring
  have hc : Benchmark.twoHeadValue ((q + 2) / 3) < c := by
    rw [← hvalue]
    exact hgap
  have hνeq : γ + ell = ν := by dsimp [γ, ell]; linarith only [hm]
  have hb : 0 ≤ b := measureReal_nonneg
  have hbpos : 0 < b := ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne'
    (measure_ne_top μ Pset)
  have hk : 0 < μ K := S.private_hole_measure_pos i p hip hW hd hgap hprivate
  have hkreal : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  have hmargin := S.upper_e2_private_triangle_margin i p hip hW hq hdq hvalue hderiv
    hgap hglobal hprivate hA
  obtain ⟨P⟩ := S.exists_private_physical_primal i p hip hW hd hgap hprivate
  have hE : k < E := P.private_hole_exposure_gt_mass hW hd hgap hpeak hhigh
    hprivate hA hell hmargin.1
  have hcov0 := S.private_covariance_of_private_hole i p hip hW hd hgap hhigh
    hprivate hmargin.2 hk hE
  have hcov : (A + b + k - h) ^ 2 < 2 * (γ + ell) * k * (A + k) := by
    change (A + b + k - (1 - 2 * d)) ^ 2 < 2 * ν * k * (A + k) at hcov0
    rw [hmissing] at hcov0
    simpa only [hνeq] using hcov0
  have hinventory := S.private_body_missing_inventory i p hip hW hd hgap hprivate
  let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) (I ∪ Pset)
  have hinv : 1 - 2 * d = (A + b) ^ 2 +
      (∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ) + 2 * b * k := hinventory
  have hbody : (A + b) ^ 2 ≤ h := by
    have he : 0 ≤ ∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hbk := mul_nonneg hb hkreal.le
    nlinarith only [hinv, he, hbk, hmissing]
  by_cases hsat : ∃ u : S.I, S.IsSaturatedAtomPair p u
  · obtain ⟨u, hpu⟩ := hsat
    let η := 1 - m - S.headPairing i u
    let Δ := 1 - m - 2 * ν
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree u.val
    let U := (Pset ∪ S.rootNeighborhood p)ᶜ \ S.rootNeighborhood u
    have hgeom : 0 < η ∧ 0 < Δ ∧ 0 < v ∧
        2 * A + b ≤ wholeRowDegree u.val ∧
        wholeRowDegree p.val = 1 - A - b - k ∧
        ν ≤ (1 - m) * wholeRowDegree p.val :=
      S.private_saturated_bill_geometry i p u hip hW hd hgap hell.2 hpu hhigh hprivate
    obtain ⟨hη, hΔ, hv, hgU, hgP, hrow⟩ := hgeom
    have hAk : k < A := (UpperE2PrivateScalar.private_hole_lt_first_mass
      A b k m ν (wholeRowDegree p.val) hA hb hell.1 hs.gamma_pos hrow hgP).2
    have hvbound : v ≤ 1 - 2 * h - A + k ∧ 0 < 1 - 2 * h - A + k := by
      have hupper : v ≤ 1 - 2 * h - A + k := by
        dsimp [v]
        linarith only [hmissing, hgP, hgU]
      exact ⟨hupper, hv.trans_le hupper⟩
    have hbill : E + (1 + m) * k + (A - k) * η +
        min (1 + m) η * μ.real U + 2 * (2 * c - h) ≤ (1 + m) * v := by
      have hb0 := S.private_saturated_whole_hole_bill i p u hip hW hd hgap
        hell.2 hpu hhigh hprivate
      change E + (1 + m) * k + (A - k) * η + min (1 + m) η * μ.real U +
        2 * (2 * c - (1 - 2 * d)) ≤ (1 + m) * v at hb0
      rw [hmissing] at hb0
      exact hb0
    have htangent : Δ * k ≤ η * v :=
      S.private_saturated_tangent_le i p u hip hW hd hgap hell.2 hpu hprivate hk
    have hδ : 0 < 1 + m := by linarith [hell.2]
    have hred : k + 2 * (2 * c - h) +
        ((A - k) * k / (1 - 2 * h - A + k)) * Δ <
      (1 + m) * (1 - 2 * h - A) :=
      UpperE2PrivateScalar.reduced_saturated_bill hAk.le hδ.le hη.le measureReal_nonneg
        hvbound.2 hvbound.1 hE hbill htangent
    have hΔeq : 1 - ell - 2 * γ = Δ := by
      dsimp [ell, γ, Δ]
      linarith only [hm]
    have hδeq : 1 - ell = 1 + m := by dsimp [ell]; linarith only [hm]
    have hred' : k + 2 * (2 * c - h) +
        ((A - k) * k / (1 - 2 * h - A + k)) * (1 - ell - 2 * γ) <
      (1 - ell) * (1 - 2 * h - A) := by
      rw [hΔeq, hδeq]
      exact hred
    have hΔ' : 0 < 1 - ell - 2 * γ := by rw [hΔeq]; exact hΔ
    exact UpperE2PrivateScalar.saturated_false hq hA hbpos hkreal hAk hγeq hc
      hΔ' hvbound.2 hred' hcov
  · have hunsat : ∀ u : S.I, p ≠ u → ¬S.IsSaturatedAtomPair p u := by
      intro u _ hpu
      exact hsat ⟨u, hpu⟩
    have hdemand := P.objective_le_half_private_quota hW hd hgap hpeak hhigh hprivate
      hA hell hmargin.1 hunsat
    change 2 * c ≤ (A + b) * (1 - A - b) - b * k at hdemand
    by_cases hbg : b ≤ γ
    · have htrace : 2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤ 2 * h := by
        have ht := S.private_body_strong_trace i p hip hW hd hgap hprivate hbg
        change 2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤ 2 * (1 - 2 * d) at ht
        rw [hmissing] at ht
        exact ht
      exact UpperE2PrivateScalar.unsaturated_small_b_false hq hA hb hkreal.le hγeq hc
        hbody hbg htrace hdemand
    · exact UpperE2PrivateScalar.unsaturated_large_b_false hq hA (lt_of_not_ge hbg)
        hkreal hγeq hc hbody hdemand hcov

/-- At a genuine upper-E2 contact, an original common peak cannot have
one distinct whole private hole. Its mass and HIGH location are derived. -/
theorem no_upper_e2_private_common_peak
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) : False := by
  have hlarge := S.private_common_peak_gt_third_high i p hip hW hq hdq hvalue hderiv
    hgap hglobal hpeak hprivate
  exact S.upper_e2_private_large_high_false i p hip hW hq hdq hvalue hderiv hgap hglobal
    hpeak hlarge.2 hprivate hlarge.1

/-- The actual selected upper-E2 peak is chosen internally and has no
single distinct whole private hole. Contact value and derivative stay explicit. -/
theorem exists_original_upper_e2_peak_no_private_hole
    (S : SelectedHighLowStructure W m)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      1 / 3 < S.originalAtomMass i ∧ S.IsCommonForwardPeak d c i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N)) ∧
      (∀ j : S.I, j ≠ i → S.originalAtomMass j < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' j, (S.originalAtomMass j) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      ((∑' j : {j : S.I // j ≠ i}, (S.originalAtomMass j.val) ^ 2) <
        (S.originalAtomMass i) ^ 2) ∧
      ∀ p : S.I, i ≠ p → ¬(∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
        adjacencyKernel W z.1 z.2 =
          if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) := by
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority⟩ :=
    S.exists_original_upper_e2_peak_gt_third hW hq hdq hvalue hderiv hgap hglobal
  refine ⟨hΔ, i, hA, hpeak, hside, hlargest, hreserve, hmajority, ?_⟩
  intro p hip hprivate
  exact S.no_upper_e2_private_common_peak i p hip hW hq hdq hvalue hderiv hgap hglobal
    hpeak hprivate

end Erdos1017.CappedModel.SelectedHighLowStructure
