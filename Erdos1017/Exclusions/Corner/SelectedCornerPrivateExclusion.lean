module

public import Erdos1017.Exclusions.Corner.CornerPrivateScalar
public import Erdos1017.Exclusions.Corner.FullSharpCornerPeak
public import Erdos1017.Exclusions.Corner.SelectedPrivateSaturatedQuota
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyTrace
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovarianceGeometry
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateSaturatedBill

/-!
# Exclusion of a private common peak at the corner

The common corner peak cannot have a single distinct whole outside hole; its own
one-sided slope, same-law physical exposure and private covariance are derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem corner_private_peak_gt_third_high
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    1 / 3 < μ.real {x | S.ρ x = i.val} ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) := by
  obtain ⟨hΔ, j, hA, hj, _, _⟩ :=
    S.exists_sharp_corner_peak hW hd hgap he heq hglobal
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  change 1 / 3 < μ.real {x | S.ρ x = i.val} at hA
  obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  refine ⟨hA, ?_⟩
  rcases hside with hH | hN
  · exact hH
  · let I := {x | S.ρ x = i.val}
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

private theorem reduced_corner_private_bill {A k E δ η Δ u v V0 K0 : ℝ}
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

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual original common corner peak cannot have a single distinct
whole outside hole. Its own one-sided slope, same-law physical exposure,
private covariance and both partner-star alternatives are derived internally. -/
theorem no_corner_private_common_peak
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) : False := by
  obtain ⟨hA, hhigh⟩ := S.corner_private_peak_gt_third_high i p hip hW hd hgap
    he heq hglobal hpeak hprivate
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨hell, _, _, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hellI : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hell.1, hell.2]
  have hbox := (Benchmark.crossing_contact_location he heq).1
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let K := (I ∪ Pset)ᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let b := μ.real Pset
  let k := μ.real K
  let h := 1 - 2 * d
  let δ := 1 + m
  let γ := 2 * c - (1 - δ) * h
  let ν := γ + 1 - δ
  let E := ∫ z in K, (i.val : Ω → ℝ) z ∂μ
  have hγeq : γ = 2 * (c - m * d) + m := by
    dsimp [γ, δ, h]
    ring
  have hνeq : ν = 2 * (c - m * d) := by
    dsimp [ν, γ, δ, h]
    ring
  have hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000) := by
    dsimp [h]
    constructor <;> linarith [hbox.1, hbox.2]
  have hδ : δ ∈ Icc (2 / 11 : ℝ) (226 / 589) := by
    dsimp [δ]
    constructor <;> linarith [hell.1, hell.2]
  have hcurve : benchmark d = Benchmark.mixedCurve (h / 2) := by
    have heps : h / 2 = 1 / 2 - d := by
      dsimp [h]
      ring
    rw [heps]
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true, heq, max_self]
  have hcostlower : Benchmark.mixedTangent (117 / 100) (h / 2) < c := by
    apply lt_of_le_of_lt (Benchmark.mixedTangent_le_mixedCurve (by norm_num) ?_) _
    · have heps : h / 2 = 1 / 2 - d := by
        dsimp [h]
        ring
      rw [heps]
      exact ⟨by linarith [he.1, Benchmark.epsilonStar_lt_tenth,
        Benchmark.tenth_lt_epsilonC], he.2⟩
    · rwa [← hcurve]
  have hb : 0 ≤ b := measureReal_nonneg
  have hbpos : 0 < b := ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne'
    (measure_ne_top μ Pset)
  have hk : 0 < μ K := S.private_hole_measure_pos i p hip hW hd hgap hprivate
  have hkreal : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) (I ∪ Pset)
  have hinventory : h = (A + b) ^ 2 +
      (∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ) + 2 * b * k :=
    S.private_body_missing_inventory i p hip hW hd hgap hprivate
  have hbody : (A + b) ^ 2 ≤ h := by
    have he : 0 ≤ ∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hbk := mul_nonneg hb hkreal.le
    nlinarith only [hinventory, he, hbk]
  have htrace (hbg : b ≤ γ) :
      2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤ 2 * h := by
    have ht := S.private_body_strong_trace i p hip hW hd hgap hprivate
      (by
        change b ≤ _
        rwa [← hγeq])
    change 2 * (A + b) ^ 2 + (A + (2 * (c - m * d) + m) - b) ^ 2 +
      4 * b * k ≤ 2 * h at ht
    rwa [← hγeq] at ht
  have hmargin : 2 * (1 + m) * A < 3 * (2 * (c - m * d) + m) := by
    rw [← hγeq]
    exact CornerPrivateScalar.triangle_margin hh hδ hA hb hkreal.le hcostlower hbody htrace
  obtain ⟨P⟩ := S.exists_private_physical_primal i p hip hW hd hgap hprivate
  have hE : k < E := P.private_hole_exposure_gt_mass hW hd hgap hpeak hhigh
    hprivate hA hellI hmargin
  have hnA : 1 - 2 * d < A := by
    dsimp [h] at hh
    linarith only [hh.2, hA]
  have hcov : (A + b + k - h) ^ 2 < 2 * ν * k * (A + k) := by
    have hc := S.private_covariance_of_private_hole i p hip hW hd hgap hhigh
      hprivate hnA hk hE
    change (A + b + k - h) ^ 2 < 2 * (2 * (c - m * d)) * k * (A + k) at hc
    rwa [← hνeq] at hc
  by_cases hsat : ∃ q : S.I, S.IsSaturatedAtomPair p q
  · obtain ⟨q, hpq⟩ := hsat
    let η := 1 - m - S.headPairing i q
    let Δ := 1 - m - 2 * ν
    let v := 4 * d - wholeRowDegree p.val - wholeRowDegree q.val
    let U := (Pset ∪ S.rootNeighborhood p)ᶜ \ S.rootNeighborhood q
    have hΔν : Δ = 1 - m - 2 * (2 * (c - m * d)) := by
      dsimp [Δ]
      rw [hνeq]
    have hgeom : 0 < η ∧ 0 < Δ ∧ 0 < v ∧
        2 * A + b ≤ wholeRowDegree q.val ∧
        wholeRowDegree p.val = 1 - A - b - k ∧
        ν ≤ (1 - m) * wholeRowDegree p.val := by
      rw [hΔν, hνeq]
      exact S.private_saturated_bill_geometry i p q hip hW hd hgap hellI.2 hpq hhigh hprivate
    obtain ⟨hη, hΔ, hv, hgQ, hgP, hrow⟩ := hgeom
    have hgp : 1 / 3 < wholeRowDegree p.val := by
      have hνpos : -m < ν := by
        rw [hνeq]
        linarith only [hs.gamma_pos]
      have hm : 0 ≤ 1 - m := by linarith only [hellI.1]
      by_contra hnot
      have hbound := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hm
      have hthird : (1 - m) * (1 / 3 : ℝ) < -m := by linarith only [hellI.1]
      linarith only [hrow, hνpos, hbound, hthird]
    have hAk : k < A := by linarith only [hgp, hgP, hA, hb]
    have hvbound : v ≤ 1 - 2 * h - A + k ∧ 0 < 1 - 2 * h - A + k := by
      have hupper : v ≤ 1 - 2 * h - A + k := by
        dsimp [v, h]
        linarith only [hgP, hgQ]
      exact ⟨hupper, hv.trans_le hupper⟩
    have hbill : E + δ * k + (A - k) * η +
        min δ η * μ.real U + 2 * (2 * c - h) ≤ δ * v :=
      S.private_saturated_whole_hole_bill i p q hip hW hd hgap hellI.2 hpq hhigh hprivate
    have htangent : Δ * k ≤ η * v := by
      rw [hΔν]
      exact S.private_saturated_tangent_le i p q hip hW hd hgap hellI.2 hpq hprivate hk
    have hred : k + 2 * (2 * c - h) +
        ((A - k) * k / (1 - 2 * h - A + k)) * Δ < δ * (1 - 2 * h - A) :=
      reduced_corner_private_bill hAk.le (by dsimp [δ]; linarith [hellI.2]) hη.le
        measureReal_nonneg hvbound.2 hvbound.1 hE hbill htangent
    have hΔeq : δ - 2 * γ = Δ := by
      dsimp [δ, γ, Δ, ν, h]
      ring
    have hcost : 2 * c ≤ A - A ^ 2 + 2 * b - 4 * A * b - 2 * b ^ 2 - b * k :=
      P.saturated_objective_le_private_quota hW hd hgap hpeak hhigh hprivate hA
        hellI hmargin hpq
    exact CornerPrivateScalar.saturated_false hh hδ hA hbpos hkreal hAk hcostlower hbody
      htrace (by rwa [hΔeq]) hvbound.2 hcost (by rwa [hΔeq]) hcov
  · have hunsat : ∀ q : S.I, p ≠ q → ¬S.IsSaturatedAtomPair p q := by
      intro q _ hpq
      exact hsat ⟨q, hpq⟩
    have hdemand : 2 * c ≤ (A + b) * (1 - A - b) - b * k :=
      P.objective_le_half_private_quota hW hd hgap hpeak hhigh hprivate hA hellI hmargin hunsat
    by_cases hbg : b ≤ γ
    · exact CornerPrivateScalar.unsaturated_small_b_false hh hδ hA hb hkreal.le hcostlower
        hbody hbg (htrace hbg) hdemand
    · exact CornerPrivateScalar.unsaturated_large_b_false hh hδ hA (lt_of_not_ge hbg)
        hkreal hcostlower hbody hdemand hcov

end Erdos1017.CappedModel.SelectedHighLowStructure
