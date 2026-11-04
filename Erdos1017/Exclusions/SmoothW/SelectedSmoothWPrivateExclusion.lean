module

public import Erdos1017.Exclusions.SmoothW.FullFreshIndependentStarCap
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWPositiveBody
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyTrace
public import Erdos1017.Exclusions.Common.SelectedAtomCopy

/-!
# No private common peak at the smooth `W` contact

The same original common `W` peak cannot have one entire outside missing whole
atom; the independent union pays its fresh-star mass cap, and sharp contact
closes the case (`no_smoothW_private_common_peak`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SmoothWScalar

private theorem private_partner_lt_intercept_of_fresh_cap
    {A b ell gamma : ℝ}
    (hA : 357 / 1000 < A) (hg : 103 / 1000 < gamma)
    (hell0 : 0 ≤ ell) (hell : ell < 5 / 8)
    (hcap : (1 + ell) * (A + b) ≤ ell + gamma) :
    b < gamma := by
  have hmargin : 0 < (1 + ell) * A - ell * (1 - gamma) := by
    by_cases hsum : 1 ≤ A + gamma
    · nlinarith [mul_nonneg hell0 (sub_nonneg.mpr hsum)]
    · have hsum' : A + gamma < 1 := lt_of_not_ge hsum
      have hprod := mul_pos (sub_pos.mpr hell) (sub_pos.mpr hsum')
      nlinarith
  by_contra h
  have hb : gamma ≤ b := le_of_not_gt h
  have hpos : 0 ≤ 1 + ell := by linarith
  have hmul := mul_le_mul_of_nonneg_left hb hpos
  nlinarith only [hcap, hmul, hmargin]

end Erdos1017.SmoothWScalar

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

attribute [local instance] Classical.propDecidable

private theorem smoothW_same_peak_sharp_guards
    (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r) :
    357 / 1000 < μ.real {x | S.ρ x = r.val} ∧
      103 / 1000 < 2 * (c - m * d) + m ∧
      2 * (c - m * d) + m < μ.real {x | S.ρ x = r.val} ∧
      -m < 5 / 8 ∧ 1 - 2 * d < 1163 / 5000 := by
  obtain ⟨hΔ, i, hA, hg, hγA, hi, _, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  have heq : i = r := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  change 357 / 1000 < μ.real {x | S.ρ x = r.val} at hA
  change 2 * (c - m * d) + m < μ.real {x | S.ρ x = r.val} at hγA
  obtain ⟨hm, hs, _, _, _, hh⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  let s := Benchmark.mixedInverse (1 / 2 - d)
  have hden : 0 < 3 * s := by dsimp [s]; linarith [hs.1]
  have hell : (s + 1) / (3 * s) < 5 / 8 := by
    apply (div_lt_iff₀ hden).mpr
    dsimp [s] at hs ⊢
    linarith [hs.1]
  have hell' : -m < 5 / 8 := by simpa only [hm, neg_neg] using hell
  exact ⟨hA, hg, hγA, hell', hh⟩

private theorem ae_private_union_independent
    (S : SelectedHighLowStructure W m) (r u : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) →
      p.2 ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) →
        adjacencyKernel W p.1 p.2 = 0 := by
  let hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [hprivate, hswap.ae hprivate,
    S.ae_root_fiber_physical_independent u hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    adjacencyKernel_symm W] with p hi hir hp hphys hsym hx hy
  have hy' : S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val := hy
  have hx' : S.ρ p.1 = r.val ∨ S.ρ p.1 = u.val := hx
  rcases hx with hx | hx
  · simpa [hy'] using hi hx
  · rcases hy with hy | hy
    · have hz : adjacencyKernel W p.2 p.1 = 0 := by
        simpa [hx'] using hir hy
      exact hsym.trans hz
    · have hb := hp hx hy
      change adjacencyKernel W p.1 p.2 =
        (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) at hphys
      simpa [hb] using hphys

/-- The same original common W peak cannot have one entire outside missing
whole atom. The actual independent union pays its fresh-star mass cap;
sharp contact and the strict original private-body trace then conflict. -/
theorem no_smoothW_private_common_peak
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c r)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) : False := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = u.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers u.val u.property).1
  have hdis : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hru (Subtype.ext (hx.symm.trans hy)))
  have hmass : μ.real (I ∪ P) = μ.real I + μ.real P := measureReal_union hdis hP
  have hcap := hW.independent_set_mass_le_stationary hd hgap (I ∪ P)
    (hI.union hP) (S.ae_private_union_independent r u hW hd hgap hprivate)
  rw [hmass] at hcap
  obtain ⟨hA, hg, hγA, hell, hh⟩ :=
    S.smoothW_same_peak_sharp_guards r hW hd hgap he hactive hglobal hpeak
  obtain ⟨_, _, hellI, _, _, _⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  have hb : μ.real P < 2 * (c - m * d) + m :=
    SmoothWScalar.private_partner_lt_intercept_of_fresh_cap hA hg
      (by linarith [hellI.1]) hell
      (by dsimp only [I, P] at hcap ⊢; nlinarith only [hcap])
  have htrace := S.private_body_strict_trace r u hru hW hd hgap hprivate hb.le hγA
  exact SmoothWScalar.not_trace_of_sharp_guards hA hg hh htrace.le

end Erdos1017.CappedModel.SelectedHighLowStructure
