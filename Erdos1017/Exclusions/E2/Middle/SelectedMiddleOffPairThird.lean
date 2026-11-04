module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateSector
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Joined
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairDominance

/-!
# Off-pair peaks lie below one third

An original common peak off the saturated pair lies below one third, with its
one-center recovery and both location alternatives derived
(`middle_e2_off_pair_peak_lt_third`).
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

/-- An original common peak off the actual saturated pair lies below one
third. Its one-center recovery and both location alternatives are derived. -/
theorem middle_e2_off_pair_peak_lt_third (S : SelectedHighLowStructure W m)
    (i r u : S.I) (hir : i ≠ r) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair r u)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i) : S.originalAtomMass i < 1 / 3 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hell := (hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal).2.1.2
  obtain ⟨_, _, _, _, R, p, k, hp, _, hkp, hk, _, _, _, hloc⟩ :=
    S.exists_middle_e2_one_center_entry hW hq hdq hvalue hderiv hgap hglobal
  obtain ⟨hDelta, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  have hki : k = i := (hk S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst k
  rcases hloc with ⟨_, hprivate⟩ | hjoined
  · have hsector := S.private_peak_large_sector i p hkp hW hq hdq hvalue hderiv
      hgap hglobal hpeak hprivate
    have hp0 : 0 < μ.real {x | S.ρ x = p.val} :=
      ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne' (measure_ne_top μ _)
    change μ.real {x | S.ρ x = i.val} < 1 / 3
    linarith
  · rcases R.middle_e2_joined_peak_alternatives hW hq hdq hvalue hderiv hgap hglobal
        p i hp hkp hpeak hjoined with ⟨hip, _, _⟩ | ⟨_, _, _, hthird⟩
    · rcases hip.unique hpair hW hd hgap hell with h | h
      · exact False.elim (hir h.1)
      · exact False.elim (hiu h.1)
    · exact hthird

end Erdos1017.CappedModel.SelectedHighLowStructure
