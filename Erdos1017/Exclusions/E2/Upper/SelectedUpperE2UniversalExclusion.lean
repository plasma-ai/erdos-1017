module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPriceJoin
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2OneCenterGeometry
public import Erdos1017.Exclusions.E2.Upper.SelectedE2ZeroBody

/-!
# No positive source for the upper `E₂` singleton recovery

The upper-`E₂` singleton recovery cannot have positive entire source; the
original peak, saturated pair, universal row, physical primal and positive-body
alternatives are all derived on the selected model
(`no_upper_e2_one_center_positive_source`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c q : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual upper-E2 singleton recovery cannot have positive entire
source. The original peak, saturated pair, universal row, physical primal
and positive-body alternative are all selected from the model inputs. -/
theorem no_upper_e2_one_center_positive_source (R : S.ReverseRecovery)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 1)
    (hsource : 0 < μ (S.reverseCompulsorySource R.plateau)) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    have hm := UpperE2Parameter.missingMass_mem hq
    constructor <;> linarith only [hm.1, hm.2]
  obtain ⟨r, p, hr, _, hpeak, _, hpair, huniv, _⟩ :=
    R.exists_upper_e2_one_center_universal_sat_peak hW hq hdq hvalue hderiv
      hgap hglobal hcard hsource
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith only [hq.1], by linarith only [hq.2]⟩
  have hnonnegative := bodyPositiveEnergy_nonnegative W {x | S.ρ x = r.val}
  have hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} ≠ 0 := fun hz =>
    S.no_e2_zero_body r hW hq' hdq hvalue hderiv hgap hglobal hz
  have hpositive := lt_of_le_of_ne hnonnegative (Ne.symm hzero)
  rw [hr] at hsource
  exact P.no_upper_e2_universal_positive_source S R r p hpair hW hq hdq hvalue
    hderiv hgap hglobal hr hsource huniv hpeak hpositive

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
