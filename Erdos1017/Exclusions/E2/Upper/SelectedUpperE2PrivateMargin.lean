module

public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyTrace
public import Erdos1017.Exclusions.E2.Upper.UpperE2PrivateScalar

/-!
# Triangle margin of the upper `E₂` private model

The original upper-`E₂` private model derives its triangle margin and covariance
density gate from contact, inventory and strong trace
(`upper_e2_private_triangle_margin`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The same original upper-E2 private model derives its triangle margin
and covariance density gate from actual contact, inventory and strong trace. -/
theorem upper_e2_private_triangle_margin
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
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = i.val}) :
    2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
        3 * (2 * (c - m * d) + m) ∧
      1 - 2 * d < μ.real {x | S.ρ x = i.val} := by
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
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let b := μ.real P
  let k := μ.real K
  let γ := 2 * (c - m * d) + m
  let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) (I ∪ P)
  have hγ : LowerE2Scalar.gapFloor q < γ := by
    have hid := LowerE2Scalar.gapFloor_eq_twoHeadValue (show 0 ≤ q by linarith [hq.1])
    have hc := hgap
    rw [hvalue] at hc
    dsimp only [γ]
    rw [hm, hdq]
    nlinarith [hid, hc]
  have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by linarith [hdq]
  have hinventory : 1 - 2 * d = (A + b) ^ 2 +
      (∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ) + 2 * b * k :=
    S.private_body_missing_inventory i p hip hW hd hgap hprivate
  have hbody : (A + b) ^ 2 ≤ LowerE2Scalar.missingMass q := by
    have he : 0 ≤ ∫ z : Ω × Ω, (J z.1 z.2) ^ 2 ∂μ.prod μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hbk : 0 ≤ b * k := mul_nonneg measureReal_nonneg measureReal_nonneg
    nlinarith only [hinventory, he, hbk, hmissing]
  have htrace (hb : b ≤ γ) :
      2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤
        2 * LowerE2Scalar.missingMass q := by
    have ht := S.private_body_strong_trace i p hip hW hd hgap hprivate hb
    change 2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤ 2 * (1 - 2 * d) at ht
    rw [hmissing] at ht
    exact ht
  have hmargin := UpperE2PrivateScalar.triangle_margin hq hA
    (show 0 ≤ b from measureReal_nonneg) (show 0 ≤ k from measureReal_nonneg)
    hγ hbody htrace
  constructor
  · dsimp only [A, I, γ] at hmargin
    have hδ : 1 + m = 1 - LowerE2Scalar.multiplier q := by linarith only [hm]
    rw [hδ]
    exact hmargin
  · rw [hmissing]
    linarith [hh.2, hA]

end Erdos1017.CappedModel.SelectedHighLowStructure
