module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairCapacity
public import Erdos1017.Exclusions.Common.Flows.FullForwardQuarterFloor

/-!
# Saturated atoms at the lower `E₂` contact

At the selected lower `E₂` global contact, the same-model physical primal has
strictly more saturated mass than the stationary-family floor, and the contact
constructs its saturated original atoms with strictly positive product capacity,
with no atom pair or primal supplied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- At the actual selected lower-E2 global contact, the same-model physical
primal has strictly more saturated mass than the stationary-family floor. -/
theorem FullStationaryClass.lowerE2_saturated_mass_floor (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    m = -LowerE2Scalar.multiplier q ∧ -m ∈ Ioo (0 : ℝ) 1 ∧
      LowerE2Scalar.pairFloor q <
        (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} / 2 := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨hq.1, by linarith [hq.2]⟩
  obtain ⟨hm, hell, _⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq'
  have hB : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3) := by
    rw [hdq]
    exact Benchmark.benchmark_e2_q hq'
  have hfloor := LowerE2Scalar.pairFloor_eq_twoHeadValue hq.1.le
  rw [← hdq] at hfloor
  rw [hB] at hgap
  have hstrict : LowerE2Scalar.pairFloor q < (3 * c - d) / 2 := by linarith
  have hmass := hW.saturated_charge_mass_lower_bound hd.2 (by rwa [hB])
  exact ⟨hm, hell, hstrict.trans_le hmass⟩

/-- The actual lower-E2 contact constructs its saturated original atoms
and strictly positive product capacity. No atom pair or primal is supplied. -/
theorem SelectedHighLowStructure.exists_lowerE2_saturated_atoms
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ r u : S.I, S.IsSaturatedAtomPair r u ∧
      LowerE2Scalar.pairFloor q <
        μ.real {x | S.ρ x = r.val} * μ.real {x | S.ρ x = u.val} := by
  obtain ⟨_, hell, hfloor⟩ := hW.lowerE2_saturated_mass_floor hq hdq hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem ⟨hq.1, by linarith [hq.2]⟩
  have hpositive := LowerE2Scalar.pairFloor_pos ⟨hq.1.le, hq.2⟩
  have hmass : 0 < (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} := by linarith
  obtain ⟨r, u, hru⟩ := S.exists_saturated_atom_pair_of_positive_mass hW hd hgap hell.2 hmass
  have heq := hru.saturated_mass_eq hW hd hgap hell.2
  exact ⟨r, u, hru, by rw [heq] at hfloor; linarith⟩

end Erdos1017.CappedModel
