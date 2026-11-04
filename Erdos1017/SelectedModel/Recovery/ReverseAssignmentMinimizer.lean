module

public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCompactness
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Minimizer of the reverse assignment objective

A feasible countable assignment attains the minimum of the extended square-sum
objective `dualObjective`, which is lower semicontinuous in the product weak
topology and agrees with the real square sum on admissible assignments
(`exists_minimizer`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology ENNReal

namespace Erdos1017.ReverseAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The nonnegative extended square sum is defined even before feasibility
and real summability have been established. -/
def dualObjective (a : ℕ → ℝ) (d : DualFamily μ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal ((a i + d i (Lp.const 2 μ (1 : ℝ))) ^ 2)

/-- The actual extended objective is lower semicontinuous in the product weak topology. -/
theorem lowerSemicontinuous_dualObjective (a : ℕ → ℝ) :
    LowerSemicontinuous (dualObjective (μ := μ) a) := by
  apply lowerSemicontinuous_tsum
  intro i
  have hc : Continuous (fun d : DualFamily μ => a i + d i (Lp.const 2 μ (1 : ℝ))) :=
    continuous_const.add ((WeakDual.eval_continuous _).comp (continuous_apply i))
  exact (ENNReal.continuous_ofReal.comp (hc.pow 2)).lowerSemicontinuous

/-- Feasibility pays real square summability, so the extended objective
is exactly the original real square sum on every admissible assignment. -/
theorem ofReal_objective_decode {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a) (d : DualFamily μ)
    (hd : Feasible allowed δ (decode d)) :
    ENNReal.ofReal (objective a (decode d)) = dualObjective a d := by
  unfold objective dualObjective
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg (mass a (decode d) i))
    (hd.square_mass_summable ha haSum)]
  simp only [mass_decode]

/-- An actual feasible countable assignment attains the true real squared-mass minimum.
The weak compactness, all AE limit constraints and real summability are derived. -/
theorem exists_minimizer {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    (q0 : ℕ → Lp ℝ 2 μ) (hq0 : Feasible allowed δ q0) :
    ∃ q : ℕ → Lp ℝ 2 μ, Feasible allowed δ q ∧
      ∀ v : ℕ → Lp ℝ 2 μ, Feasible allowed δ v → objective a q ≤ objective a v := by
  have hnonempty : (dualFeasibleSet (μ := μ) allowed δ).Nonempty :=
    ⟨encode q0, encode_mem_dualFeasibleSet hq0⟩
  obtain ⟨d, hd, hmin⟩ :=
    ((lowerSemicontinuous_dualObjective a).lowerSemicontinuousOn _).exists_isMinOn
      hnonempty (isCompact_dualFeasibleSet hallowed hδ)
  have hfeas : Feasible allowed δ (decode d) := hd
  refine ⟨decode d, hfeas, ?_⟩
  intro v hv
  have hv' : Feasible allowed δ (decode (encode v)) := by
    simpa only [decode_encode] using hv
  have hcomparison := (isMinOn_iff.mp hmin) (encode v) (encode_mem_dualFeasibleSet hv)
  rw [← ofReal_objective_decode ha haSum d hfeas,
    ← ofReal_objective_decode ha haSum (encode v) hv', decode_encode] at hcomparison
  exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun i => sq_nonneg (mass a v i)))).mp
    hcomparison

end Erdos1017.ReverseAssignment
