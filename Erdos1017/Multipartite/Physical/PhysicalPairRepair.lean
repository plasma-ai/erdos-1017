module

public import Erdos1017.Multipartite.Physical.PhysicalRepairTuples

/-!
# Adding an order-two law for residual edge demand

`pairRepair` adds an order-two law carrying half of a symmetric residual edge
demand to a balanced family, with its exact occupation, feasibility and cost
(`cost_pairRepair`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalPrimal

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [MeasurableSpace V]

/-- Add a genuine order-two law for half of a symmetric residual edge demand. -/
def pairRepair (μ : Laws V) (ρ : Measure (V × V)) : Laws V :=
  fun n => μ n + singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n

theorem pairRepair_finite (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (ρ : Measure (V × V)) [IsFiniteMeasure ρ] (n : ℕ) :
    IsFiniteMeasure (pairRepair μ ρ n) := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • ρ) := Measure.smul_finite _ (by norm_num)
  have : IsFiniteMeasure (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) := Measure.isFiniteMeasure_map _ _
  have := singleOrder_finite 2 n (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ))
  unfold pairRepair
  infer_instance

/-- Both orientations are retained, so the added occupation is precisely the
whole residual demand, while its parent cost is half the residual edge mass. -/
theorem occupation_pairRepair (μ : Laws V) (ρ : Measure (V × V))
    (hswap : ρ.map Prod.swap = ρ) :
    occupation (pairRepair μ ρ) = occupation μ + ρ := by
  unfold pairRepair
  rw [occupation_add, occupation_singleOrder, edgeLaw_occupation,
    Measure.map_smul _ measurable_swap.aemeasurable, hswap, ← add_smul]
  have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [hhalf, one_smul]

theorem pairRepair_feasible (μ : Laws V) (A : V → V → Prop) (demand ρ : Measure (V × V))
    (hμ : Feasible A demand μ) (hA : MeasurableSet {z : V × V | A z.1 z.2})
    (hsym : ∀ x y, A x y → A y x) (hρ : ∀ᵐ z ∂ρ, A z.1 z.2)
    (hswap : ρ.map Prod.swap = ρ) :
    Feasible A (demand + ρ) (pairRepair μ ρ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pairRepair, hμ.1]
  · simp [pairRepair, hμ.2.1]
  · intro n
    apply ae_add_measure_iff.mpr
    refine ⟨hμ.2.2.1 n, ?_⟩
    by_cases hn : n = 2
    · subst n
      rw [singleOrder_self]
      exact edgeLaw_clique _ A hA hsym (Measure.ae_smul_measure hρ _)
    · rw [singleOrder_ne 2 n _ (Ne.symm hn)]
      simp
  · rw [occupation_pairRepair μ ρ hswap, hμ.2.2.2]

/-- Exact cost of adding the residual edge law to an arbitrary balanced family. -/
theorem cost_pairRepair (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (demand ρ : Measure (V × V)) [IsFiniteMeasure demand] [IsFiniteMeasure ρ]
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = demand) :
    cost (pairRepair μ ρ) = cost μ + ρ.real Set.univ / 2 := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • ρ) := Measure.smul_finite _ (by norm_num)
  have : IsFiniteMeasure (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) := Measure.isFiniteMeasure_map _ _
  have (n : ℕ) : IsFiniteMeasure (singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n) :=
    singleOrder_finite _ _ _
  have hs : Summable (fun n => (singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n).real Set.univ) := by
    apply summable_of_ne_finset_zero (s := {2})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [singleOrder_ne 2 n _ (Ne.symm hn)]
  change (∑' n, (μ n + singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n).real Set.univ) = _
  have hr (n : ℕ) : (μ n + singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n).real Set.univ =
      (μ n).real Set.univ + (singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ)) n).real Set.univ :=
    measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)
  simp_rw [hr]
  rw [(summable_mass_of_balance μ demand hzero hone hbalance).tsum_add hs]
  change cost μ + cost (singleOrder 2 (edgeLaw ((2 : ℝ≥0∞)⁻¹ • ρ))) = _
  rw [cost_singleOrder, edgeLaw_mass]
  simp [measureReal_def, ENNReal.toReal_mul, div_eq_mul_inv, mul_comm]

end Erdos1017.PhysicalPrimal
