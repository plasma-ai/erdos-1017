module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalRootLeaves
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalOccupation

/-!
# Root and leaf counts in parent laws

One root coordinate contributes `n-1` leaves at order `n`, a parent with a root
and two coordinates supplies two leaves per unit mass, and when every parent
meets the root the all-order cost is at most half the root-leaf occupation;
root-pair balance gives the quota `A(1-A)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- One root coordinate contributes exactly n−1 leaves at order n.
The identity retains the entire original joint parent law. -/
theorem orderRootLeaves_mass (n : ℕ) (ρ : Measure (Fin n → Ω))
    (I : Set Ω) (hI : MeasurableSet I) :
    orderRootLeaves n ρ I univ = (n - 1 : ℕ) * orderFirstOccupation n ρ I := by
  rw [orderRootLeaves_eq_snd_restrict n ρ I hI, Measure.snd_apply MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  have hset : I ×ˢ (univ : Set Ω) = Prod.fst ⁻¹' I := by ext p; simp
  rw [hset, ← Measure.fst_apply hI, fst_orderOccupation]
  simp only [Measure.smul_apply, nsmul_eq_mul]

/-- If almost every parent meets the root, its original mass is at most
the first occupation of the root set. No independence is required. -/
theorem mass_le_orderFirstOccupation_of_has_root (n : ℕ) (ρ : Measure (Fin n → Ω))
    (I : Set Ω) (hI : MeasurableSet I)
    (hroot : ∀ᵐ v ∂ρ, ∃ i : Fin n, v i ∈ I) :
    ρ univ ≤ orderFirstOccupation n ρ I := by
  have hmass : ρ (⋃ i : Fin n, {v : Fin n → Ω | v i ∈ I}) = ρ univ := by
    apply measure_congr
    filter_upwards [hroot] with v hv
    exact propext ⟨fun _ => trivial, fun _ => by simpa only [mem_iUnion, mem_ofPred_eq] using hv⟩
  rw [← hmass]
  have h := measure_iUnion_le (μ := ρ) (fun i : Fin n => {v : Fin n → Ω | v i ∈ I})
  have heq : orderFirstOccupation n ρ I = ∑ i : Fin n, ρ {v : Fin n → Ω | v i ∈ I} := by
    rw [orderFirstOccupation, Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact Measure.map_apply (measurable_pi_apply i) hI
  rw [heq]
  simpa only [tsum_fintype] using h

/-- A parent with a root and at least two other coordinates supplies at
least two leaves per unit of its actual parent mass. -/
theorem twice_mass_le_orderRootLeaves (n : ℕ) (hn : 3 ≤ n)
    (ρ : Measure (Fin n → Ω)) (I : Set Ω) (hI : MeasurableSet I)
    (hroot : ∀ᵐ v ∂ρ, ∃ i : Fin n, v i ∈ I) :
    2 * ρ univ ≤ orderRootLeaves n ρ I univ := by
  rw [orderRootLeaves_mass n ρ I hI]
  have hn' : (2 : ℝ≥0∞) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 by omega)
  exact (mul_le_mul_of_nonneg_left
    (mass_le_orderFirstOccupation_of_has_root n ρ I hI hroot) (by norm_num : (0 : ℝ≥0∞) ≤ 2)).trans
    (mul_le_mul_of_nonneg_right hn' (show (0 : ℝ≥0∞) ≤ orderFirstOccupation n ρ I from zero_le))

/-- Exact original root-leaf occupation bounds the actual all-order cost
when every parent meets the root and contains at least two leaves. The
laws can be singular and no order cap or symmetry is imposed. -/
theorem cost_le_half_rootLeaves_mass (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I : Set Ω) (hI : MeasurableSet I) [IsFiniteMeasure (rootLeaves η I)]
    (hsmall : ∀ n, n < 3 → η n = 0)
    (hroot : ∀ n, ∀ᵐ v ∂η n, ∃ i : Fin n, v i ∈ I) :
    cost η ≤ (rootLeaves η I).real univ / 2 := by
  have hord (n : ℕ) : 2 * η n univ ≤ orderRootLeaves n (η n) I univ := by
    by_cases hn : 3 ≤ n
    · exact twice_mass_le_orderRootLeaves n hn (η n) I hI (hroot n)
    · rw [hsmall n (by omega)]
      simp only [Measure.coe_zero, Pi.zero_apply, mul_zero]
      exact zero_le
  have htotal : 2 * (∑' n, η n univ) ≤ rootLeaves η I univ := by
    rw [← ENNReal.tsum_mul_left, rootLeaves, Measure.sum_apply_of_countable]
    exact ENNReal.tsum_le_tsum hord
  have hreal := ENNReal.toReal_mono (measure_ne_top (rootLeaves η I) univ) htotal
  have hcost : (∑' n, η n univ).toReal = cost η := by
    simpa only [cost, measureReal_def] using
      ENNReal.tsum_toReal_eq (fun n => measure_ne_top (η n) univ)
  rw [ENNReal.toReal_mul, hcost] at hreal
  norm_num only [ENNReal.toReal_ofNat] at hreal
  change cost η ≤ (rootLeaves η I univ).toReal / 2
  linarith

/-- Actual universal root-pair balance gives the quota A(1−A), and hence
the half-quota cost bound once every parent has a root and two leaves.
The original root-leaf identity is derived from the actual graph demand. -/
theorem cost_le_universal_root_quota (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set (Ω × Ω)) (hE : MeasurableSet E)
    (hbalance : occupation η = graphDemand μ E) (I : Set Ω) (hI : MeasurableSet I)
    (hrow : ∀ᵐ p ∂(μ.restrict I).prod μ, p ∈ E ↔ p.2 ∉ I)
    (hsmall : ∀ n, n < 3 → η n = 0)
    (hroot : ∀ n, ∀ᵐ v ∂η n, ∃ i : Fin n, v i ∈ I) :
    cost η ≤ μ.real I * (1 - μ.real I) / 2 := by
  have hleaves := rootLeaves_graphDemand_homogeneous η μ E hE hbalance I Iᶜ hI hrow
  have : IsFiniteMeasure (rootLeaves η I) := by
    constructor
    rw [hleaves, Measure.smul_apply, Measure.restrict_apply_univ]
    change μ I * μ Iᶜ < ∞
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (measure_ne_top μ I) (measure_ne_top μ Iᶜ))
  have hm : (rootLeaves η I).real univ = μ.real I * (1 - μ.real I) := by
    rw [measureReal_def, hleaves, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, ENNReal.toReal_mul]
    change μ.real I * μ.real Iᶜ = _
    rw [measureReal_compl hI, probReal_univ]
  rw [← hm]
  exact cost_le_half_rootLeaves_mass η I hI hsmall hroot

end Erdos1017.PhysicalPrimal
