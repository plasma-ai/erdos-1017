module

public import Erdos1017.Exclusions.Common.Universal.UniversalRootColumnCount
public import Erdos1017.Exclusions.Common.Physical.PhysicalRootReplacement

/-!
# Root leaves and degree incidence

With at most one root per parent, each coordinate is counted at most once as a
root leaf, root leaves of order at least four pay three incidences in the degree
measure, and universal root-pair quotas make every exterior event without
order-two or order-three root incidence null.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- With at most one root, each actual parent coordinate is counted at
most once as a root leaf. The original parent law remains unchanged. -/
theorem orderRootLeaves_le_orderFirstOccupation (n : ℕ)
    (ρ : Measure (Fin n → Ω)) (I : Set Ω) (hI : MeasurableSet I)
    (hunique : ∀ᵐ v ∂ρ, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    orderRootLeaves n ρ I ≤ orderFirstOccupation n ρ := by
  classical
  have hd := PhysicalRootReplacement.rootedLaw_decomposition I hI ρ hunique
  have hm : (∑ i : Fin n, PhysicalRootReplacement.rootedLaw ρ I i) ≤ ρ := by
    intro s
    have h := congrArg (fun ν : Measure (Fin n → Ω) => ν s) hd
    rw [Measure.add_apply] at h
    exact (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤
      PhysicalRootReplacement.noRootLaw ρ I s from zero_le)).trans_eq h
  apply Measure.le_iff.mpr
  intro B hB
  let a := fun i j : Fin n => ρ ((fun v : Fin n → Ω => v j) ⁻¹' B ∩ {v | v i ∈ I})
  have ha (j : Fin n) : (∑ i : Fin n, a i j) ≤ ρ ((fun v : Fin n → Ω => v j) ⁻¹' B) := by
    have h := hm ((fun v : Fin n → Ω => v j) ⁻¹' B)
    have hT : MeasurableSet ((fun v : Fin n → Ω => v j) ⁻¹' B) :=
      hB.preimage (measurable_pi_apply j)
    simpa only [Measure.finsetSum_apply, PhysicalRootReplacement.rootedLaw,
      Measure.restrict_apply hT, a] using h
  have hleaves : orderRootLeaves n ρ I B = ∑ ij : PairIndex n, a ij.val.1 ij.val.2 := by
    rw [orderRootLeaves, Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro ij _
    rw [Measure.map_apply (measurable_pi_apply _) hB,
      Measure.restrict_apply ((measurable_pi_apply _) hB)]
  have hsum : (∑ ij : PairIndex n, a ij.val.1 ij.val.2) =
      ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then a i j else 0 := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then a ij.1 ij.2 else 0), ← Finset.sum_filter]
    exact (Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
      (fun ij => a ij.1 ij.2)).symm
  rw [hleaves, hsum]
  calc
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then a i j else 0) ≤
        ∑ i : Fin n, ∑ j : Fin n, a i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = ∑ j : Fin n, ∑ i : Fin n, a i j := Finset.sum_comm
    _ ≤ ∑ j : Fin n, ρ ((fun v : Fin n → Ω => v j) ⁻¹' B) :=
      Finset.sum_le_sum (fun j _ => ha j)
    _ = orderFirstOccupation n ρ B := by
      rw [orderFirstOccupation, Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      exact (Measure.map_apply (measurable_pi_apply j) hB).symm

/-- If orders below four have no root leaves in B, every remaining
root leaf pays at least three incidences in the original degree measure. -/
theorem three_rootLeaves_le_degree (η : Laws Ω) (I : Set Ω) (hI : MeasurableSet I)
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j, v i ∈ I → v j ∈ I → i = j)
    (B : Set Ω) (hsmall : ∀ n, n < 4 → orderRootLeaves n (η n) I B = 0) :
    3 * rootLeaves η I B ≤ (occupation η).fst B := by
  have hord (n : ℕ) : 3 * orderRootLeaves n (η n) I B ≤ (orderOccupation n (η n)).fst B := by
    by_cases hn : 4 ≤ n
    · have h := orderRootLeaves_le_orderFirstOccupation n (η n) I hI (hunique n) B
      rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
      have hn' : (3 : ℝ≥0∞) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 3 ≤ n - 1 by omega)
      exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ≥0∞) ≤ 3)).trans
        (mul_le_mul_of_nonneg_right hn' (show (0 : ℝ≥0∞) ≤
          orderFirstOccupation n (η n) B from zero_le))
    · rw [hsmall n (by omega), mul_zero]
      exact zero_le
  rw [rootLeaves, Measure.sum_apply_of_countable, ← ENNReal.tsum_mul_left,
    occupation, Measure.fst_sum, Measure.sum_apply_of_countable]
  exact ENNReal.tsum_le_tsum hord

/-- Universal root-pair quotas and the actual degree bound force every
exterior event with no order-two or order-three root incidence to be null
when the original root mass is above one third. -/
theorem null_event_of_small_root_incidence (η : Laws Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set (Ω × Ω)) (hE : MeasurableSet E)
    (hbalance : occupation η = graphDemand μ E) (I : Set Ω) (hI : MeasurableSet I)
    (hrow : ∀ᵐ p ∂(μ.restrict I).prod μ, p ∈ E ↔ p.2 ∉ I)
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j, v i ∈ I → v j ∈ I → i = j)
    (B : Set Ω) (hB : MeasurableSet B) (hBI : B ⊆ Iᶜ)
    (hsmall : ∀ n, n < 4 → orderRootLeaves n (η n) I B = 0)
    (hA : 1 / 3 < μ.real I) : μ B = 0 := by
  have h := three_rootLeaves_le_degree η I hI hunique B hsmall
  rw [hbalance] at h
  have hd := graphDemand_fst_le μ E B
  have hleaves := rootLeaves_graphDemand_homogeneous η μ E hE hbalance I Iᶜ hI hrow
  have htotal : 3 * (μ I * μ B) ≤ μ B := by
    rw [hleaves, Measure.smul_apply, Measure.restrict_apply hB,
      inter_eq_left.mpr hBI, smul_eq_mul] at h
    exact h.trans hd
  have hr := ENNReal.toReal_mono (measure_ne_top μ B) htotal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hr
  by_contra hnull
  have hBpos : 0 < (μ B).toReal := ENNReal.toReal_pos hnull (measure_ne_top μ B)
  have hcoef : 0 < 3 * (μ I).toReal - 1 := by change 0 < 3 * μ.real I - 1; linarith
  nlinarith [mul_pos hcoef hBpos]

end Erdos1017.PhysicalPrimal
