module

public import Erdos1017.Exclusions.Common.Physical.PhysicalRootReplacement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive-charge covers and tight parents

The positive body energy `bodyPositiveEnergy` is defined, a zero value gives a
product-almost-everywhere positive cover, every tight physical parent meets such
a cover so the rootless restriction of its law vanishes, and pair properties
valid in every parent transfer to the occupied demand.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Squared positive charge on the literal complement of a proposed cover.
The original product measure is retained, without conditional normalization. -/
def bodyPositiveEnergy (μ : Measure Ω) (Y : Ω × Ω → ℝ) (I : Set Ω) : ℝ :=
  ∫ p in Iᶜ ×ˢ Iᶜ, (max (Y p) 0) ^ 2 ∂μ.prod μ

/-- A zero positive-body integral gives the actual product-AE positive
cover. The bounded measurable kernel supplies integrability internally. -/
theorem ae_nonpositive_of_bodyPositiveEnergy_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hB : ∀ p, |Y p| ≤ B)
    (I : Set Ω) (hI : MeasurableSet I) (hzero : bodyPositiveEnergy μ Y I = 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → Y p ≤ 0 := by
  have hi : Integrable (fun p => (max (Y p) 0) ^ 2) ((μ.prod μ).restrict (Iᶜ ×ˢ Iᶜ)) := by
    apply Integrable.of_bound ((hY.max measurable_const).pow_const 2).aestronglyMeasurable (B ^ 2)
    exact Eventually.of_forall (fun p => by
      have hlo : 0 ≤ max (Y p) 0 := le_max_right _ _
      have hhi : max (Y p) 0 ≤ B := (max_le (le_abs_self _) (abs_nonneg _)).trans (hB p)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun p => sq_nonneg (max (Y p) 0))) hi).mp hzero
  have hraw := (ae_restrict_iff' (hI.compl.prod hI.compl)).mp hae
  filter_upwards [hraw] with p hp hx hy
  have hz := hp ⟨hx, hy⟩
  have hm : max (Y p) 0 = 0 := sq_eq_zero_iff.mp hz
  exact (le_max_left _ _).trans hm.le

/-- A tight physical parent must meet any actual positive-charge cover.
Exact ordered pair occupation licenses the argument even when the full
parent law is singular with respect to the product vertex law. -/
theorem ae_parent_meets_positive_cover (η : Laws Ω) (demand : Measure (Ω × Ω))
    (hbalance : occupation η = demand) (Y : Ω × Ω → ℝ) (I : Set Ω)
    (hcover : ∀ᵐ p ∂demand, p.1 ∉ I → p.2 ∉ I → Y p ≤ 0)
    (htight : ∀ n, ∀ᵐ v ∂η n, charge Y v = 1) (n : ℕ) :
    ∀ᵐ v ∂η n, ∃ i, v i ∈ I := by
  classical
  have hp := ae_all_pairs_of_balance η demand hbalance _ hcover n
  filter_upwards [hp, htight n] with v hp ht
  by_contra hn
  push Not at hn
  have hsum : (∑ ij : PairIndex n, Y (v ij.val.1, v ij.val.2)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro ij _
    exact hp _ _ ij.property (hn _) (hn _)
  unfold charge at ht
  linarith

/-- Consequently the literal rootless restriction of every tight parent
law vanishes; this does not replace the parent law by independent draws. -/
theorem noRootLaw_eq_zero_of_positive_cover (η : Laws Ω) (demand : Measure (Ω × Ω))
    (hbalance : occupation η = demand) (Y : Ω × Ω → ℝ) (I : Set Ω)
    (hcover : ∀ᵐ p ∂demand, p.1 ∉ I → p.2 ∉ I → Y p ≤ 0)
    (htight : ∀ n, ∀ᵐ v ∂η n, charge Y v = 1) (n : ℕ) :
    PhysicalRootReplacement.noRootLaw (η n) I = 0 := by
  apply Measure.restrict_eq_zero.mpr
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_parent_meets_positive_cover η demand hbalance Y I hcover htight n]
    with v hv hn
  obtain ⟨i, hi⟩ := hv
  exact hn i hi

/-- Conversely, a measurable pair property valid in every actual parent
holds under its exact occupied demand. This is a transfer through a sum
of pair marginals, not through joint product absolute continuity. -/
theorem ae_pair_of_all_parents (η : Laws Ω) (demand : Measure (Ω × Ω))
    (hbalance : occupation η = demand) (P : Ω × Ω → Prop)
    (hP : MeasurableSet {p | P p})
    (hparents : ∀ n, ∀ᵐ v ∂η n, ∀ i j, i ≠ j → P (v i, v j)) :
    ∀ᵐ p ∂demand, P p := by
  classical
  rw [← hbalance, occupation, Measure.ae_sum_iff]
  intro n
  rw [orderOccupation, ae_finsetSum_measure_iff]
  intro ij _
  apply (ae_map_iff ((measurable_pi_apply _).prodMk
    (measurable_pi_apply _)).aemeasurable hP).mpr
  exact (hparents n).mono (fun _ hv => hv _ _ ij.property)

end Erdos1017.PhysicalPrimal
