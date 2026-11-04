module

public import Erdos1017.Models.Capped.CappedColorConfiguration
public import Erdos1017.IntegerTransfer.FractionalCliqueTruncation

/-!
# Finite capped error bound for sampled configurations

This module tests through order `r` bound the capped objective by the cost of
fractional partitions on cliques of those orders, the capped dual error is paid
by a truncated optimal fractional partition, and the bound holds for every
sampled configuration on one full-measure set.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.WeightedGraph

variable {n : ℕ}

/-- Tests through order r bound the objective by the cost of any fractional
partition supported on cliques of those orders. -/
theorem capped_objective_le_subset_cost (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (r : ℕ)
    (hzero : ∀ i j, ¬G.Adj i j → y i j = 0)
    (htests : ∀ S : Finset (Fin n), 2 ≤ S.card → S.card ≤ r →
      G.IsClique (S : Set (Fin n)) → charge y S ≤ 1)
    (w : Finset (Fin n) → ℝ) (hw : FractionalGraph.SubsetFeasible G w)
    (horder : ∀ S, w S ≠ 0 → S.card ≤ r) :
    objective (fun _ => 1) y ≤ ∑ S, w S := by
  have hcharge : objective (fun _ => 1) y = ∑ S, w S * charge y S := by
    rw [weighted_charge_identity]
    unfold objective
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · simp [hw.2.2 i j hij]
    · simp [hzero i j hij]
  rw [hcharge]
  apply Finset.sum_le_sum
  intro S _
  by_cases hz : w S = 0
  · simp [hz]
  · obtain ⟨hsize, hclique⟩ := hw.2.1 S hz
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (htests S hsize (horder S hz) hclique) (hw.1 S)

/-- The finite capped dual error is paid by an actual truncated optimal
fractional partition, without assuming any omitted clique test. -/
theorem capped_objective_le_value (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hzero : ∀ i j, ¬G.Adj i j → y i j = 0)
    (htests : ∀ S : Finset (Fin n), 2 ≤ S.card → S.card ≤ r →
      G.IsClique (S : Set (Fin n)) → charge y S ≤ 1) :
    objective (fun _ => 1) y ≤
      FractionalGraph.value G + (G.edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) := by
  obtain ⟨w, hw, horder, hcost⟩ :=
    FractionalGraph.exists_bounded_clique_partition G r hr
  exact (capped_objective_le_subset_cost G y r hzero htests w hw horder).trans hcost

end Erdos1017.WeightedGraph

namespace Erdos1017.CappedModel

variable {n : ℕ}

/-- Every sampled colored configuration satisfying the imposed subclique
tests obeys the finite capped-error bound. -/
theorem configuration_charge_le_value (c : CliquePair n → CappedColor)
    (r : ℕ) (hr : 2 ≤ r)
    (htests : ∀ k, 2 ≤ k → k ≤ r → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    (∑ p, CappedColor.charge (c p)) ≤ FractionalGraph.value (configurationGraph c) +
      ((configurationGraph c).edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) := by
  rw [← chargeMatrix_objective]
  apply WeightedGraph.capped_objective_le_value (configurationGraph c)
    (chargeMatrix c) r hr (chargeMatrix_nonedge c)
  intro S hsize horder hclique
  let e := S.orderEmbOfFin rfl
  have ht := htests S.card hsize horder e
  have hp (p : CliquePair S.card) : CappedColor.adjacency (c (pairEmbedding e p)) = 1 := by
    have h := hclique (S.orderEmbOfFin_mem rfl p.val.1)
      (S.orderEmbOfFin_mem rfl p.val.2) (e.strictMono p.property).ne
    change CappedColor.adjacency (pairColor c (e p.val.1) (e p.val.2)) = 1 at h
    rwa [pairColor_lt _ _ _ (e.strictMono p.property)] at h
  simp only [violation, hp, Finset.prod_const_one, mul_one] at ht
  rw [chargeMatrix_subset]
  have hle := le_max_left ((∑ p, CappedColor.charge (c (pairEmbedding e p))) - 1) 0
  rw [ht] at hle
  linarith

/-- The sampled finite-graph inequality holds on a single full-measure set
for every capped model and every sample size. -/
theorem ae_configuration_charge_le_value {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (W : Model Ω μ) {r : ℕ} (hr : 2 ≤ r) (hW : Feasible r W) (n : ℕ) :
    ∀ᵐ x ∂MeasureTheory.Measure.pi (fun _ : Fin n => μ), ∀ᵐ c ∂cliqueLaw W x,
      (∑ p, CappedColor.charge (c p)) ≤ FractionalGraph.value (configurationGraph c) +
        ((configurationGraph c).edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) := by
  filter_upwards [ae_all_subclique_tests W hW n] with x hx
  filter_upwards [hx] with c hc
  exact configuration_charge_le_value c r hr hc

end Erdos1017.CappedModel
