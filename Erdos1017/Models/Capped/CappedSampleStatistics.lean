module

public import Erdos1017.Models.Capped.CappedGraphBound
public import Erdos1017.FractionalLimit.FractionalDensityLimit

/-!
# Sampled density and charge of a capped model

The sampled edge density and signed dual objective (`sampleDensity`,
`sampleCharge`) use the same `n`-squared normalization as `F`, and the finite
fractional envelope bounds the sampled charge by the density limit almost surely
for every capped feasible model.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.CappedModel

variable {n : ℕ}

/-- The sampled edge density uses the same n-squared normalization as F. -/
def sampleDensity (c : CliquePair n → CappedColor) : ℝ :=
  (∑ p, CappedColor.adjacency (c p)) / (n : ℝ) ^ 2

/-- The sampled signed dual objective in the same normalization. -/
def sampleCharge (c : CliquePair n → CappedColor) : ℝ :=
  (∑ p, CappedColor.charge (c p)) / (n : ℝ) ^ 2

/-- Counting the present colors gives exactly the edge count of the
actual sampled graph. -/
theorem configuration_adjacency_sum (c : CliquePair n → CappedColor) :
    (∑ p, CappedColor.adjacency (c p)) =
      ((configurationGraph c).edgeSet.ncard : ℝ) := by
  classical
  have hmatrix (i j : Fin n) :
      WeightedGraph.adjacencyMatrix (configurationGraph c) i j =
        CappedColor.adjacency (pairColor c i j) := by
    by_cases h : CappedColor.adjacency (pairColor c i j) = 1
    · simp [WeightedGraph.adjacencyMatrix, configurationGraph, h]
    · rw [color_eq_absent_of_not_present _ h]
      simp [WeightedGraph.adjacencyMatrix, configurationGraph, h]
  rw [← WeightedGraph.adjacency_objective]
  simp only [WeightedGraph.objective, mul_one, hmatrix]
  rw [ordered_sum_eq_twice_upper _
    (fun i j => congrArg CappedColor.adjacency (pairColor_symm c i j))
    (fun i => by simp)]
  have hupper : (∑ i, ∑ j, if i < j then CappedColor.adjacency (pairColor c i j) else 0) =
      ∑ i, ∑ j, if h : i < j then CappedColor.adjacency (c ⟨(i, j), h⟩) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j <;> simp [hij, pairColor]
  have hpair := sum_cliquePair_eq_upper (fun p : CliquePair n => CappedColor.adjacency (c p))
  rw [hupper, ← hpair]
  ring

/-- The finite fractional envelope removes the graph optimization from the
sample bound, leaving continuous functions of the sampled colors. -/
theorem sampleCharge_le_densityLimit (c : CliquePair n → CappedColor)
    (hn : 0 < n) (r : ℕ) (hr : 2 ≤ r) (d : ℝ)
    (htests : ∀ k, 2 ≤ k → k ≤ r → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    sampleCharge c ≤ FractionalGraph.densityLimit d + 3 * |sampleDensity c - d| +
      sampleDensity c / (r.choose 2 : ℝ) := by
  have hcap := configuration_charge_le_value c r hr htests
  rw [← configuration_adjacency_sum c] at hcap
  have hf := FractionalGraph.finite_graph_le_densityLimit (configurationGraph c) hn d
  rw [← configuration_adjacency_sum c] at hf
  have hfinite : FractionalGraph.value (configurationGraph c) / (n : ℝ) ^ 2 ≤
      FractionalGraph.densityLimit d + 3 * |sampleDensity c - d| := by
    change _ - 3 * |sampleDensity c - d| ≤ _ at hf
    linarith
  calc
    sampleCharge c ≤ (FractionalGraph.value (configurationGraph c) +
        (∑ p, CappedColor.adjacency (c p)) / (r.choose 2 : ℝ)) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcap (sq_nonneg _)
    _ = FractionalGraph.value (configurationGraph c) / (n : ℝ) ^ 2 +
        sampleDensity c / (r.choose 2 : ℝ) := by
      unfold sampleDensity
      rw [add_div]
      ring
    _ ≤ _ := by linarith

/-- The bound applies almost surely to the actual independently colored
sample of every capped feasible model. -/
theorem ae_sampleCharge_le_densityLimit {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (W : Model Ω μ) {r : ℕ} (hr : 2 ≤ r) (hW : Feasible r W)
    (n : ℕ) (hn : 0 < n) (d : ℝ) :
    ∀ᵐ x ∂MeasureTheory.Measure.pi (fun _ : Fin n => μ), ∀ᵐ c ∂cliqueLaw W x,
      sampleCharge c ≤ FractionalGraph.densityLimit d + 3 * |sampleDensity c - d| +
        sampleDensity c / (r.choose 2 : ℝ) := by
  filter_upwards [ae_all_subclique_tests W hW n] with x hx
  filter_upwards [hx] with c hc
  exact sampleCharge_le_densityLimit c hn r hr d hc

end Erdos1017.CappedModel
