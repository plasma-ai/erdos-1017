module

public import Erdos1017.IntegerTransfer.MultipartiteBaseMoments

/-!
# Concentration of extension counts on base cliques

This module defines the predicted number of extensions of a complete base
transversal and proves quantitative concentration of the extension counts around
it, with regularity of the original pairs as the only graph hypothesis
(`exceptional_extension_bound`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteExtension

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {t u : ℕ}

/-- The predicted number of extensions of a complete base transversal. -/
def prediction (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] : ℝ :=
  (Fintype.card A : ℝ) ^ u * extensionDensity G

omit [DecidableEq A] in
theorem prediction_bounds (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj] :
    0 ≤ prediction G ∧ prediction G ≤ (Fintype.card A : ℝ) ^ u := by
  have h0 : ∀ e ∈ SharedBasePattern.extensionEdges t u,
      0 ≤ (G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2) : ℝ) := by
    intro e _
    exact_mod_cast G.edgeDensity_nonneg (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2)
  have h1 : extensionDensity G ≤ 1 := Finset.prod_le_one₀ h0 (by
    intro e _
    exact_mod_cast G.edgeDensity_le_one (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2))
  exact ⟨mul_nonneg (by positivity) (Finset.prod_nonneg h0),
    mul_le_of_le_one_right (by positivity) h1⟩

/-- Quantitative concentration of the actual extension counts on actual base
cliques. The only graph hypothesis is regularity of the original pairs. -/
theorem exceptional_extension_bound (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hreg : ∀ i j : Fin (t + u), i < j →
      G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    τ ^ 2 * (((bases G).filter (fun x =>
      τ ≤ |CliqueExtension.count (extensionRelation G) x - prediction G|)).card : ℝ) ≤
      ε * (Fintype.card A : ℝ) ^ (t + u + u) *
        ((SharedBasePattern.edges t u).card + 2 * (completeEdges (t + u)).card +
          3 * (completeEdges t).card : ℝ) := by
  let n : ℝ := Fintype.card A
  let μ := prediction G
  let ν := n ^ t * baseDensity G
  let e₀ := (completeEdges t).card * ε * n ^ t
  let e₁ := (completeEdges (t + u)).card * ε * n ^ (t + u)
  let e₂ := (SharedBasePattern.edges t u).card * ε * n ^ (t + u + u)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hμ : 0 ≤ μ ∧ μ ≤ n ^ u := prediction_bounds G
  have he₀ : 0 ≤ e₀ := by dsimp [e₀]; positivity
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; positivity
  have hbase : |((bases G).card : ℝ) - ν| ≤ e₀ := base_count_error G hε hreg
  have hfirst : |(∑ x ∈ bases G, CliqueExtension.count (extensionRelation G) x) - ν * μ| ≤ e₁ := by
    rw [sum_bases_count]
    have h := first_moment_error G hε hreg
    rw [SharedBasePattern.product_complete] at h
    simpa only [ν, μ, prediction, baseDensity, extensionDensity, n, e₁, pow_add,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hsecond : |(∑ x ∈ bases G, CliqueExtension.count (extensionRelation G) x ^ 2) - ν * μ ^ 2| ≤ e₂ := by
    rw [sum_bases_count_sq]
    have h := second_moment_error G hε hreg
    rw [SharedBasePattern.product_double_factor t u
      (fun e => (G.edgeDensity (MultipartiteCounting.part e.1)
        (MultipartiteCounting.part e.2) : ℝ))] at h
    simpa only [ν, μ, prediction, baseDensity, extensionDensity, n, e₂, pow_add,
      mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hb := abs_le.mp hbase
  have hf := abs_le.mp hfirst
  have hs := abs_le.mp hsecond
  have hfirst' : (bases G).card * μ - (e₁ + μ * e₀) ≤
      ∑ x ∈ bases G, CliqueExtension.count (extensionRelation G) x := by
    have hmul := mul_le_mul_of_nonneg_right hb.2 hμ.1
    nlinarith
  have hsecond' : (∑ x ∈ bases G, ∑ y, ∑ z,
      if extensionRelation G x y ∧ extensionRelation G x z then (1 : ℝ) else 0) ≤
      (bases G).card * μ ^ 2 + (e₂ + μ ^ 2 * e₀) := by
    simp_rw [← CliqueExtension.count_sq]
    have hmul := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg μ)
    nlinarith
  have hc := CliqueExtension.exceptional_bases_le (extensionRelation G) (bases G)
    μ τ (e₁ + μ * e₀) (e₂ + μ ^ 2 * e₀) hμ.1 hτ hfirst' hsecond'
  have hm₁ := mul_le_mul_of_nonneg_right hμ.2 he₁
  have hm₂ : μ ^ 2 * e₀ ≤ (n ^ u) ^ 2 * e₀ := by
    apply mul_le_mul_of_nonneg_right _ he₀
    nlinarith [pow_nonneg hn u]
  calc
    _ ≤ (e₂ + μ ^ 2 * e₀) + 2 * μ * (e₁ + μ * e₀) := hc
    _ ≤ e₂ + 2 * n ^ u * e₁ + 3 * (n ^ u) ^ 2 * e₀ := by nlinarith
    _ = _ := by dsimp [e₀, e₁, e₂, n]; simp only [pow_add, pow_two]; ring

end Erdos1017.MultipartiteExtension
