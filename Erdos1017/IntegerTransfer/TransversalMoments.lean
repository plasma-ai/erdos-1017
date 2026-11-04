module

public import Erdos1017.IntegerTransfer.ThinnedGraph

/-!
# Mean and variance of thinned transversal extensions

With a common thinning probability between each pair of parts, the thinned
extension mean of any family of extensions is exact, the variance has order
`n^(2u-1)`, and the relative deviation mass is `O(1/n)` with a coefficient
independent of the graph.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- All edges between the same pair of parts have the same thinning probability. -/
def partProbability (q : Fin (t + u) × Fin (t + u) → ℝ)
    (v : Coordinate (t + u) A) : ℝ := q (v.1.1, v.2.1)

/-- The common probability of retaining every non-base edge of an extension. -/
def extensionProbability (q : Fin (t + u) × Fin (t + u) → ℝ) : ℝ :=
  ∏ e ∈ SharedBasePattern.extensionEdges t u, q e

omit [Fintype A] in
/-- The retention probability of an extension depends only on its role labels. -/
theorem support_probability (x : Fin t → A) (y : Fin u → A)
    (q : Fin (t + u) × Fin (t + u) → ℝ) :
    (∏ v ∈ support x y, partProbability q v) = extensionProbability q := by
  rw [support, Finset.prod_image (coordinate_injective _).injOn]
  rfl

omit [Fintype A] in
/-- Exact thinned extension mean, for an arbitrary actual family of extensions. -/
theorem mean_partProbability (F : Finset (Fin u → A)) (x : Fin t → A)
    (q : Fin (t + u) × Fin (t + u) → ℝ) :
    BernoulliFamily.mean F (support x) (partProbability q) = F.card * extensionProbability q := by
  simp only [BernoulliFamily.mean, support_probability, Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq A] in
/-- The family size is at most the total number of extension assignments. -/
theorem family_card_le (F : Finset (Fin u → A)) : F.card ≤ Fintype.card A ^ u := by
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ F)

/-- The variance has order n^(2u−1), uniformly over all original graphs. -/
theorem variance_le_scale (F : Finset (Fin u → A)) (x : Fin t → A)
    (p : Coordinate (t + u) A → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) :
    (∑ X, CliqueSampling.weight p X *
      (((BernoulliFamily.retained F (support x) X).card : ℝ) - BernoulliFamily.mean F (support x) p) ^ 2) ≤
      (Fintype.card A : ℝ) ^ u * ((u : ℝ) * (Fintype.card A : ℝ) ^ (u - 1)) := by
  apply (variance_le F x p hp).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast family_card_le F

/-- Relative deviation mass is O(1/n), with a coefficient independent of the graph. -/
theorem deviation_mass_le [Nonempty A] (hu : 0 < u)
    (F : Finset (Fin u → A)) (x : Fin t → A)
    (p : Coordinate (t + u) A → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (τ : ℝ) (hτ : 0 < τ) :
    (∑ X, if τ * (Fintype.card A : ℝ) ^ u ≤
      |((BernoulliFamily.retained F (support x) X).card : ℝ) - BernoulliFamily.mean F (support x) p| then
      CliqueSampling.weight p X else 0) ≤ (u : ℝ) / (τ ^ 2 * Fintype.card A) := by
  let n : ℝ := Fintype.card A
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hbound := BernoulliFamily.deviation_mass F (support x) p hp
    ((u : ℝ) * n ^ (u - 1)) (τ * n ^ u) (by positivity) (fun y _ => by
      dsimp only [n]
      exact_mod_cast overlap_card_le F x y)
  have hcard : (F.card : ℝ) ≤ n ^ u := by
    dsimp only [n]
    exact_mod_cast family_card_le F
  have hbound := hbound.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hpow : n ^ (u - 1) * n = n ^ u := by
    rw [← pow_succ]
    congr 1
    omega
  apply (le_div_iff₀ (by positivity : 0 < τ ^ 2 * n)).mpr
  apply le_of_mul_le_mul_left (a := n ^ u * n ^ (u - 1)) ?_ (by positivity)
  calc
    _ = (τ * n ^ u) ^ 2 * (∑ X, if τ * n ^ u ≤
        |((BernoulliFamily.retained F (support x) X).card : ℝ) - BernoulliFamily.mean F (support x) p| then
        CliqueSampling.weight p X else 0) := by rw [← hpow]; ring
    _ ≤ n ^ u * ((u : ℝ) * n ^ (u - 1)) := hbound
    _ = _ := by ring

end Erdos1017.TransversalThinning
