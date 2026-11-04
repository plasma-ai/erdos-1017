module

public import Erdos1017.Exclusions.Common.ConditionalCliqueAverages

/-!
# Rooted counts from conditional region averages

This module defines the charge average `regionPairCharge` under two
independently conditioned region laws and the rooted coefficients
`h, v, p, q, r`, computes the one-root, two-region count polynomial, and shows
every rooted conditional count satisfies the full clique test, with only the
root single-use (`rooted_region_count_le_one`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.FiniteArity

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The literal charge average under two independently conditioned
original region laws. -/
def regionPairCharge {κ : Type*} (Y : Ω → Ω → ℝ) (T : κ → Set Ω) (a b : κ) : ℝ :=
  ∫ p, Y p.1 p.2 ∂(cond μ (T a)).prod (cond μ (T b))

omit [IsProbabilityMeasure μ] in
/-- Swapping the two actual conditional laws preserves a symmetric
charge average, including equal region labels. -/
theorem regionPairCharge_symm {κ : Type*} (Y : Ω → Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x) (T : κ → Set Ω) (a b : κ) :
    regionPairCharge μ Y T a b = regionPairCharge μ Y T b a := by
  unfold regionPairCharge
  rw [← integral_prod_swap (fun p : Ω × Ω => Y p.1 p.2)]
  exact integral_congr_ae (Eventually.of_forall (fun p => hYsym p.2 p.1))

/-- Coordinates h,v,p,q,r come from root-to-region averages and the
negatives of the three genuine diffuse pair averages. -/
def rootedRegionCoefficients (Y : Ω → Ω → ℝ) (T : Fin 3 → Set Ω) : Fin 5 → ℝ :=
  ![regionPairCharge μ Y T 0 1, regionPairCharge μ Y T 0 2,
    -regionPairCharge μ Y T 1 1, -regionPairCharge μ Y T 2 2,
    -regionPairCharge μ Y T 1 2]

omit [IsProbabilityMeasure μ] in
/-- The exact one-root, two-region count polynomial of the actual
conditional averages. No limiting or diagonal convention is used. -/
theorem multiplicityCharge_rooted_regions (Y : Ω → Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x) (T : Fin 3 → Set Ω) (k l : ℕ) :
    multiplicityCharge (regionPairCharge μ Y T) ![1, k, l] =
      rootedRegionCoefficients μ Y T 0 * k + rootedRegionCoefficients μ Y T 1 * l -
      rootedRegionCoefficients μ Y T 2 * k * ((k : ℝ) - 1) / 2 -
      rootedRegionCoefficients μ Y T 3 * l * ((l : ℝ) - 1) / 2 -
      rootedRegionCoefficients μ Y T 4 * k * l := by
  have h10 := regionPairCharge_symm μ Y hYsym T 1 0
  have h20 := regionPairCharge_symm μ Y hYsym T 2 0
  have h21 := regionPairCharge_symm μ Y hYsym T 2 1
  simp [multiplicityCharge, Fin.sum_univ_three, rootedRegionCoefficients, h10, h20, h21]
  ring

/-- Every actual rooted conditional count satisfies the original full
clique test. Only the root is single-use; both diffuse regions may occur
with arbitrary natural multiplicities. -/
theorem rooted_region_count_le_one (T : Fin 3 → Set Ω)
    (hT : ∀ a, MeasurableSet (T a)) (hpos : ∀ a, 0 < μ (T a))
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hfull : ∀ n, FeasibleOrder μ A Y n)
    (hclique : ∀ a b, (a ≠ 0 ∨ b ≠ 0) → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T a → p.2 ∈ T b → A p.1 p.2 = true) (k l : ℕ) :
    rootedRegionCoefficients μ Y T 0 * k + rootedRegionCoefficients μ Y T 1 * l -
      rootedRegionCoefficients μ Y T 2 * k * ((k : ℝ) - 1) / 2 -
      rootedRegionCoefficients μ Y T 3 * l * ((l : ℝ) - 1) / 2 -
      rootedRegionCoefficients μ Y T 4 * k * l ≤ 1 := by
  rw [← multiplicityCharge_rooted_regions μ Y hYsym T k l]
  exact conditional_multiplicity_average_le_one T hT hpos A Y hY B hbound ![1, k, l]
    (hfull _) (fun a ha => hclique a a (Or.inl (fun he => by simp [he] at ha)))
    (fun a b hab _ _ => hclique a b (by
      by_cases ha : a = 0
      · exact Or.inr (fun hb => hab (ha.trans hb.symm))
      · exact Or.inl ha))

end Erdos1017.FiniteArity
