module

public import Erdos1017.Exclusions.Cusp.DispersedMissingEdit

/-!
# Density and objective of the dispersed edit

Exact formulas under the same law: the dispersed density gains every missing
body pair and loses every missing-region edge, and the objective pays every
missing-region charge and the positive body charge. Under every absolutely
continuous original law these values obey the scalar limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.DispersedMissingEdit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
private theorem density_pointwise (A : Ω → Ω → Bool) (J N : Set Ω) (hdis : Disjoint J N)
    (x y : Ω) :
    (if adjacency A J N x y = true then (1 : ℝ) else 0) =
      (if A x y = true then 1 else 0) +
        (J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y) +
        (N ×ˢ J).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y) -
        (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) (x, y) := by
  by_cases hxJ : x ∈ J <;> by_cases hyJ : y ∈ J <;>
    by_cases hxN : x ∈ N <;> by_cases hyN : y ∈ N
  all_goals first
    | exact False.elim (disjoint_left.mp hdis hxJ hxN)
    | exact False.elim (disjoint_left.mp hdis hyJ hyN)
    | skip
  all_goals cases ha : A x y <;>
    simp [adjacency, removed, filled, Set.indicator, hxJ, hyJ, hxN, hyN, ha]

omit [MeasurableSpace Ω] in
private theorem objective_pointwise (Y : Ω → Ω → ℝ) (J N : Set Ω) (hdis : Disjoint J N)
    (x y : Ω) :
    charge Y J N x y =
      Y x y - (J ×ˢ J).indicator (Function.uncurry Y) (x, y) -
        (N ×ˢ N).indicator (fun p => max (Y p.1 p.2) 0) (x, y) := by
  have hm := min_add_max (Y x y) 0
  by_cases hxJ : x ∈ J <;> by_cases hyJ : y ∈ J <;>
    by_cases hxN : x ∈ N <;> by_cases hyN : y ∈ N
  all_goals first
    | exact False.elim (disjoint_left.mp hdis hxJ hxN)
    | exact False.elim (disjoint_left.mp hdis hyJ hyN)
    | skip
  all_goals simp [charge, removed, body, Set.indicator, hxJ, hyJ, hxN, hyN]
  linarith

/-- The exact dispersed density under the same law: every missing body pair
is gained and every missing-region edge is lost. -/
theorem density_eq (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) (hN : MeasurableSet N)
    (hdis : Disjoint J N) (hAsym : ∀ x y, A x y = A y x) :
    FiniteCappedSamplingCost.physicalDensity μ (adjacency A J N) =
      FiniteCappedSamplingCost.physicalDensity μ A +
        (∫ p, (J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) p
          ∂μ.prod μ) -
        (∫ p, (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) p
          ∂μ.prod μ) / 2 := by
  let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  let K : Ω × Ω → ℝ := fun p => 1 - G p
  have hGmeas : Measurable G :=
    measurable_const.ite (measurableSet_eq_fun hA measurable_const) measurable_const
  have hG : Integrable G (μ.prod μ) := Integrable.of_bound hGmeas.aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by cases ha : A p.1 p.2 <;> norm_num [G, ha]))
  have hK : Integrable K (μ.prod μ) := (integrable_const 1).sub hG
  have hJJ := hG.indicator (hJ.prod hJ)
  have hJN := hK.indicator (hJ.prod hN)
  have hNJ := hK.indicator (hN.prod hJ)
  unfold FiniteCappedSamplingCost.physicalDensity
  simp_rw [density_pointwise A J N hdis]
  have hsub := integral_sub ((hG.add hJN).add hNJ) hJJ
  simp only [Pi.add_apply] at hsub
  rw [hsub]
  have hadd := integral_add (hG.add hJN) hNJ
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hG hJN]
  have hswap : (∫ p, (N ×ˢ J).indicator K p ∂μ.prod μ) =
      ∫ p, (J ×ˢ N).indicator K p ∂μ.prod μ := by
    rw [← integral_prod_swap (fun p : Ω × Ω => (J ×ˢ N).indicator K p)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hx : p.1 ∈ N <;> by_cases hy : p.2 ∈ J <;>
      simp [Set.indicator, hx, hy, K, G, hAsym]
  rw [hswap]
  ring

/-- The exact dispersed objective under the same law pays every
missing-region charge and the entire positive body charge. -/
theorem objective_eq (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hJ : MeasurableSet J) (hN : MeasurableSet N)
    (hdis : Disjoint J N) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B) :
    FiniteCappedSamplingCost.physicalObjective μ (charge Y J N) =
      FiniteCappedSamplingCost.physicalObjective μ Y -
        (∫ p, (J ×ˢ J).indicator (Function.uncurry Y) p ∂μ.prod μ) / 2 -
        (∫ p, (N ×ˢ N).indicator (fun p => max (Y p.1 p.2) 0) p ∂μ.prod μ) / 2 := by
  have hi : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound _ _))
  have hpos : Integrable (fun p : Ω × Ω => max (Y p.1 p.2) 0) (μ.prod μ) := hi.pos_part
  unfold FiniteCappedSamplingCost.physicalObjective
  simp_rw [objective_pointwise Y J N hdis]
  have hsub := integral_sub (hi.sub (hi.indicator (hJ.prod hJ))) (hpos.indicator (hN.prod hN))
  simp only [Pi.sub_apply, Function.uncurry] at hsub
  rw [hsub]
  have hsub' := integral_sub hi (hi.indicator (hJ.prod hJ))
  simp only [Function.uncurry] at hsub'
  rw [hsub']
  ring

/-- Under every absolutely continuous old law, the actual dispersed
competitor's exact density and value obey the full scalar limit. -/
theorem objective_le_densityLimit_values
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hY : Measurable (Function.uncurry Y))
    (hJ : MeasurableSet J) (hN : MeasurableSet N) (hdis : Disjoint J N)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) :
    FiniteCappedSamplingCost.physicalObjective ν Y -
        (∫ p, (J ×ˢ J).indicator (Function.uncurry Y) p ∂ν.prod ν) / 2 -
        (∫ p, (N ×ˢ N).indicator (fun p => max (Y p.1 p.2) 0) p ∂ν.prod ν) / 2 ≤
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity ν A +
        (∫ p, (J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) p
          ∂ν.prod ν) -
        (∫ p, (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) p
          ∂ν.prod ν) / 2) := by
  rw [← objective_eq Y J N hY hJ hN hdis B hbound, ← density_eq A J N hA hJ hN hdis hAsym]
  exact objective_le_densityLimit_ac A Y J N hA hY hJ hN hAsym hYsym B hB hbound hzero
    hmiss hfull ν hac

end Erdos1017.DispersedMissingEdit
