module

public import Erdos1017.Exclusions.Cusp.MarkedMissingEdit
public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyValues

/-!
# Values of the marked missing edit

The linear and quadratic density terms and the linear objective term are
measurable and bounded. The edited objective keeps the quadratic probability
that both source endpoints were marked under any original law, and the marked
density keeps every source-source quadratic term and both cross rectangles
before their symmetry is integrated.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.MarkedMissingEdit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def densityLinear (A : Ω → Ω → Bool) (J N : Set Ω) (x y : Ω) : ℝ :=
  (J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y) -
    (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) (x, y)

def densityQuadratic (A : Ω → Ω → Bool) (J : Set Ω) (x y : Ω) : ℝ :=
  (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) (x, y) / 2

def objectiveLinear (Y : Ω → Ω → ℝ) (J : Set Ω) (x y : Ω) : ℝ :=
  -(J ×ˢ J).indicator (Function.uncurry Y) (x, y)

private theorem integral_marked (alpha : unitInterval) (H : (Ω × Bool) → (Ω × Bool) → ℝ)
    (hH : Measurable (Function.uncurry H)) (B : ℝ) (hB : ∀ x y, ‖H x y‖ ≤ B) :
    (∫ p, H p.1 p.2 ∂(CappedModel.universalMeasure μ alpha).prod
      (CappedModel.universalMeasure μ alpha)) =
      ∫ p : Ω × Ω, (alpha : ℝ) ^ 2 * H (p.1, true) (p.2, true) +
        (alpha : ℝ) * (1 - (alpha : ℝ)) * H (p.1, true) (p.2, false) +
        (1 - (alpha : ℝ)) * (alpha : ℝ) * H (p.1, false) (p.2, true) +
        (1 - (alpha : ℝ)) ^ 2 * H (p.1, false) (p.2, false) ∂μ.prod μ := by
  let F : (Ω × Ω) × (Bool × Bool) → ℝ :=
    fun p => H (p.1.1, p.2.1) (p.1.2, p.2.2)
  have hF : Measurable F := hH.comp
    (((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hi : Integrable F ((μ.prod μ).prod
      ((bernoulliMeasure true false alpha).prod (bernoulliMeasure true false alpha))) :=
    Integrable.of_bound hF.aestronglyMeasurable B (Eventually.of_forall (fun p => hB _ _))
  have hm := integral_map_of_stronglyMeasurable
    (μ := (CappedModel.universalMeasure μ alpha).prod (CappedModel.universalMeasure μ alpha))
    (CappedModel.universal_pair_shuffle (μ := μ) alpha).measurable hF.stronglyMeasurable
  rw [(CappedModel.universal_pair_shuffle (μ := μ) alpha).map_eq] at hm
  change (∫ p, F ((p.1.1, p.2.1), (p.1.2, p.2.2))
    ∂(CappedModel.universalMeasure μ alpha).prod (CappedModel.universalMeasure μ alpha)) = _
  rw [← hm, integral_prod _ hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  dsimp only [F]
  rw [integral_prod _ Integrable.of_finite]
  simp only [integral_bernoulliMeasure, smul_eq_mul]
  ring

theorem measurable_densityLinear (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    Measurable (Function.uncurry (densityLinear A J N)) := by
  have hG : Measurable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hA measurable_const) measurable_const
  exact ((measurable_const.sub hG).indicator (hJ.prod hN)).sub (hG.indicator (hJ.prod hJ))

theorem measurable_densityQuadratic (A : Ω → Ω → Bool) (J : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) :
    Measurable (Function.uncurry (densityQuadratic A J)) := by
  have hG : Measurable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hA measurable_const) measurable_const
  exact (hG.indicator (hJ.prod hJ)).div_const 2

theorem measurable_objectiveLinear (Y : Ω → Ω → ℝ) (J : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hJ : MeasurableSet J) :
    Measurable (Function.uncurry (objectiveLinear Y J)) :=
  (hY.indicator (hJ.prod hJ)).neg

omit [MeasurableSpace Ω] in
theorem densityLinear_bound (A : Ω → Ω → Bool) (J N : Set Ω) (x y : Ω) :
    ‖densityLinear A J N x y‖ ≤ 2 := by
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;> by_cases hn : y ∈ N <;>
    cases ha : A x y <;> norm_num [densityLinear, Set.indicator, hx, hy, hn, ha]

omit [MeasurableSpace Ω] in
theorem densityQuadratic_bound (A : Ω → Ω → Bool) (J : Set Ω) (x y : Ω) :
    ‖densityQuadratic A J x y‖ ≤ 1 := by
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;>
    cases ha : A x y <;> norm_num [densityQuadratic, Set.indicator, hx, hy, ha]

omit [MeasurableSpace Ω] in
theorem objectiveLinear_bound (Y : Ω → Ω → ℝ) (J : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω) : ‖objectiveLinear Y J x y‖ ≤ B := by
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J <;>
    simp only [objectiveLinear, Set.mem_prod, hx, hy, and_self, and_true, and_false,
      ite_true, ite_false, Set.indicator_apply, neg_zero, norm_zero, norm_neg]
  all_goals first | exact hY _ _ | exact hB

omit [MeasurableSpace Ω] in
private theorem density_coins (A : Ω → Ω → Bool) (J N : Set Ω) (hdis : Disjoint J N)
    (alpha : ℝ) (x y : Ω) :
    alpha ^ 2 * (if adjacency A J N (x, true) (y, true) = true then 1 else 0) +
      alpha * (1 - alpha) * (if adjacency A J N (x, true) (y, false) = true then 1 else 0) +
      (1 - alpha) * alpha * (if adjacency A J N (x, false) (y, true) = true then 1 else 0) +
      (1 - alpha) ^ 2 * (if adjacency A J N (x, false) (y, false) = true then 1 else 0) =
      (if A x y = true then 1 else 0) +
        alpha * ((J ×ˢ N).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y) +
          (N ×ˢ J).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y)) -
        (2 * alpha - alpha ^ 2) *
          (J ×ˢ J).indicator (fun p => if A p.1 p.2 = true then 1 else 0) (x, y) := by
  by_cases hxJ : x ∈ J <;> by_cases hyJ : y ∈ J <;>
    by_cases hxN : x ∈ N <;> by_cases hyN : y ∈ N
  all_goals first
    | exact False.elim (disjoint_left.mp hdis hxJ hxN)
    | exact False.elim (disjoint_left.mp hdis hyJ hyN)
    | skip
  all_goals cases ha : A x y <;>
    simp [adjacency, active, removed, filled, Set.indicator, hxJ, hyJ, hxN, hyN, ha] <;> ring

omit [MeasurableSpace Ω] in
private theorem objective_coins (Y : Ω → Ω → ℝ) (J : Set Ω) (alpha : ℝ) (x y : Ω) :
    alpha ^ 2 * charge Y J (x, true) (y, true) +
      alpha * (1 - alpha) * charge Y J (x, true) (y, false) +
      (1 - alpha) * alpha * charge Y J (x, false) (y, true) +
      (1 - alpha) ^ 2 * charge Y J (x, false) (y, false) =
      Y x y - (2 * alpha - alpha ^ 2) * (J ×ˢ J).indicator (Function.uncurry Y) (x, y) := by
  by_cases hxJ : x ∈ J <;> by_cases hyJ : y ∈ J <;>
    simp [charge, removed, Set.indicator, hxJ, hyJ] <;> ring

/-- The exact edited objective retains the quadratic probability that both
source endpoints were marked, under any original probability law. -/
theorem objective_marked (alpha : unitInterval) (Y : Ω → Ω → ℝ) (J : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hJ : MeasurableSet J)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure μ alpha) (charge Y J) =
      FiniteCappedSamplingCost.physicalObjective μ Y +
        (alpha : ℝ) * (∫ p : Ω × Ω, objectiveLinear Y J p.1 p.2 ∂μ.prod μ) -
        (alpha : ℝ) ^ 2 * (∫ p : Ω × Ω, objectiveLinear Y J p.1 p.2 ∂μ.prod μ) / 2 := by
  have hi : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound _ _))
  unfold FiniteCappedSamplingCost.physicalObjective
  rw [integral_marked alpha _ (measurable_charge Y J hY hJ) B (charge_bound Y J B hB hbound)]
  simp_rw [objective_coins]
  simp only [Prod.eta]
  have hsub := integral_sub hi ((hi.indicator (hJ.prod hJ)).const_mul (2 * (alpha : ℝ) - (alpha : ℝ) ^ 2))
  simp only [Function.uncurry] at hsub
  rw [hsub, integral_const_mul]
  have hlin : (∫ p : Ω × Ω, objectiveLinear Y J p.1 p.2 ∂μ.prod μ) =
      -(∫ p, (J ×ˢ J).indicator (Function.uncurry Y) p ∂μ.prod μ) := by
    exact integral_neg _
  rw [hlin]
  ring

/-- The same marked law retains every source-source quadratic term and
both original cross rectangles before their symmetry is integrated. -/
theorem density_marked (alpha : unitInterval) (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) (hN : MeasurableSet N)
    (hdis : Disjoint J N) (hAsym : ∀ x y, A x y = A y x) :
    FiniteCappedSamplingCost.physicalDensity (CappedModel.universalMeasure μ alpha) (adjacency A J N) =
      FiniteCappedSamplingCost.physicalDensity μ A +
        (alpha : ℝ) * (∫ p : Ω × Ω, densityLinear A J N p.1 p.2 ∂μ.prod μ) +
        (alpha : ℝ) ^ 2 * (∫ p : Ω × Ω, densityQuadratic A J p.1 p.2 ∂μ.prod μ) := by
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
  have hAdj := measurable_adjacency A J N hA hJ hN
  have hAdjReal : Measurable (fun p : (Ω × Bool) × (Ω × Bool) =>
      if adjacency A J N p.1 p.2 = true then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hAdj measurable_const) measurable_const
  unfold FiniteCappedSamplingCost.physicalDensity
  rw [integral_marked alpha (fun x y => if adjacency A J N x y = true then (1 : ℝ) else 0) hAdjReal 1
    (fun x y => by cases ha : adjacency A J N x y <;> norm_num [ha])]
  simp_rw [density_coins A J N hdis]
  have hsub := integral_sub (hG.add ((hJN.add hNJ).const_mul (alpha : ℝ)))
    (hJJ.const_mul (2 * (alpha : ℝ) - (alpha : ℝ) ^ 2))
  simp only [Pi.add_apply] at hsub
  rw [hsub]
  have hadd := integral_add hG ((hJN.add hNJ).const_mul (alpha : ℝ))
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_const_mul, integral_const_mul, integral_add hJN hNJ]
  have hswap : (∫ p, (N ×ˢ J).indicator K p ∂μ.prod μ) =
      ∫ p, (J ×ˢ N).indicator K p ∂μ.prod μ := by
    rw [← integral_prod_swap (fun p : Ω × Ω => (J ×ˢ N).indicator K p)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hx : p.1 ∈ N <;> by_cases hy : p.2 ∈ J <;>
      simp [Set.indicator, hx, hy, K, G, hAsym]
  rw [hswap]
  have hlin : (∫ p : Ω × Ω, densityLinear A J N p.1 p.2 ∂μ.prod μ) =
      (∫ p, (J ×ˢ N).indicator K p ∂μ.prod μ) -
        ∫ p, (J ×ˢ J).indicator G p ∂μ.prod μ := integral_sub hJN hJJ
  have hquad : (∫ p : Ω × Ω, densityQuadratic A J p.1 p.2 ∂μ.prod μ) =
      (∫ p, (J ×ˢ J).indicator G p ∂μ.prod μ) / 2 := integral_div _ _
  rw [hlin, hquad]
  ring

end Erdos1017.MarkedMissingEdit
