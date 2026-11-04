module

public import Erdos1017.Exclusions.Cusp.DominantAtomMarkedEdit
public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyValues

/-!
# Values of the dominant-atom marked edit

The linear density and linear and quadratic cost terms (`densityLinear`,
`costLinear`, `costQuadratic`) are measurable and bounded. The marked clipping
cost keeps its full quadratic marking probability under the same law, and
filling the original U-P nonedges is affine in the marking probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.DominantAtomMarkedEdit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def densityLinear (A : Ω → Ω → Bool) (P U : Set Ω) (x y : Ω) : ℝ :=
  (U ×ˢ P).indicator (fun p => 1 - if A p.1 p.2 = true then 1 else 0) (x, y)

def costLinear (Y : Ω → Ω → ℝ) (I P U : Set Ω) (x y : Ω) : ℝ :=
  (U ×ˢ P).indicator (Function.uncurry Y) (x, y) +
    (U ×ˢ exterior I P).indicator (fun p => max (Y p.1 p.2) 0) (x, y)

def costQuadratic (Y : Ω → Ω → ℝ) (U : Set Ω) (x y : Ω) : ℝ :=
  (U ×ˢ U).indicator (fun p => max (Y p.1 p.2) 0) (x, y) / 2

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

theorem measurable_densityLinear (A : Ω → Ω → Bool) (P U : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hP : MeasurableSet P) (hU : MeasurableSet U) :
    Measurable (Function.uncurry (densityLinear A P U)) := by
  have hG : Measurable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hA measurable_const) measurable_const
  exact (measurable_const.sub hG).indicator (hU.prod hP)

theorem measurable_costLinear (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hY : Measurable (Function.uncurry Y))
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hU : MeasurableSet U) :
    Measurable (Function.uncurry (costLinear Y I P U)) := by
  exact (hY.indicator (hU.prod hP)).add
    ((hY.max measurable_const).indicator (hU.prod (hI.union hP).compl))

theorem measurable_costQuadratic (Y : Ω → Ω → ℝ) (U : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hU : MeasurableSet U) :
    Measurable (Function.uncurry (costQuadratic Y U)) :=
  ((hY.max measurable_const).indicator (hU.prod hU)).div_const 2

omit [MeasurableSpace Ω] in
private theorem density_coins (A : Ω → Ω → Bool) (P U : Set Ω) (hdis : Disjoint U P)
    (hAsym : ∀ x y, A x y = A y x) (alpha : ℝ) (x y : Ω) :
    alpha ^ 2 * (if adjacency A P U (x, true) (y, true) = true then 1 else 0) +
      alpha * (1 - alpha) * (if adjacency A P U (x, true) (y, false) = true then 1 else 0) +
      (1 - alpha) * alpha * (if adjacency A P U (x, false) (y, true) = true then 1 else 0) +
      (1 - alpha) ^ 2 * (if adjacency A P U (x, false) (y, false) = true then 1 else 0) =
      (if A x y = true then 1 else 0) +
        alpha * (densityLinear A P U x y + densityLinear A P U y x) := by
  by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U <;>
    by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
  all_goals first
    | exact False.elim (disjoint_left.mp hdis hxU hxP)
    | exact False.elim (disjoint_left.mp hdis hyU hyP)
    | skip
  all_goals cases ha : A x y <;>
    simp [adjacency, filled, MarkedMissingEdit.active, densityLinear,
      Set.indicator, hxU, hyU, hxP, hyP, hAsym y x, ha] <;> ring

omit [MeasurableSpace Ω] in
private theorem objective_coins (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hU : U ⊆ exterior I P) (hYsym : ∀ x y, Y x y = Y y x) (alpha : ℝ) (x y : Ω) :
    alpha ^ 2 * charge Y I P U (x, true) (y, true) +
      alpha * (1 - alpha) * charge Y I P U (x, true) (y, false) +
      (1 - alpha) * alpha * charge Y I P U (x, false) (y, true) +
      (1 - alpha) ^ 2 * charge Y I P U (x, false) (y, false) =
      Y x y - alpha * (costLinear Y I P U x y + costLinear Y I P U y x) +
        alpha ^ 2 * (2 * costQuadratic Y U x y) := by
  have hUnP {x : Ω} (hx : x ∈ U) : x ∉ P := fun hp => hU hx (Or.inr hp)
  have hPE {x : Ω} (hx : x ∈ P) : x ∉ exterior I P := fun he => he (Or.inr hx)
  by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U <;>
    by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P <;>
    by_cases hxE : x ∈ exterior I P <;> by_cases hyE : y ∈ exterior I P
  all_goals first
    | exact False.elim (hUnP hxU hxP)
    | exact False.elim (hUnP hyU hyP)
    | exact False.elim (hxE (hU hxU))
    | exact False.elim (hyE (hU hyU))
    | exact False.elim (hPE hxP hxE)
    | exact False.elim (hPE hyP hyE)
    | skip
  all_goals
    have hmin : min (Y x y) 0 = Y x y - max (Y x y) 0 := by
      linarith only [min_add_max (Y x y) 0]
    simp [charge, filled, clipped, MarkedMissingEdit.active, costLinear, costQuadratic,
      Set.indicator, hxU, hyU, hxP, hyP, hxE, hyE, hYsym y x, hmin]
    ring

omit [MeasurableSpace Ω] in
theorem densityLinear_bound (A : Ω → Ω → Bool) (P U : Set Ω) (x y : Ω) :
    ‖densityLinear A P U x y‖ ≤ 1 := by
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ P <;>
    cases ha : A x y <;> norm_num [densityLinear, Set.indicator, hx, hy, ha]

omit [MeasurableSpace Ω] in
theorem costLinear_bound (Y : Ω → Ω → ℝ) (I P U : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω) :
    ‖costLinear Y I P U x y‖ ≤ 2 * B := by
  have hmax : ‖max (Y x y) 0‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hY _ _)) hB
  unfold costLinear
  refine (norm_add_le _ _).trans ?_
  have hfirst : ‖(U ×ˢ P).indicator (Function.uncurry Y) (x, y)‖ ≤ B := by
    by_cases h : (x, y) ∈ U ×ˢ P
    · simpa only [Set.indicator_of_mem h, Function.uncurry_apply_pair] using hY x y
    · simp only [Set.indicator_of_notMem h, norm_zero]
      exact hB
  have hsecond : ‖(U ×ˢ exterior I P).indicator (fun p => max (Y p.1 p.2) 0) (x, y)‖ ≤ B := by
    by_cases h : (x, y) ∈ U ×ˢ exterior I P
    · simpa only [Set.indicator_of_mem h] using hmax
    · simp only [Set.indicator_of_notMem h, norm_zero]
      exact hB
  linarith only [hfirst, hsecond]

omit [MeasurableSpace Ω] in
theorem costQuadratic_bound (Y : Ω → Ω → ℝ) (U : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω) :
    ‖costQuadratic Y U x y‖ ≤ B := by
  have hmax : ‖max (Y x y) 0‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hY _ _)) hB
  by_cases h : (x, y) ∈ U ×ˢ U
  · simp only [costQuadratic, Set.indicator_of_mem h, norm_div, Real.norm_ofNat]
    linarith only [hmax, hB]
  · simp [costQuadratic, Set.indicator, h, hB]

/-- The marked body/remainder clipping cost retains its full quadratic
marking probability under the same original probability law. -/
theorem objective_marked (alpha : unitInterval) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hY : Measurable (Function.uncurry Y))
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hUmeas : MeasurableSet U)
    (hU : U ⊆ exterior I P) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure μ alpha) (charge Y I P U) =
      FiniteCappedSamplingCost.physicalObjective μ Y -
        (alpha : ℝ) * (∫ p : Ω × Ω, costLinear Y I P U p.1 p.2 ∂μ.prod μ) +
        (alpha : ℝ) ^ 2 * (∫ p : Ω × Ω, costQuadratic Y U p.1 p.2 ∂μ.prod μ) := by
  have hi : Integrable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound _ _))
  have hlin : Integrable (fun p : Ω × Ω => costLinear Y I P U p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (measurable_costLinear Y I P U hY hI hP hUmeas).aestronglyMeasurable
      (2 * B) (Eventually.of_forall (fun p => costLinear_bound Y I P U B hB hbound _ _))
  have hquad : Integrable (fun p : Ω × Ω => costQuadratic Y U p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (measurable_costQuadratic Y U hY hUmeas).aestronglyMeasurable
      B (Eventually.of_forall (fun p => costQuadratic_bound Y U B hB hbound _ _))
  have hlinSwap : Integrable (fun p : Ω × Ω => costLinear Y I P U p.2 p.1) (μ.prod μ) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integrable_comp_of_integrable hlin
  have hswap : (∫ p : Ω × Ω, costLinear Y I P U p.2 p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, costLinear Y I P U p.1 p.2 ∂μ.prod μ :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integral_comp
      (MeasurableEquiv.prodComm (α := Ω) (β := Ω)).measurableEmbedding
      (fun p : Ω × Ω => costLinear Y I P U p.1 p.2)
  unfold FiniteCappedSamplingCost.physicalObjective
  rw [integral_marked alpha _ (measurable_charge Y I P U hY hI hP hUmeas) B
    (charge_bound Y I P U B hB hbound)]
  simp_rw [objective_coins Y I P U hU hYsym]
  have htotal := integral_add (hi.sub ((hlin.add hlinSwap).const_mul (alpha : ℝ)))
    ((hquad.const_mul 2).const_mul ((alpha : ℝ) ^ 2))
  simp only [Pi.add_apply, Pi.sub_apply] at htotal
  have hsub := integral_sub hi ((hlin.add hlinSwap).const_mul (alpha : ℝ))
  have hadd := integral_add hlin hlinSwap
  simp only [Pi.add_apply] at hsub hadd
  rw [htotal, hsub, integral_const_mul, hadd, integral_const_mul, integral_const_mul, hswap]
  ring

/-- Filling original U-P nonedges is affine in the marking probability;
all original old-law weights remain in this exact moment formula. -/
theorem density_marked (alpha : unitInterval) (A : Ω → Ω → Bool) (P U : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hP : MeasurableSet P) (hU : MeasurableSet U)
    (hdis : Disjoint U P) (hAsym : ∀ x y, A x y = A y x) :
    FiniteCappedSamplingCost.physicalDensity (CappedModel.universalMeasure μ alpha) (adjacency A P U) =
      FiniteCappedSamplingCost.physicalDensity μ A +
        (alpha : ℝ) * (∫ p : Ω × Ω, densityLinear A P U p.1 p.2 ∂μ.prod μ) := by
  let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  have hGmeas : Measurable G :=
    measurable_const.ite (measurableSet_eq_fun hA measurable_const) measurable_const
  have hG : Integrable G (μ.prod μ) := Integrable.of_bound hGmeas.aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by cases ha : A p.1 p.2 <;> norm_num [G, ha]))
  have hlin : Integrable (fun p : Ω × Ω => densityLinear A P U p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (measurable_densityLinear A P U hA hP hU).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => densityLinear_bound A P U _ _))
  have hlinSwap : Integrable (fun p : Ω × Ω => densityLinear A P U p.2 p.1) (μ.prod μ) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integrable_comp_of_integrable hlin
  have hswap : (∫ p : Ω × Ω, densityLinear A P U p.2 p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, densityLinear A P U p.1 p.2 ∂μ.prod μ :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integral_comp
      (MeasurableEquiv.prodComm (α := Ω) (β := Ω)).measurableEmbedding
      (fun p : Ω × Ω => densityLinear A P U p.1 p.2)
  have hAdj := measurable_adjacency A P U hA hP hU
  have hAdjReal : Measurable (fun p : (Ω × Bool) × (Ω × Bool) =>
      if adjacency A P U p.1 p.2 = true then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hAdj measurable_const) measurable_const
  unfold FiniteCappedSamplingCost.physicalDensity
  rw [integral_marked alpha (fun x y => if adjacency A P U x y = true then (1 : ℝ) else 0) hAdjReal 1
    (fun x y => by cases ha : adjacency A P U x y <;> norm_num [ha])]
  simp_rw [density_coins A P U hdis hAsym]
  have he := integral_add hG ((hlin.add hlinSwap).const_mul (alpha : ℝ))
  simp only [Pi.add_apply, G] at he
  rw [he, integral_const_mul, integral_add hlin hlinSwap, hswap]
  ring

end Erdos1017.DominantAtomMarkedEdit
