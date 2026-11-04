module

public import Erdos1017.Exclusions.Common.Physical.IndependentPositiveCoverCompletion
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.SelectedModel.Capped.CappedScalarModel
public import Erdos1017.Models.Selection.FullEditComparison
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# No missing cross edges on an independent positive cover

At a strict-gap full optimum, an independent set covering every positive charge
has no missing cross edges, by a feasible Bernoulli insertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An independent set covering every positive charge has no missing cross
edges at an actual strict-gap full optimum. The feasible Bernoulli insertion
and its exact-density correction are constructed from the original model. -/
theorem FullStationaryClass.no_missing_cross_on_independent_positive_cover
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hdhalf : d < 1 / 2) (hgap : benchmark d < c) (H : Set Ω) (hH : MeasurableSet H)
    (hind : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ H → p.2 ∈ H → adjacencyKernel W p.1 p.2 = 0)
    (hcover : ∀ᵐ p ∂μ.prod μ,
      p.1 ∉ H → p.2 ∉ H → chargeKernel W p.1 p.2 ≤ 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∉ H → adjacencyKernel W p.1 p.2 = 1 := by
  classical
  have hs := hW.strict_gap_structure_of_density_lt_half hdhalf hgap
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hAsym : ∀ x y, A x y = A y x := PhysicalRepresentative.adjacency_symm W m
  have hYsym : ∀ x y, Y x y = Y y x := PhysicalRepresentative.charge_symm W m
  have hAeq := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hYeq := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  change ∀ᵐ p ∂μ.prod μ,
    W.moment CappedColor.adjacency p = (if A p.1 p.2 = true then 1 else 0) at hAeq
  change ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = chargeKernel W p.1 p.2 at hYeq
  have hindA : ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∈ H → A p.1 p.2 = false := by
    filter_upwards [hind, hAeq] with p hp he hx hy
    have hz := hp hx hy
    change W.moment CappedColor.adjacency p = 0 at hz
    change W.moment CappedColor.adjacency p = (if A p.1 p.2 = true then 1 else 0) at he
    exact Bool.eq_false_iff.mpr (fun ha => by simp [ha, hz] at he)
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ H → p.2 ∉ H → Y p.1 p.2 ≤ 0 := by
    filter_upwards [hcover, hYeq] with p hp he hx hy
    rw [he]
    exact hp hx hy
  have hzero (x y : Ω) (ha : A x y = false) : Y x y = 0 :=
    PhysicalRepresentative.charge_zero_of_nonedge W m x y ha
  have htests := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  let G := FiniteArity.completeCrossAdjacency A H
  have hG : Measurable (Function.uncurry G) := by
    apply measurable_const.ite _ hA
    exact ((hH.preimage measurable_fst).inter (hH.compl.preimage measurable_snd)).union
      ((hH.preimage measurable_snd).inter (hH.compl.preimage measurable_fst))
  have hGsym (x y : Ω) : G x y = G y x := by
    dsimp only [G, FiniteArity.completeCrossAdjacency]
    rw [hAsym]
    congr 1
    exact propext (by tauto)
  have hAG (x y : Ω) (ha : A x y = true) : G x y = true := by
    dsimp only [G, FiniteArity.completeCrossAdjacency]
    split_ifs <;> simp [ha]
  have hcomplete (n : ℕ) : FiniteArity.FeasibleOrder μ G Y n :=
    FiniteArity.feasibleOrder_complete_cross_of_independent_positive_cover μ A Y hAsym hYsym H
      hindA hbody (Eventually.of_forall (fun p => hzero p.1 p.2)) htests n
  let P (t : unitInterval) (p : Ω × Ω) : unitInterval :=
    if A p.1 p.2 = true then 1 else if G p.1 p.2 = true then t else 0
  let Z (p : Ω × Ω) : Icc (-3 : ℝ) 1 :=
    ⟨Y p.1 p.2, PhysicalRepresentative.charge_mem_Icc W m p.1 p.2⟩
  have hP (t : unitInterval) : Measurable (P t) :=
    measurable_const.ite (hA (measurableSet_singleton true))
      (measurable_const.ite (hG (measurableSet_singleton true)) measurable_const)
  have hZ : Measurable Z := hY.subtype_mk
  have hPsym (t : unitInterval) : ∀ᵐ p ∂μ.prod μ, P t p.swap = P t p := by
    exact Eventually.of_forall (fun p => by dsimp only [P, Prod.swap]; rw [hAsym, hGsym])
  have hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p :=
    Eventually.of_forall (fun p => Subtype.ext (hYsym p.2 p.1))
  let V (t : unitInterval) := ScalarModel.model (P t) Z (hP t) hZ (hPsym t) hZsym
  have hadj (t : unitInterval) (p : Ω × Ω) :
      (V t).moment CappedColor.adjacency p = (P t p : ℝ) :=
    ScalarModel.adjacency_moment (P t) Z (hP t) hZ (hPsym t) hZsym p
  have hcharge (t : unitInterval) (p : Ω × Ω) :
      (V t).moment CappedColor.charge p = Y p.1 p.2 := by
    rw [ScalarModel.charge_moment]
    by_cases ha : A p.1 p.2 = true
    · simp [P, Z, ha]
    · have hz := hzero p.1 p.2 (Bool.eq_false_iff.mpr ha)
      simp [Z, hz]
  have hfull (t : unitInterval) : FullFeasible (V t) := by
    apply ScalarModel.fullFeasible_model (P t) Z (hP t) hZ (hPsym t) hZsym G
    · exact Eventually.of_forall (fun p hp => by
        have ha : A p.1 p.2 ≠ true := fun ha => by rw [hAG _ _ ha] at hp; contradiction
        simp [P, ha, hp])
    · exact fun n _ => hcomplete n
  have hadj0 (p : Ω × Ω) :
      (V 0).moment CappedColor.adjacency p = if A p.1 p.2 = true then 1 else 0 := by
    rw [hadj]
    by_cases ha : A p.1 p.2 = true <;> simp [P, ha]
  have hadj1 (p : Ω × Ω) :
      (V 1).moment CappedColor.adjacency p = if G p.1 p.2 = true then 1 else 0 := by
    rw [hadj]
    by_cases ha : A p.1 p.2 = true
    · simp [P, ha, hAG _ _ ha]
    · by_cases hg : G p.1 p.2 = true <;> simp [P, ha, hg]
  let E : AffineEdit (V 0) := {
    model := V
    feasible := fun r _ t => hfull t r
    adjacency := by
      intro t p
      rw [hadj, hadj0, hadj1]
      by_cases ha : A p.1 p.2 = true
      · simp [P, ha, hAG _ _ ha]
      · by_cases hg : G p.1 p.2 = true <;> simp [P, ha, hg]
    charge := by
      intro t p
      simp only [hcharge, sub_self, mul_zero, add_zero] }
  have hbaseA : ∀ᵐ p ∂μ.prod μ,
      (V 0).moment CappedColor.adjacency p = W.moment CappedColor.adjacency p := by
    filter_upwards [hAeq] with p hp
    exact (hadj0 p).trans hp.symm
  have hbaseY : ∀ᵐ p ∂μ.prod μ,
      (V 0).moment CappedColor.charge p = W.moment CappedColor.charge p := by
    filter_upwards [hYeq] with p hp
    exact (hcharge 0 p).trans hp
  have hAop : adjacencyOperator (V 0) = adjacencyOperator W := by
    apply ContinuousLinearMap.ext
    intro f
    apply ext_inner_right ℝ
    intro g
    simp only [adjacencyOperator, KernelOperator.operator_inner]
    apply integral_congr_ae
    filter_upwards [hbaseA] with p hp
    rw [adjacencyKernel, adjacencyKernel, hp]
  have hYop : chargeOperator (V 0) = chargeOperator W := by
    apply ContinuousLinearMap.ext
    intro f
    apply ext_inner_right ℝ
    intro g
    simp only [chargeOperator, KernelOperator.operator_inner]
    apply integral_congr_ae
    filter_upwards [hbaseY] with p hp
    rw [chargeKernel, chargeKernel, hp]
  have hd0 : density (V 0) = density W := by
    unfold density
    rw [integral_congr_ae hbaseA]
  have hc0 : objective (V 0) = objective W := by
    unfold objective
    rw [integral_congr_ae hbaseY]
  have hopt : objective (V 0) = FractionalGraph.densityLimit (density (V 0)) := by
    rw [hc0, hd0, hW.density_eq, hW.objective_eq]
    exact hW.optimal
  have hm : Variation.weightFirstVariation (chargeOperator (V 0)) =
      m • Variation.weightFirstVariation (adjacencyOperator (V 0)) := by
    rw [hYop, hAop]
    exact firstVariation_identity_of_shifted_zero W m
      (shiftedFirstVariation_zero_of_stationary W m _ hW.stationary)
  have hsign := full_affine_edit_sign (V 0) (hfull 0) hopt E m hm (hAop ▸ hs.regular)
  have hc1 : objective (V 1) = objective (V 0) := by
    unfold objective
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => (hcharge 1 p).trans (hcharge 0 p).symm)
  let K (p : Ω × Ω) : ℝ :=
    (if G p.1 p.2 = true then 1 else 0) - (if A p.1 p.2 = true then 1 else 0)
  have hKmeas : Measurable K :=
    (measurable_const.ite (hG (measurableSet_singleton true)) measurable_const).sub
      (measurable_const.ite (hA (measurableSet_singleton true)) measurable_const)
  have hKbounds (p : Ω × Ω) : K p ∈ Icc (0 : ℝ) 1 := by
    dsimp only [K]
    by_cases ha : A p.1 p.2 = true
    · simp [ha, hAG _ _ ha]
    · by_cases hg : G p.1 p.2 = true <;> simp [ha, hg]
  have hKi : Integrable K (μ.prod μ) := by
    apply Integrable.of_bound hKmeas.aestronglyMeasurable 1
    exact Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hKbounds p).1]
      exact (hKbounds p).2)
  have hden : density (V 1) - density (V 0) = (∫ p, K p ∂μ.prod μ) / 2 := by
    unfold density
    rw [← sub_div, ← integral_sub
      (integrable_bounded_moment (V 1) CappedColor.adjacency
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (by
          intro z
          rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem z).1]
          exact (CappedColor.adjacency_mem z).2))
      (integrable_bounded_moment (V 0) CappedColor.adjacency
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (by
          intro z
          rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem z).1]
          exact (CappedColor.adjacency_mem z).2))]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      change (V 1).moment CappedColor.adjacency p -
        (V 0).moment CappedColor.adjacency p = K p
      rw [hadj1, hadj0])
  change objective (V 1) - objective (V 0) - m * (density (V 1) - density (V 0)) ≤ 0 at hsign
  rw [hc1, sub_self, zero_sub, hden] at hsign
  have hKzero : (∫ p, K p ∂μ.prod μ) = 0 := by
    have hnonneg := integral_nonneg (μ := μ.prod μ) (fun p => (hKbounds p).1)
    nlinarith [hs.multiplier_neg]
  have hKae : ∀ᵐ p ∂μ.prod μ, K p = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => (hKbounds p).1) hKi).mp hKzero
  filter_upwards [hKae, hAeq] with p hp he hx hy
  have hg : G p.1 p.2 = true := by
    simp [G, FiniteArity.completeCrossAdjacency, hx, hy]
  have ha : A p.1 p.2 = true := by
    by_contra hnot
    simp [K, hg, hnot] at hp
  change W.moment CappedColor.adjacency p = 1
  simpa only [ha, ite_true] using he

end Erdos1017.CappedModel
