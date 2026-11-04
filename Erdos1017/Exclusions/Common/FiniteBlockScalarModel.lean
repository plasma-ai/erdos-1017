module

public import Erdos1017.Models.Capped.CappedAveraging
public import Erdos1017.SelectedModel.Capped.CappedScalarModel
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Scalar models from finite block charges

Finite block charges in the compact color box give a fully feasible model on the
same carrier with the given graph and charge moments
(`exists_boxed_finite_block_model`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual finite block charges in the compact color box give a fully
feasible same-carrier model with the literal graph and charge moments.
Conditional-charge determinism holds at every physical pair. -/
theorem exists_boxed_finite_block_model (q : Ω → ι) (hq : Measurable q)
    (G : ι → ι → Bool) (hGsym : ∀ i j, G i j = G j i)
    (y : ι → ι → ℝ) (hysym : ∀ i j, y i j = y j i)
    (hyzero : ∀ i j, G i j = false → y i j = 0)
    (hybox : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ
      (fun x z => G (q x) (q z)) (fun x z => y (q x) (q z)) n) :
    ∃ V : Model Ω μ, FullFeasible V ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p = (if G (q p.1) (q p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = y (q p.1) (q p.2)) ∧
      density V = FiniteCappedSamplingCost.physicalDensity μ (fun x z => G (q x) (q z)) ∧
      objective V = FiniteCappedSamplingCost.physicalObjective μ (fun x z => y (q x) (q z)) ∧
      ∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  classical
  have hpair : Measurable (fun p : Ω × Ω => (q p.1, q p.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  have hG : Measurable (fun p : Ω × Ω => G (q p.1) (q p.2)) :=
    (measurable_of_countable (Function.uncurry G)).comp hpair
  have hy : Measurable (fun p : Ω × Ω => y (q p.1) (q p.2)) :=
    (measurable_of_countable (Function.uncurry y)).comp hpair
  let P (p : Ω × Ω) : unitInterval := if G (q p.1) (q p.2) = true then 1 else 0
  let Z (p : Ω × Ω) : Icc (-3 : ℝ) 1 := ⟨y (q p.1) (q p.2), hybox _ _⟩
  have hP : Measurable P :=
    measurable_const.ite (hG (measurableSet_singleton true)) measurable_const
  have hZ : Measurable Z := hy.subtype_mk
  have hPsym : ∀ᵐ p ∂μ.prod μ, P p.swap = P p :=
    Eventually.of_forall (fun p => by dsimp only [P, Prod.swap]; rw [hGsym])
  have hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p :=
    Eventually.of_forall (fun p => Subtype.ext (hysym _ _))
  let U := ScalarModel.model P Z hP hZ hPsym hZsym
  have hU : FullFeasible U := by
    apply ScalarModel.fullFeasible_model P Z hP hZ hPsym hZsym (fun x z => G (q x) (q z))
    · exact Eventually.of_forall (fun p hp => by simp [P, hp])
    · exact fun n _ => hfull n
  have hmom (p : Ω × Ω) :
      U.moment CappedColor.adjacency p = (if G (q p.1) (q p.2) = true then 1 else 0) ∧
      U.moment CappedColor.charge p = y (q p.1) (q p.2) := by
    constructor
    · rw [ScalarModel.adjacency_moment]
      by_cases hp : G (q p.1) (q p.2) = true <;> simp [P, hp]
    · rw [ScalarModel.charge_moment]
      by_cases hp : G (q p.1) (q p.2) = true
      · simp [P, Z, hp]
      · simp [P, Z, hp, hyzero _ _ (Bool.eq_false_iff.mpr hp)]
  refine ⟨averaged U, fun r => feasible_averaged U (hU r), ?_, ?_, ?_, ?_⟩
  · intro p
    exact ⟨(adjacency_moment_averaged U p).trans (hmom p).1,
      (charge_moment_averaged U p).trans (hmom p).2⟩
  · rw [density_averaged]
    unfold density FiniteCappedSamplingCost.physicalDensity
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).1))
  · rw [objective_averaged]
    unfold objective FiniteCappedSamplingCost.physicalObjective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2))
  · intro p
    rw [conditionalCharge_averaged]
    exact averaged_deterministic U p

end Erdos1017.CappedModel
