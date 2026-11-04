module

public import Erdos1017.Exclusions.Common.CountableConditionalAveraging
public import Erdos1017.Exclusions.Common.CappedBinaryRepresentative
public import Erdos1017.SelectedModel.Capped.CappedScalarModel

/-!
# Countable fiber averaging of a capped model

Averaging over countably many positive fibers constructs a fully feasible
colored model on the same original probability space, with the label graph as
its adjacency (`exists_full_conditional_average`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
  [Countable ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual countable positive-fiber averaging constructs a fully
feasible colored model on the same original probability space. Its
adjacency is the unchanged label graph, its charge is the literal original
conditional average, and its density and objective are exactly preserved. -/
theorem exists_full_conditional_average (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → ι) (hq : Measurable q) (hpos : ∀ i, 0 < μ (q ⁻¹' {i}))
    (H : ι → ι → Bool) (hHsym : ∀ i j, H i j = H j i)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if H (q p.1) (q p.2) = true then 1 else 0) :
    ∃ V : Model Ω μ, FullFeasible V ∧ density V = density W ∧ objective V = objective W ∧
      ∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p = (if H (q p.1) (q p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p =
          ConditionalAveraging.charge (μ := μ) q (chargeKernel W) p.1 p.2 := by
  let G := fun p : Ω × Ω => H (q p.1) (q p.2)
  have hG : Measurable G := by
    have hH : Measurable (Function.uncurry H) := measurable_of_countable _
    have hQ : Measurable (fun p : Ω × Ω => (q p.1, q p.2)) :=
      (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
    exact hH.comp hQ
  have hGsym (x y : Ω) : G (x, y) = G (y, x) := hHsym _ _
  let Y := fun x y => BinaryRepresentative.charge W G (x, y)
  have hY : Measurable (Function.uncurry Y) := BinaryRepresentative.measurable_charge W G hG
  have hYsym : ∀ x y, Y x y = Y y x := BinaryRepresentative.charge_symm W G hGsym
  have hYbox : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1 := fun x y =>
    BinaryRepresentative.charge_mem_Icc W G (x, y)
  have hYbound : ∀ x y, ‖Y x y‖ ≤ 3 := by
    intro x y
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(hYbox x y).1, (hYbox x y).2.trans (by norm_num)⟩
  have hYeq : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = chargeKernel W p.1 p.2 :=
    BinaryRepresentative.charge_ae_eq W G hsupport
  let P : Ω × Ω → unitInterval := fun p => if G p = true then 1 else 0
  have hP : Measurable P := Measurable.ite (hG (measurableSet_singleton true))
    measurable_const measurable_const
  have hPsym : ∀ᵐ p ∂μ.prod μ, P p.swap = P p := Eventually.of_forall (fun p => by
    dsimp only [P, Prod.swap]
    rw [hGsym p.2 p.1])
  let Z : Ω × Ω → Icc (-3 : ℝ) 1 := fun p =>
    ⟨ConditionalAveraging.charge (μ := μ) q Y p.1 p.2,
      ConditionalAveraging.charge_mem_Icc q hpos Y hY hYbox p.1 p.2⟩
  have hZ : Measurable Z := (ConditionalAveraging.measurable_charge q hq Y).subtype_mk
  have hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p := Eventually.of_forall (fun p =>
    Subtype.ext (ConditionalAveraging.charge_symm q Y hYsym p.2 p.1))
  let V := ScalarModel.model P Z hP hZ hPsym hZsym
  have hfull : FullFeasible V := by
    apply ScalarModel.fullFeasible_model P Z hP hZ hPsym hZsym
      (fun x y => H (q x) (q y))
    · exact Eventually.of_forall (fun p hp => by simp [P, G, hp])
    · intro n _
      exact ConditionalAveraging.full_scalar_tests q hq hpos H (fun x y => G (x, y)) Y hY 3 hYbound
        (Eventually.of_forall (fun _ => rfl)) (BinaryRepresentative.full_feasible W hW G hsupport) n
  have hcharge (p : Ω × Ω) : V.moment CappedColor.charge p =
      ConditionalAveraging.charge (μ := μ) q Y p.1 p.2 := by
    change (ScalarModel.model P Z hP hZ hPsym hZsym).moment CappedColor.charge p = _
    rw [ScalarModel.charge_moment]
    by_cases hp : G p = true
    · simp [P, hp, Z]
    · have hzero := ConditionalAveraging.charge_zero_of_nonedge (μ := μ) q hq H
        (fun x y => G (x, y)) Y (Eventually.of_forall (fun _ => rfl))
        (fun x y hx => BinaryRepresentative.charge_zero W G (x, y) hx) p.1 p.2
        (Bool.eq_false_iff.mpr hp)
      simpa [P, hp, Z] using hzero.symm
  have hadj (p : Ω × Ω) : V.moment CappedColor.adjacency p =
      if H (q p.1) (q p.2) = true then 1 else 0 := by
    change (ScalarModel.model P Z hP hZ hPsym hZsym).moment CappedColor.adjacency p = _
    rw [ScalarModel.adjacency_moment]
    dsimp only [P, G]
    split_ifs <;> rfl
  refine ⟨V, hfull, ?_, ?_, ?_⟩
  · unfold density
    congr 1
    apply integral_congr_ae
    exact hsupport.mono (fun p hp => (hadj p).trans hp.symm)
  · have hi : Integrable (Function.uncurry Y) (μ.prod μ) := Integrable.of_bound
      hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => hYbound p.1 p.2))
    unfold objective
    congr 1
    calc
      _ = ∫ p, ConditionalAveraging.charge (μ := μ) q Y p.1 p.2 ∂μ.prod μ :=
        integral_congr_ae (Eventually.of_forall hcharge)
      _ = ∫ p, Y p.1 p.2 ∂μ.prod μ := ConditionalAveraging.integral_charge q hq hpos Y hi
      _ = _ := integral_congr_ae hYeq
  · intro p
    exact ⟨hadj p, (hcharge p).trans (ConditionalAveraging.charge_congr_ae q Y (chargeKernel W) hYeq _ _)⟩

end Erdos1017.CappedModel
