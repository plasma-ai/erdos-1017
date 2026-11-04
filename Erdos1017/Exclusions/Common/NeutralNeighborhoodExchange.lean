module

public import Erdos1017.Exclusions.Common.RectangleTransfer
public import Erdos1017.SelectedModel.Capped.CappedScalarModel
public import Erdos1017.Models.Capped.CappedMaskedDeletion

/-!
# Neutral exchange of neighborhood rectangles

Inserting recipient-to-exterior edges while deleting the donor-to-exterior
rectangle gives a fully feasible same-law model, and when the two rectangles
have equal mass the exchange is neutral in density and objective, with row
changes supported only on the donor and recipient cells.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Erdos1017.FiniteArity Erdos1017.NeighborhoodExchange
open scoped Classical

namespace Erdos1017.CappedModel.NeighborhoodExchange

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Construct the actual same-law colored exchange: insert canceling
recipient/exterior edges and delete the donor/exterior rectangle. Every
finite clique constraint and both literal moments are derived. Equal
masses and original rectangle identities are used only in the subsequent
neutrality calculation, not as an edited feasibility premise. -/
theorem exists_model
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (hYsym : ∀ x y, Y x y = Y y x) (hYbox : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1)
    (hYzero : ∀ x y, A x y = false → Y x y = 0)
    (s : Ω → ℝ) (hs : Measurable s) (hsbox : ∀ x, s x ∈ Icc (0 : ℝ) 1)
    (R J E K : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E) (hK : MeasurableSet K)
    (hRJ : Disjoint R J) (hRE : Disjoint R E) (hJE : Disjoint J E)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ E → Y p.1 p.2 = s p.2)
    (hfull : ∀ n, FeasibleOrder μ A Y n) :
    ∃ V : Model Ω μ, FullFeasible V ∧
      (∀ p, V.moment CappedColor.adjacency p =
        if extensionPair K E p.1 p.2 then 0 else
          if extensionAdjacency A J E p.1 p.2 = true then 1 else 0) ∧
      ∀ p, V.moment CappedColor.charge p =
        if extensionPair K E p.1 p.2 then 0 else extensionCharge Y s J E p.1 p.2 := by
  classical
  let P : Ω × Ω → unitInterval := fun p =>
    if extensionAdjacency A J E p.1 p.2 = true then 1 else 0
  let Z : Ω × Ω → Icc (-3 : ℝ) 1 := fun p =>
    ⟨extensionCharge Y s J E p.1 p.2, extensionCharge_mem_Icc Y s hYbox hsbox J E hJE p.1 p.2⟩
  have hP : Measurable P := measurable_const.ite
    ((measurable_extensionAdjacency A hA J E hJ hE) (measurableSet_singleton true)) measurable_const
  have hZ : Measurable Z := (measurable_extensionCharge Y hY s hs J E hJ hE).subtype_mk
  have hPsym : ∀ᵐ p ∂μ.prod μ, P p.swap = P p := Eventually.of_forall (fun p => by
    simp only [P, Prod.swap, extensionAdjacency_symm A hAsym J E p.2 p.1])
  have hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p := Eventually.of_forall (fun p =>
    Subtype.ext (extensionCharge_symm Y s hYsym J E p.2 p.1))
  let U := ScalarModel.model P Z hP hZ hPsym hZsym
  have hU : FullFeasible U := by
    apply ScalarModel.fullFeasible_model P Z hP hZ hPsym hZsym (extensionAdjacency A J E)
    · exact Eventually.of_forall (fun p hp => by simp [P, hp])
    · intro n _
      exact feasibleOrder_extension_of_single_root μ A Y s hYsym R J E hRJ hRE hJE
        hroot hbody hstar (Eventually.of_forall (fun x _ => (hsbox x).1)) hfull n
  have hUA (p : Ω × Ω) : U.moment CappedColor.adjacency p =
      if extensionAdjacency A J E p.1 p.2 = true then 1 else 0 := by
    rw [ScalarModel.adjacency_moment]
    dsimp only [P]
    split_ifs <;> rfl
  have hUY (p : Ω × Ω) : U.moment CappedColor.charge p = extensionCharge Y s J E p.1 p.2 := by
    rw [ScalarModel.charge_moment]
    by_cases hp : extensionAdjacency A J E p.1 p.2 = true
    · simp [P, Z, hp]
    · have hz := extensionCharge_zero_of_nonedge A Y s hYzero J E p.1 p.2
        (Bool.eq_false_iff.mpr hp)
      simp only [Z, hz, mul_zero]
  let T := {p : Ω × Ω | extensionPair K E p.1 p.2}
  have hT : MeasurableSet T := measurableSet_extensionPair K E hK hE
  have hTsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ T ↔ p ∈ T := Eventually.of_forall (fun p => by
    simp only [T, extensionPair, mem_ofPred_eq, Prod.swap]
    exact or_comm)
  let V := maskedThin U 1 T hT hTsym
  refine ⟨V, (fun r => feasible_maskedThin U (hU r) 1 T hT hTsym), ?_, ?_⟩
  · intro p
    rw [moment_maskedThin U 1 T hT hTsym p CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable
      CappedColor.adjacency_absent 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2)]
    simp [hUA, T]
  · intro p
    rw [moment_maskedThin U 1 T hT hTsym p CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable
      CappedColor.charge_absent 3 (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩)]
    simp [hUY, T]

omit [MeasurableSpace Ω] in
/-- The literal edited graph changes by two opposite symmetric rectangles.
The old absent/present rectangle facts rule out overlap themselves. -/
theorem adjacency_exchange_formula
    (A : Ω → Ω → Bool) (J K E : Set Ω) (hJE : Disjoint J E) (hKE : Disjoint K E)
    (x y : Ω)
    (hJ : extensionPair J E x y → A x y = false)
    (hK : extensionPair K E x y → A x y = true) :
    (if extensionPair K E x y then (0 : ℝ) else
      if extensionAdjacency A J E x y = true then 1 else 0) =
    (if A x y = true then 1 else 0) + rectangle J E (fun _ => 1) x y -
      rectangle K E (fun _ => 1) x y := by
  rw [rectangle_one_eq_ite J E hJE, rectangle_one_eq_ite K E hKE]
  by_cases hJp : extensionPair J E x y
  · by_cases hKp : extensionPair K E x y
    · have := (hJ hJp).symm.trans (hK hKp)
      contradiction
    · simp [extensionAdjacency, hJp, hKp, hJ hJp]
  · by_cases hKp : extensionPair K E x y
    · simp [hJp, hKp, hK hKp]
    · simp [extensionAdjacency, hJp, hKp]

omit [MeasurableSpace Ω] in
/-- The literal edited charge transfers exactly the donor's canceled
exterior row, with its sign retained. -/
theorem charge_exchange_formula
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (s : Ω → ℝ)
    (J K E : Set Ω) (hJE : Disjoint J E) (hKE : Disjoint K E)
    (x y : Ω) (hzero : A x y = false → Y x y = 0)
    (hJ : extensionPair J E x y → A x y = false)
    (hK : extensionPair K E x y → A x y = true ∧ Y x y = -(E.indicator s x + E.indicator s y)) :
    (if extensionPair K E x y then (0 : ℝ) else extensionCharge Y s J E x y) =
      Y x y - rectangle J E s x y + rectangle K E s x y := by
  rw [rectangle_eq_ite J E hJE, rectangle_eq_ite K E hKE]
  by_cases hJp : extensionPair J E x y
  · by_cases hKp : extensionPair K E x y
    · have := (hJ hJp).symm.trans (hK hKp).1
      contradiction
    · simp [extensionCharge, hJp, hKp, hzero (hJ hJp)]
  · by_cases hKp : extensionPair K E x y
    · simp [hJp, hKp, (hK hKp).2]
    · simp [extensionCharge, hJp, hKp]

/-- Equal old masses make an actual rectangle exchange neutral for the
original objective or density moment. The row function may be signed. -/
theorem integral_eq_of_equal_mass_rectangles
    (F H : Ω × Ω → ℝ) (hF : Integrable F (μ.prod μ))
    (J K E : Set Ω) (hJ : MeasurableSet J) (hK : MeasurableSet K) (hE : MeasurableSet E)
    (s : Ω → ℝ) (hs : Integrable s μ) (hmass : μ.real J = μ.real K)
    (hH : ∀ᵐ p ∂μ.prod μ, H p = F p + rectangle J E s p.1 p.2 - rectangle K E s p.1 p.2) :
    (∫ p, H p ∂μ.prod μ) = ∫ p, F p ∂μ.prod μ := by
  rw [integral_congr_ae hH, integral_sub (f := fun p => F p + rectangle J E s p.1 p.2)
    (g := fun p => rectangle K E s p.1 p.2) (hF.add (integrable_rectangle J E hJ hE s hs))
    (integrable_rectangle K E hK hE s hs), integral_add (f := F) (g := fun p => rectangle J E s p.1 p.2)
      hF (integrable_rectangle J E hJ hE s hs),
    integral_rectangle J E hJ hE s hs, integral_rectangle K E hK hE s hs, hmass]
  ring

/-- After an equal-mass transfer, the complete row change is supported
only on the donor and recipient cells. Exterior old rows are unchanged. -/
theorem row_eq_of_equal_mass_rectangles
    (F H : Ω × Ω → ℝ) (hF : Integrable F (μ.prod μ))
    (J K E : Set Ω) (hJ : MeasurableSet J) (hK : MeasurableSet K) (hE : MeasurableSet E)
    (s : Ω → ℝ) (hs : Integrable s μ) (hmass : μ.real J = μ.real K)
    (hH : ∀ᵐ p ∂μ.prod μ, H p = F p + rectangle J E s p.1 p.2 - rectangle K E s p.1 p.2) :
    ∀ᵐ x ∂μ, (∫ y, H (x, y) ∂μ) = (∫ y, F (x, y) ∂μ) +
      (J.indicator (fun _ => 1) x - K.indicator (fun _ => 1) x) * (∫ y in E, s y ∂μ) := by
  have hJint := integrable_rectangle J E hJ hE s hs
  have hKint := integrable_rectangle K E hK hE s hs
  filter_upwards [Measure.ae_ae_of_ae_prod hH, hF.prod_right_ae,
    hJint.prod_right_ae, hKint.prod_right_ae] with x hx hFx hJx hKx
  rw [integral_congr_ae hx, integral_sub (f := fun y => F (x, y) + rectangle J E s x y)
    (g := fun y => rectangle K E s x y) (hFx.add hJx) hKx,
    integral_add (f := fun y => F (x, y)) (g := fun y => rectangle J E s x y) hFx hJx,
    integral_rectangle_row J E hJ hE s hs, integral_rectangle_row K E hK hE s hs, hmass]
  ring

/-- The actual equal-mass exchange is fully feasible and exactly neutral
in density and objective. Its two row changes are derived on the original
law, rather than imposed as a stationarity or optimality certificate. -/
theorem exists_neutral_model
    (W : Model Ω μ)
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (hYsym : ∀ x y, Y x y = Y y x) (hYbox : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1)
    (hYzero : ∀ x y, A x y = false → Y x y = 0)
    (hWmom : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if A p.1 p.2 = true then 1 else 0) ∧ W.moment CappedColor.charge p = Y p.1 p.2)
    (s : Ω → ℝ) (hs : Measurable s) (hsbox : ∀ x, s x ∈ Icc (0 : ℝ) 1)
    (R J E K : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E) (hK : MeasurableSet K)
    (hRJ : Disjoint R J) (hRE : Disjoint R E) (hJE : Disjoint J E) (hKE : Disjoint K E)
    (hmass : μ.real J = μ.real K)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ E → Y p.1 p.2 = s p.2)
    (hJrect : ∀ᵐ p ∂μ.prod μ, extensionPair J E p.1 p.2 → A p.1 p.2 = false)
    (hKrect : ∀ᵐ p ∂μ.prod μ, extensionPair K E p.1 p.2 →
      A p.1 p.2 = true ∧ Y p.1 p.2 = -(E.indicator s p.1 + E.indicator s p.2))
    (hfull : ∀ n, FeasibleOrder μ A Y n) :
    ∃ V : Model Ω μ, FullFeasible V ∧ density V = density W ∧ objective V = objective W ∧
      ∀ᵐ x ∂μ,
        (∫ y, adjacencyKernel V x y ∂μ) = (∫ y, adjacencyKernel W x y ∂μ) +
          (J.indicator (fun _ => 1) x - K.indicator (fun _ => 1) x) * μ.real E ∧
        (∫ y, chargeKernel V x y ∂μ) = (∫ y, chargeKernel W x y ∂μ) -
          (J.indicator (fun _ => 1) x - K.indicator (fun _ => 1) x) * (∫ y in E, s y ∂μ) := by
  obtain ⟨V, hV, hVA, hVY⟩ := exists_model A hA hAsym Y hY hYsym hYbox hYzero
    s hs hsbox R J E K hJ hE hK hRJ hRE hJE hroot hbody hstar hfull
  let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  have hG : Integrable G (μ.prod μ) := Integrable.of_bound
    (measurable_const.ite (hA (measurableSet_singleton true)) measurable_const).aestronglyMeasurable
    1 (Eventually.of_forall (fun p => by dsimp only [G]; split_ifs <;> norm_num))
  have hYint : Integrable (Function.uncurry Y) (μ.prod μ) := Integrable.of_bound
    hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(hYbox p.1 p.2).1, (hYbox p.1 p.2).2.trans (by norm_num)⟩))
  have hsint : Integrable s μ := Integrable.of_bound hs.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hsbox x).1]
      exact (hsbox x).2))
  have hGA : ∀ᵐ p ∂μ.prod μ, V.moment CappedColor.adjacency p =
      G p + rectangle J E (fun _ => 1) p.1 p.2 - rectangle K E (fun _ => 1) p.1 p.2 := by
    filter_upwards [hJrect, hKrect] with p hj hk
    rw [hVA]
    exact adjacency_exchange_formula A J K E hJE hKE p.1 p.2 hj (fun h => (hk h).1)
  have hYC : ∀ᵐ p ∂μ.prod μ, V.moment CappedColor.charge p =
      Y p.1 p.2 + rectangle K E s p.1 p.2 - rectangle J E s p.1 p.2 := by
    filter_upwards [hJrect, hKrect] with p hj hk
    rw [hVY, charge_exchange_formula A Y s J K E hJE hKE p.1 p.2 (hYzero p.1 p.2) hj hk]
    ring
  have hGint := integral_eq_of_equal_mass_rectangles G _ hG J K E hJ hK hE
    (fun _ => 1) (integrable_const 1) hmass hGA
  have hCint := integral_eq_of_equal_mass_rectangles (Function.uncurry Y) _ hYint K J E hK hJ hE
    s hsint hmass.symm hYC
  have hGrows := row_eq_of_equal_mass_rectangles G _ hG J K E hJ hK hE
    (fun _ => 1) (integrable_const 1) hmass hGA
  have hCrows := row_eq_of_equal_mass_rectangles (Function.uncurry Y) _ hYint K J E hK hJ hE
    s hsint hmass.symm hYC
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · unfold density
    rw [hGint, integral_congr_ae (hWmom.mono (fun _ h => h.1))]
  · unfold objective
    rw [hCint, integral_congr_ae (hWmom.mono (fun _ h => h.2))]
    rfl
  · filter_upwards [hGrows, hCrows, Measure.ae_ae_of_ae_prod hWmom] with x hg hc hw
    have hgOld := integral_congr_ae (hw.mono (fun _ h => h.1))
    have hcOld := integral_congr_ae (hw.mono (fun _ h => h.2))
    constructor
    · change (∫ y, V.moment CappedColor.adjacency (x, y) ∂μ) = _
      rw [hg]
      change _ = (∫ y, W.moment CappedColor.adjacency (x, y) ∂μ) + _
      rw [hgOld]
      simp only [G, setIntegral_const, smul_eq_mul, mul_one]
    · change (∫ y, V.moment CappedColor.charge (x, y) ∂μ) = _
      rw [hc]
      change _ = (∫ y, W.moment CappedColor.charge (x, y) ∂μ) - _
      rw [hcOld]
      dsimp only [Function.uncurry]
      ring

end Erdos1017.CappedModel.NeighborhoodExchange
