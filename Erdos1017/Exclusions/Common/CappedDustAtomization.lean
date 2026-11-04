module

public import Erdos1017.Exclusions.Common.CappedBinaryRepresentative
public import Erdos1017.Exclusions.Common.MultipartiteDustAtomization
public import Erdos1017.SelectedModel.Capped.CappedScalarModel
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteClassMasses

/-!
# Atomization of a clique-dust set

This module turns a positive clique-dust set into one independent class on the
same latent probability law, giving a feasible bounded `model` whose charge
moment, objective and density are computed, so that atomization followed by the
own-profile bound yields the signed internal-charge comparison
(`objective_sub_internal_le_sq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.DustAtomization

open MultipartiteDustAtomization

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

local instance cappedAtomizationOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance cappedAtomizationNewOptionMeasurable : MeasurableSpace (Option (ι ⊕ Unit)) := ⊤

/-- The new binary multipartite support makes the displayed current dust
set one independent class. -/
def probability (labels : Ω → Option ι) (C : Set Ω) (p : Ω × Ω) : unitInterval :=
  if adjacency (atomizedLabels labels C) p.1 p.2 = true then 1 else 0

theorem measurable_probability (labels : Ω → Option ι) (hlabels : Measurable labels)
    (C : Set Ω) (hC : MeasurableSet C) : Measurable (probability labels C) :=
  Measurable.ite
    ((measurable_adjacency _ (measurable_atomizedLabels labels hlabels C hC))
      (measurableSet_singleton true)) measurable_const measurable_const

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem probability_symm (labels : Ω → Option ι) (C : Set Ω) (p : Ω × Ω) :
    probability labels C p.swap = probability labels C p := by
  simp only [probability, Prod.swap, adjacency_symm (atomizedLabels labels C) p.2 p.1]

/-- The actual averaged signed charge lies in the unchanged compact color box. -/
def charge (C : Set Ω) (hCpos : 0 < ν C) (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) : Icc (-3 : ℝ) 1 :=
  ⟨atomizedCharge (ν := ν) C Y p, atomizedCharge_mem_Icc C hCpos Y hY hbound p⟩

theorem measurable_charge (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1) :
    Measurable (charge C hCpos Y hY hbound) :=
  (measurable_atomizedCharge C hC hCpos Y hY).subtype_mk

theorem charge_symm (C : Set Ω) (hCpos : 0 < ν C) (Y : Ω × Ω → ℝ)
    (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (p : Ω × Ω) :
    charge C hCpos Y hY hbound p.swap = charge C hCpos Y hY hbound p :=
  Subtype.ext (atomizedCharge_symm C Y hsym p.2 p.1)

/-- Actual bounded atomization on the same current latent probability law.
Full feasibility is derived below from actual old tests. -/
def model (labels : Ω → Option ι) (hlabels : Measurable labels)
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) : Model Ω ν :=
  ScalarModel.model (probability labels C) (charge C hCpos Y hY hbound)
    (measurable_probability labels hlabels C hC) (measurable_charge C hC hCpos Y hY hbound)
    (Eventually.of_forall (probability_symm labels C))
    (Eventually.of_forall (charge_symm C hCpos Y hY hbound hsym))

section ScalarConstruction

variable (labels : Ω → Option ι) (hlabels : Measurable labels)
  (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
  (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hbound : ∀ p, Y p ∈ Icc (-3 : ℝ) 1)
  (hsym : ∀ x y, Y (x, y) = Y (y, x))

theorem adjacency_moment (p : Ω × Ω) :
    (model labels hlabels C hC hCpos Y hY hbound hsym).moment CappedColor.adjacency p =
      if (atomizedLabels labels C) p.1 ≠ (atomizedLabels labels C) p.2 ∨
          (atomizedLabels labels C) p.1 = none then 1 else 0 := by
  rw [model, ScalarModel.adjacency_moment]
  simp only [probability, adjacency_eq_true_iff]
  split_ifs <;> rfl

/-- The signed scalar charge is the actual new charge moment, not an
unrealized dual array or an externally supplied edited value. -/
theorem charge_moment
    (hzero : ∀ x y, adjacency labels x y = false → Y (x, y) = 0) (p : Ω × Ω) :
    (model labels hlabels C hC hCpos Y hY hbound hsym).moment CappedColor.charge p =
      atomizedCharge (ν := ν) C Y p := by
  rw [model, ScalarModel.charge_moment]
  by_cases hp : adjacency (atomizedLabels labels C) p.1 p.2 = true
  · simp [probability, hp, charge]
  · have hf := atomizedCharge_zero_of_nonedge (ν := ν) labels C Y hzero p.1 p.2
      (Bool.eq_false_iff.mpr hp)
    simp only [charge, hf, mul_zero]

/-- Genuine old all-order tests license the constructed colored model.
The terminal original-model theorem supplies these tests internally. -/
theorem fullFeasible_model (hCdust : C ⊆ labels ⁻¹' {none})
    (htests : ∀ n, FiniteArity.FeasibleOrder ν (adjacency labels) (fun x y => Y (x, y)) n) :
    FullFeasible (model labels hlabels C hC hCpos Y hY hbound hsym) := by
  apply ScalarModel.fullFeasible_model
    (probability labels C) (charge C hCpos Y hY hbound)
    (measurable_probability labels hlabels C hC) (measurable_charge C hC hCpos Y hY hbound)
    (Eventually.of_forall (probability_symm labels C))
    (Eventually.of_forall (charge_symm C hCpos Y hY hbound hsym))
    (adjacency (atomizedLabels labels C))
  · exact Eventually.of_forall (fun p hp => by simp [probability, hp])
  · intro n _
    exact feasibleOrder labels C hC hCpos hCdust Y hY hbound hsym n (htests n)

/-- External averaging preserves the actual total charge; only the
internal current-law C square is removed. -/
theorem objective_model
    (hzero : ∀ x y, adjacency labels x y = false → Y (x, y) = 0) :
    objective (model labels hlabels C hC hCpos Y hY hbound hsym) =
      (∫ p, Y p ∂ν.prod ν) / 2 - (∫ p in C ×ˢ C, Y p ∂ν.prod ν) / 2 := by
  unfold objective
  simp_rw [charge_moment labels hlabels C hC hCpos Y hY hbound hsym hzero]
  rw [integral_atomizedCharge C hC hCpos Y hY hbound hsym]
  ring

/-- The literal new class adds exactly its current mass square to the
actual multipartite missing-density identity. -/
theorem density_model (W : Model Ω ν)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if labels p.1 ≠ labels p.2 ∨ labels p.1 = none then 1 else 0)
    (hCdust : C ⊆ labels ⁻¹' {none}) :
    density (model labels hlabels C hC hCpos Y hY hbound hsym) =
      density W - (ν.real C) ^ 2 / 2 := by
  have hnewlabels := measurable_atomizedLabels labels hlabels C hC
  have hleft : Summable (fun i : ι =>
      (MultipartiteClassMasses.classMass ν (atomizedLabels labels C) (.inl i)) ^ 2) := by
    simpa only [MultipartiteClassMasses.classMass, atomized_old_fiber labels C hCdust] using
      MultipartiteClassMasses.classMass_sq_summable (μ := ν) labels hlabels
  have hright : Summable (fun u : Unit =>
      (MultipartiteClassMasses.classMass ν (atomizedLabels labels C) (.inr u)) ^ 2) :=
    Summable.of_finite
  have hsplit : (∑' j : ι ⊕ Unit,
      (MultipartiteClassMasses.classMass ν (atomizedLabels labels C) j) ^ 2) =
      (∑' i, (MultipartiteClassMasses.classMass ν labels i) ^ 2) + (ν.real C) ^ 2 := by
    rw [Summable.tsum_sum (f := fun j : ι ⊕ Unit =>
      (MultipartiteClassMasses.classMass ν (atomizedLabels labels C) j) ^ 2) hleft hright]
    congr 1
    · simp only [MultipartiteClassMasses.classMass, atomized_old_fiber labels C hCdust]
    · simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
      change (ν.real (atomizedLabels labels C ⁻¹' {some (.inr ())})) ^ 2 = _
      rw [atomized_new_fiber]
  have hold := MultipartiteClassMasses.one_sub_two_density_eq_tsum_classMass_sq W labels hlabels hA
  have hnew := MultipartiteClassMasses.one_sub_two_density_eq_tsum_classMass_sq
    (model labels hlabels C hC hCpos Y hY hbound hsym) (atomizedLabels labels C) hnewlabels
    (by
      filter_upwards [] with p
      have hp := adjacency_moment labels hlabels C hC hCpos Y hY hbound hsym p
      by_cases he : (atomizedLabels labels C) p.1 ≠ (atomizedLabels labels C) p.2 ∨
          (atomizedLabels labels C) p.1 = none <;> simpa only [he, ↓reduceIte] using hp)
  rw [hsplit] at hnew
  linarith

end ScalarConstruction

/-- Actual atomization of a positive current-law clique-dust set. The old
scalar representative and every new clique test are constructed internally. -/
theorem exists_model (W : Model Ω ν) (hW : FullFeasible W)
    (labels : Ω → Option ι) (hlabels : Measurable labels)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if labels p.1 ≠ labels p.2 ∨ labels p.1 = none then 1 else 0)
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (hCdust : C ⊆ labels ⁻¹' {none}) :
    ∃ V : Model Ω ν, FullFeasible V ∧
      (∀ p, V.moment CappedColor.adjacency p =
        if (atomizedLabels labels C) p.1 ≠ (atomizedLabels labels C) p.2 ∨
          (atomizedLabels labels C) p.1 = none then 1 else 0) ∧
      (∀ᵐ p ∂ν.prod ν, V.moment CappedColor.charge p =
        atomizedCharge (ν := ν) C (fun p => chargeKernel W p.1 p.2) p) ∧
      density V = density W - (ν.real C) ^ 2 / 2 ∧
      objective V = objective W - (∫ p in C ×ˢ C, chargeKernel W p.1 p.2 ∂ν.prod ν) / 2 := by
  let G := Function.uncurry (adjacency labels)
  have hG : Measurable G := measurable_adjacency labels hlabels
  have hGsym : ∀ x y, G (x, y) = G (y, x) := adjacency_symm labels
  have hA' : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p = if G p = true then 1 else 0 := by
    filter_upwards [hA] with p hp
    change _ = if adjacency labels p.1 p.2 = true then 1 else 0
    simpa only [adjacency_eq_true_iff] using hp
  obtain ⟨Y, hY, hsym, hbound, hzero, hcharge, htests⟩ :=
    BinaryRepresentative.exists_scalar_representative W hW G hG hGsym hA'
  let V := model labels hlabels C hC hCpos Y hY hbound hsym
  have hzero' : ∀ x y, adjacency labels x y = false → Y (x, y) = 0 :=
    fun x y => hzero (x, y)
  have hwhole : (∫ p, Y p ∂ν.prod ν) / 2 = objective W := by
    unfold objective
    congr 1
    exact integral_congr_ae hcharge
  have hinternal : (∫ p in C ×ˢ C, Y p ∂ν.prod ν) =
      ∫ p in C ×ˢ C, chargeKernel W p.1 p.2 ∂ν.prod ν :=
    integral_congr_ae (ae_restrict_of_ae hcharge)
  refine ⟨V, fullFeasible_model labels hlabels C hC hCpos Y hY hbound hsym hCdust htests,
    adjacency_moment labels hlabels C hC hCpos Y hY hbound hsym, ?_,
    density_model labels hlabels C hC hCpos Y hY hbound hsym W hA hCdust, ?_⟩
  · filter_upwards [atomizedCharge_congr_ae C hCpos Y
      (fun p => chargeKernel W p.1 p.2) hcharge] with p hp
    rw [charge_moment labels hlabels C hC hCpos Y hY hbound hsym hzero']
    exact hp
  · rw [objective_model labels hlabels C hC hCpos Y hY hbound hsym hzero', hwhole, hinternal]

variable [StandardBorelSpace Ω] [NullSingletonClass ν]

/-- Actual clique-dust atomization followed by the genuine own-profile
bound gives the exact required signed internal-charge comparison. -/
theorem objective_sub_internal_le_sq (W : Model Ω ν) (hW : FullFeasible W)
    (labels : Ω → Option ι) (hlabels : Measurable labels)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if labels p.1 ≠ labels p.2 ∨ labels p.1 = none then 1 else 0)
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < ν C)
    (hCdust : C ⊆ labels ⁻¹' {none}) (A : ℝ)
    (hclasses : ∀ i, MultipartiteClassMasses.classMass ν labels i ≤ A)
    (hCA : ν.real C ≤ A) :
    objective W - (∫ p in C ×ˢ C, chargeKernel W p.1 p.2 ∂ν.prod ν) / 2 ≤ A ^ 2 := by
  obtain ⟨V, hV, hAdj, _, _, hObj⟩ := exists_model W hW labels hlabels hA C hC hCpos hCdust
  have hparts : ∀ j : ι ⊕ Unit,
      MultipartiteClassMasses.classMass ν (atomizedLabels labels C) j ≤ A := by
    intro j
    cases j with
    | inl i =>
      simpa only [MultipartiteClassMasses.classMass, atomized_old_fiber labels C hCdust] using hclasses i
    | inr u =>
      cases u
      simpa only [MultipartiteClassMasses.classMass, atomized_new_fiber] using hCA
  have h := MultipartiteClassMasses.objective_le_class_bound_sq V hV
    (atomizedLabels labels C) (measurable_atomizedLabels labels hlabels C hC)
    (by
      filter_upwards [] with p
      have hp := hAdj p
      by_cases he : (atomizedLabels labels C) p.1 ≠ (atomizedLabels labels C) p.2 ∨
          (atomizedLabels labels C) p.1 = none <;> simpa only [he, ↓reduceIte] using hp) A hparts
  rwa [hObj] at h

end Erdos1017.CappedModel.DustAtomization
