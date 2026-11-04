module

public import Erdos1017.Exclusions.Cusp.CappedUniversalSet
public import Erdos1017.SelectedModel.ZeroClass.AtomlessClassLabels
public import Erdos1017.Exclusions.Common.SharpCounts.MultipartiteSharpCountCells

/-!
# Shrinking the distinguished class to one third

Shrinking only the distinguished class to one third and turning its removed mass
into zero-charge universal dust gives an edited full dual obeying the sharp
small-part cap (`objective_le_shrunk_third`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.MultipartiteClassMasses

open CappedModel

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

local instance headDustOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- Shrink only the distinguished class to one third and turn its removed
mass into zero-charge universal dust. The actual edited full dual obeys the
sharp small-part cap, while the cost loss is bounded by deleted pair mass. -/
theorem objective_le_shrunk_third (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0)
    (i : ι) (hT : 1 / 3 < classMass μ q i)
    (hother : ∀ j, j ≠ i → classMass μ q j ≤ 1 / 3) :
    objective W ≤ (1 - 2 * density W - (classMass μ q i) ^ 2) / 3 + 2 / 27 +
      (classMass μ q i - 1 / 3) * (1 - classMass μ q i) := by
  let P := {x | q x = some i}
  let T := classMass μ q i
  have hP : MeasurableSet P := hq (measurableSet_singleton (some i))
  have hT0 : 0 < T := by dsimp [T]; linarith only [hT]
  have hPpos : 0 < μ P := ENNReal.toReal_pos_iff.mp hT0 |>.1
  let w : Fin 2 → ℝ := ![(T - 1 / 3) / T, (1 / 3) / T]
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    fin_cases j
    · exact div_nonneg (by dsimp [T]; linarith only [hT]) hT0.le
    · exact div_nonneg (by norm_num) hT0.le
  have hsum : ∑ j, w j = 1 := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  obtain ⟨L, hL, hmass⟩ := exists_atomless_class_labels_of_masses P hP hPpos
    (by decide : 0 < 2) w hw hsum
  let C := P ∩ L ⁻¹' {0}
  have hC : MeasurableSet C := hP.inter (hL.measurable (measurableSet_singleton 0))
  have hCP : C ⊆ P := inter_subset_left
  have hCm : μ.real C = T - 1 / 3 := by
    rw [hmass]
    change T * ((T - 1 / 3) / T) = T - 1 / 3
    field_simp
  let q' : Ω → Option ι := fun x => if x ∈ C then none else q x
  have hq' : Measurable q' := measurable_const.ite hC hq
  let U := universalSet W C hC
  have hU : FullFeasible U := fullFeasible_universalSet W hW C hC
  have hmass' (j : ι) : classMass μ q' j =
      if j = i then 1 / 3 else classMass μ q j := by
    have he : {x | q' x = some j} = {x | q x = some j} \ C := by
      ext x
      by_cases hx : x ∈ C <;> simp [q', hx]
    change μ.real {x | q' x = some j} = _
    rw [he]
    by_cases hj : j = i
    · subst j
      rw [ite_eq_left rfl, measureReal_sdiff (μ := μ) hCP hC, hCm]
      change T - (T - 1 / 3) = 1 / 3
      ring
    · rw [ite_eq_right hj]
      have heq : {x | q x = some j} \ C = {x | q x = some j} := by
        apply sdiff_eq_left.mpr
        apply Set.disjoint_left.mpr
        intro x hx hc
        exact hj (Option.some.inj (hx.symm.trans (hCP hc)))
      rw [heq]
      rfl
  have hsupport' : ∀ᵐ p ∂μ.prod μ, U.moment CappedColor.adjacency p =
      if q' p.1 ≠ q' p.2 ∨ q' p.1 = none then 1 else 0 := by
    filter_upwards [hsupport] with p hp
    rw [adjacency_moment_universalSet]
    by_cases hx : p.1 ∈ C <;> by_cases hy : p.2 ∈ C <;> simp_all [q']
  have hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P →
      W.moment CappedColor.adjacency p = 0 := by
    filter_upwards [hsupport] with p hp hx hy
    rw [hp]
    simp only [show q p.1 = some i from hx, show q p.2 = some i from hy,
      ne_eq, not_true_eq_false, reduceCtorEq, or_self, ite_false]
  have hcomparison := universalSet_independent_comparison W P C hP hC hCP hind
  rw [hCm] at hcomparison
  change density W + (T - 1 / 3) * T - (T - 1 / 3) ^ 2 / 2 ≤ density U ∧
    objective W - (T - 1 / 3) * (1 - T) ≤ objective U at hcomparison
  have hcost := objective_le_sharp_smallPart U hU q' hq' hsupport' i
    (by rw [hmass']; norm_num) (by rw [hmass']; simp) (by
      intro j
      rw [hmass', hmass']
      simp only [ite_true]
      split_ifs with hj
      · exact le_rfl
      · exact hother j hj)
  have hb := hcost.trans (min_le_right _ _)
  change objective W ≤ (1 - 2 * density W - T ^ 2) / 3 + 2 / 27 +
    (T - 1 / 3) * (1 - T)
  nlinarith only [hcomparison.1, hcomparison.2, hb]

end Erdos1017.MultipartiteClassMasses
