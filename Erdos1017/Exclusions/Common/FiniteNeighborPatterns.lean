module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite incidence patterns of positive mass

A positive set whose countable incidence mass exceeds a threshold contains a
positive measurable finite incidence pattern.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.FiniteNeighborPatterns

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {μ : Measure Ω}

/-- A positive set whose actual countable incidence mass exceeds a
threshold contains one positive measurable finite incidence pattern. -/
theorem exists_positive_finite_pattern (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsum : Summable a) (P : ι → Set Ω) (hP : ∀ i, MeasurableSet (P i))
    (E : Set Ω) (hE : MeasurableSet E) (hEpos : 0 < μ E) (b : ℝ)
    (hbad : ∀ᵐ x ∂μ, x ∈ E → b < ∑' i, if x ∈ P i then a i else 0) :
    ∃ (J : Finset ι) (C : Set Ω), MeasurableSet C ∧ 0 < μ C ∧ C ⊆ E ∧
      (∀ i ∈ J, C ⊆ P i) ∧ b < ∑ i ∈ J, a i := by
  let C (J : Finset ι) : Set Ω :=
    if b < ∑ i ∈ J, a i then E ∩ ⋂ i ∈ J, P i else ∅
  have hC (J : Finset ι) : MeasurableSet (C J) := by
    unfold C
    split_ifs
    · exact hE.inter (MeasurableSet.biInter J.finite_toSet.countable (fun i _ => hP i))
    · exact MeasurableSet.empty
  have hcover : ∀ᵐ x ∂μ, x ∈ E → x ∈ ⋃ J : Finset ι, C J := by
    filter_upwards [hbad] with x hx hxE
    have hs : Summable (fun i => if x ∈ P i then a i else 0) :=
      Summable.of_nonneg_of_le (fun i => by split_ifs; exact ha i; exact le_rfl)
        (fun i => by split_ifs <;> simp_all) hsum
    obtain ⟨F, hF⟩ : ∃ F : Finset ι, b < ∑ i ∈ F, if x ∈ P i then a i else 0 := by
      by_contra hn
      push Not at hn
      exact (not_le_of_gt (hx hxE)) (hasSum_le_of_sum_le hs.hasSum hn)
    let J := F.filter (fun i => x ∈ P i)
    have hsumJ : (∑ i ∈ J, a i) = ∑ i ∈ F, if x ∈ P i then a i else 0 := by
      exact Finset.sum_filter _ _
    have hb : b < ∑ i ∈ J, a i := by rw [hsumJ]; exact hF
    apply mem_iUnion.mpr
    refine ⟨J, ?_⟩
    simp only [C, hb, ↓reduceIte]
    exact ⟨hxE, mem_iInter.mpr (fun i => mem_iInter.mpr
      (fun hi => (Finset.mem_filter.mp hi).2))⟩
  have hmass : μ E = μ (⋃ J : Finset ι, C J) := by
    apply measure_congr
    filter_upwards [hcover] with x hx
    apply propext
    refine ⟨hx, ?_⟩
    intro hxC
    obtain ⟨J, hJ⟩ := mem_iUnion.mp hxC
    unfold C at hJ
    split_ifs at hJ
    · exact hJ.1
    · exact False.elim (notMem_empty x hJ)
  obtain ⟨J, hJ⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (show μ (⋃ J : Finset ι, C J) ≠ 0 by rw [← hmass]; exact hEpos.ne')
  have hb : b < ∑ i ∈ J, a i := by
    by_contra hn
    have hz : C J = ∅ := ite_eq_right hn
    rw [hz, measure_empty] at hJ
    exact (lt_irrefl _ hJ).elim
  refine ⟨J, C J, hC J, hJ, ?_, ?_, hb⟩
  · simp only [C, hb, ↓reduceIte]
    exact inter_subset_left
  · intro i hi x hx
    simp only [C, hb, ↓reduceIte] at hx
    exact mem_iInter.mp (mem_iInter.mp hx.2 i) hi

end Erdos1017.FiniteNeighborPatterns
