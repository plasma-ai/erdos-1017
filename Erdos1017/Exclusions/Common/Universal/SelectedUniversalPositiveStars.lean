module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalExposure
public import Erdos1017.Exclusions.Common.RootLeafDegreeIncidence

/-!
# Positive root charge at exterior vertices

This module transfers the original pair-null and vertex-null events to every
parent through pair balance and the coordinate marginals, eliminates two-point
root-leaf incidences by unsaturation, and shows the triangle exposure and degree
incidence force a positive universal root charge at almost every exterior
vertex.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem orderRootLeaves_eq_zero_of_no_incidence
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (ρ : Measure (Fin n → Ω))
    (I B : Set Ω) (hB : MeasurableSet B)
    (hno : ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → v i ∈ I → v j ∈ B → False) :
    PhysicalPrimal.orderRootLeaves n ρ I B = 0 := by
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hno] with v hv hm
  exact hv ij.val.1 ij.val.2 ij.property hm.2 hm.1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

namespace UniversalPhysicalPrimal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Exact original pair balance transfers one original pair-null event
to every actual parent pair, including singular parents. -/
theorem ae_original_pairs (P : S.UniversalPhysicalPrimal r c)
    (F : Ω × Ω → Prop) (hF : ∀ᵐ p ∂μ.prod μ, F p) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j → F (v i, v j) := by
  apply PhysicalPrimal.ae_all_pairs_of_balance P.laws _ P.feasible.2.2.2 F _ n
  exact Measure.absolutelyContinuous_restrict.ae_le hF

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Actual original vertex-null events transfer through the derived
coordinate marginals, without any joint product-density hypothesis. -/
theorem ae_original_vertices (P : S.UniversalPhysicalPrimal r c)
    (F : Ω → Prop) (hF : ∀ᵐ x ∂μ, F x) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i, F (v i) := by
  simp only [ae_all_iff]
  intro i
  have hc := PhysicalPrimal.coordinate_marginal_absolutelyContinuous_of_balance
    P.laws _ P.feasible.1 P.feasible.2.1 P.feasible.2.2.2 n i
  have hd := (PhysicalPrimal.graphDemand_fst_le μ
    {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}).absolutelyContinuous
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable ((hc.trans hd).ae_le hF)

/-- Original unsaturation eliminates every two-point root-leaf incidence.
Rootless two-point parents are retained at this stage. -/
theorem orderRootLeaves_two_eq_zero (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1) (B : Set Ω) (hB : MeasurableSet B) :
    PhysicalPrimal.orderRootLeaves 2 (P.laws 2) {x | S.ρ x = r.val} B = 0 := by
  have hslack := P.ae_original_vertices _
    (S.ae_unsaturated_universal_rootChargeRow r hW hd hgap hstar) 2
  have hrow := P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) 2
  apply orderRootLeaves_eq_zero_of_no_incidence (P.laws 2) _ B hB
  filter_upwards [hslack, hrow, P.unique_root 2, P.tight_physical 2]
    with v hs hr hu ht i j hij hi _
  have hcharge : PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v =
      PhysicalRepresentative.charge W m (v 0) (v 1) := by
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
  have hpair : ∀ i j : Fin 2, i ≠ j → PhysicalRepresentative.charge W m (v i) (v j) = 1 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hcharge.symm.trans ht
    · exact (PhysicalRepresentative.charge_symm W m (v 1) (v 0)).trans (hcharge.symm.trans ht)
    · exact False.elim (hij rfl)
  have hne : S.ρ (v j) ≠ r.val := fun hj => hij (hu i j hi hj)
  have hlt := hs j hne
  have he := hr i j hij hi
  linarith [hpair i j hij]

/-- Triangle exposure and actual degree incidence force the original
universal root charge positive at almost every exterior vertex. Neither
an incidence density nor an exterior-exposure bound is assumed. -/
theorem ae_positive_exterior_rootChargeRow (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → 0 < S.rootChargeRow r x := by
  let I := {x | S.ρ x = r.val}
  let B := Iᶜ ∩ {x | S.rootChargeRow r x ≤ 0}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hB : MeasurableSet B := hI.compl.inter
    (measurableSet_le (S.measurable_rootChargeRow r) measurable_const)
  have hsmall : ∀ n, n < 4 → PhysicalPrimal.orderRootLeaves n (P.laws n) I B = 0 := by
    intro n hn
    interval_cases n
    · simp [P.feasible.1, PhysicalPrimal.orderRootLeaves]
    · simp [P.feasible.2.1, PhysicalPrimal.orderRootLeaves]
    · exact P.orderRootLeaves_two_eq_zero hW hd hgap hstar B hB
    · apply orderRootLeaves_eq_zero_of_no_incidence (P.laws 3) I B hB
      filter_upwards [P.ae_triangle_star_pos hW hd hgap hN hstar hA hell hmargin]
        with v hv i j hij hi hj
      exact (not_lt_of_ge hj.2) (hv i j hij hi)
  have hE : MeasurableSet {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hzero := PhysicalPrimal.null_event_of_small_root_incidence P.laws μ _ hE
    P.feasible.2.2.2 I hI (S.neutral_atom_physical_blocks r hW hd hgap hN).1
    P.unique_root B hB inter_subset_left hsmall hA
  have hnot : ∀ᵐ x ∂μ, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with x hx houtside
  by_contra hbad
  exact hx ⟨houtside, le_of_not_gt hbad⟩

end UniversalPhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure
