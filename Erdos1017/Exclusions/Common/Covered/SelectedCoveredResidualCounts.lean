module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedParentCounts
public import Erdos1017.Exclusions.Common.Physical.PhysicalResidualCountMeasure

/-!
# Residual count measure of parents avoiding A

Restricting the physical parents to those avoiding `A` and pushing their `R`/`E`
counts forward gives a finite measure whose cost and five residual moments are
derived (`exists_covered_residual_count_measure`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Restrict the actual original physical parents to those avoiding A,
then push their R/E counts forward. The cost and all five residual
moments are derived from actual pair balance and saturated-parent shape.
This remains valid before exterior atoms are eliminated. -/
theorem exists_covered_residual_count_measure
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      let A := {x | S.ρ x = a.val}
      let R := S.D ∩ S.rootNeighborhood a
      let E := S.D \ S.rootNeighborhood a
      let θ := PhysicalPrimal.countMeasure P.orderCap (PhysicalPrimal.withoutRegion P.laws A) R E
      IsFiniteMeasure θ ∧ (∀ F : ℕ × ℕ → ℝ, Integrable F θ) ∧
      θ.real univ = c - μ.real A * μ.real {x | S.ρ x = r.val} ∧
      (∫ z, (z.1 : ℝ) ∂θ) = (μ.real {x | S.ρ x = r.val} - μ.real A) * μ.real R ∧
      (∫ z, (z.2 : ℝ) ∂θ) = μ.real {x | S.ρ x = r.val} * μ.real E ∧
      (∫ z, (z.1 : ℝ) * ((z.1 : ℝ) - 1) ∂θ) = (μ.real R) ^ 2 ∧
      (∫ z, (z.2 : ℝ) * ((z.2 : ℝ) - 1) ∂θ) = (μ.real E) ^ 2 ∧
      (∫ z, (z.1 : ℝ) * (z.2 : ℝ) ∂θ) = μ.real R * μ.real E := by
  obtain ⟨P, hroot, _, _⟩ := S.exists_covered_tight_physical_primal
    r a hW hd hgap hpair hzero hR hE
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let A := {x | S.ρ x = a.val}
  let R := S.D ∩ S.rootNeighborhood a
  let E := S.D \ S.rootNeighborhood a
  let I := {x | S.ρ x = r.val}
  let G := {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true}
  let demand := PhysicalPrimal.graphDemand μ G
  let : IsFiniteMeasure demand := by
    dsimp only [demand, PhysicalPrimal.graphDemand]
    infer_instance
  have hRm : MeasurableSet R := S.hD.inter (S.measurableSet_rootNeighborhood a)
  have hEm : MeasurableSet E := S.hD.diff (S.measurableSet_rootNeighborhood a)
  have hIm : MeasurableSet I := (S.hfibers r.val r.property).1
  have hAm : MeasurableSet A := (S.hfibers a.val a.property).1
  have hIA : Disjoint I A := Set.disjoint_left.mpr (fun _ hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hAR : Disjoint A R := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x hy.1 a hx)
  have hIR : Disjoint I R := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x hy.1 r hx)
  have hIE : Disjoint I E := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x hy.1 r hx)
  have hRE : Disjoint R E := Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
  have hcap (n : ℕ) (hn : P.orderCap < n) : P.laws n = 0 := P.capped n (Or.inr hn)
  have hDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D → p ∈ G := by
    filter_upwards [S.hDcomplete, PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hp he hx hy
    have hm := hp hx hy
    rw [hm] at he
    change PhysicalRepresentative.adjacency W m p.1 p.2 = true
    cases hg : PhysicalRepresentative.adjacency W m p.1 p.2
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at he
      norm_num at he
    · rfl
  have hID : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ S.D → p ∈ G := by
    filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero] with p hp hx hy
    exact (hp hx).mpr (S.row_ne_atom_of_mem_diffuse p.2 hy r)
  have hIAmass : demand.real (I ×ˢ A) = μ.real I * μ.real A :=
    PhysicalPrimal.graphDemand_real_rectangle μ G I A hIm hAm (by
      filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero] with p hp hx hy
      exact (hp hx).mpr (fun he => hpair.1 (Subtype.ext (he.symm.trans hy))))
  have hARmass : demand.real (A ×ˢ R) = μ.real A * μ.real R :=
    PhysicalPrimal.graphDemand_real_rectangle μ G A R hAm hRm (by
      filter_upwards [S.ae_root_adjacency a hW hd hgap] with p hp hx hy
      exact (hp hx).mpr hy.2)
  have hIRmass : demand.real (I ×ˢ R) = μ.real I * μ.real R :=
    PhysicalPrimal.graphDemand_real_rectangle μ G I R hIm hRm
      (hID.mono (fun _ hp hx hy => hp hx hy.1))
  have hIEmass : demand.real (I ×ˢ E) = μ.real I * μ.real E :=
    PhysicalPrimal.graphDemand_real_rectangle μ G I E hIm hEm
      (hID.mono (fun _ hp hx hy => hp hx hy.1))
  have hRRmass : demand.real (R ×ˢ R) = (μ.real R) ^ 2 := by
    simpa only [pow_two] using PhysicalPrimal.graphDemand_real_rectangle μ G R R hRm hRm
      (hDD.mono (fun _ hp hx hy => hp hx.1 hy.1))
  have hEEmass : demand.real (E ×ˢ E) = (μ.real E) ^ 2 := by
    simpa only [pow_two] using PhysicalPrimal.graphDemand_real_rectangle μ G E E hEm hEm
      (hDD.mono (fun _ hp hx hy => hp hx.1 hy.1))
  have hREmass : demand.real (R ×ˢ E) = μ.real R * μ.real E :=
    PhysicalPrimal.graphDemand_real_rectangle μ G R E hRm hEm
      (hDD.mono (fun _ hp hx hy => hp hx.1 hy.1))
  have hm := PhysicalPrimal.residual_count_moments P.orderCap P.laws I A R E
    hIm hAm hRm hEm hIA hIR hIE hAR hRE hroot
    (P.ae_saturated_parent_count_shape a hW hd hgap hpair hzero) hcap demand P.feasible.2.2.2
  dsimp only at hm
  rw [hIAmass, hIRmass, hARmass, hIEmass, hRRmass, hEEmass, hREmass, P.cost] at hm
  refine ⟨P, inferInstance,
    PhysicalPrimal.integrable_countMeasure P.orderCap (PhysicalPrimal.withoutRegion P.laws A)
      R E hRm hEm, ?_, ?_, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2⟩
  · simpa only [mul_comm (μ.real I) (μ.real A)] using hm.1
  · rw [hm.2.1]
    ring

end Erdos1017.CappedModel.SelectedHighLowStructure
