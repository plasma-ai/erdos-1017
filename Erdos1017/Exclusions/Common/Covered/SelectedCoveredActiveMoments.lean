module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredResidualCounts
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomResidualTightness
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountMoments

/-!
# Tight residual moments of the four-region dual

Every feasible represented four-region dual with the original cost has a tight
residual cost measure on the same original parents
(`exists_covered_active_tight_moment_data`).
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

/-- Every feasible represented four-region dual with the original cost
has a genuine tight residual cost measure on the same original parents.
The four-region representation remains explicit until exterior atoms
are eliminated; no own multiplier or selected structure is transferred. -/
theorem exists_covered_active_tight_moment_data
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hA : label ⁻¹' {0} = {v | S.ρ v = a.val})
    (hB : label ⁻¹' {1} = {v | S.ρ v = r.val})
    (hRl : label ⁻¹' {2} = S.D ∩ S.rootNeighborhood a)
    (hEl : label ⁻¹' {3} = S.D \ S.rootNeighborhood a)
    (hgraph : ∀ᵐ p ∂μ.prod μ, PhysicalRepresentative.adjacency W m p.1 p.2 =
      TwoAtomCountGate.blockAdjacency (label p.1) (label p.2)) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      ∀ (x : TwoAtomCountGate.Coefficients), x ∈ TwoAtomCountGate.feasible →
      TwoAtomCountGate.objective
        (μ.real {v | S.ρ v = a.val}) (μ.real {v | S.ρ v = r.val})
        (μ.real (S.D ∩ S.rootNeighborhood a)) (μ.real (S.D \ S.rootNeighborhood a)) x = c →
      ∃ D : TwoAtomCountGate.TightMomentData x
        (μ.real {v | S.ρ v = a.val}) (μ.real {v | S.ρ v = r.val})
        (μ.real (S.D ∩ S.rootNeighborhood a)) (μ.real (S.D \ S.rootNeighborhood a)),
        D.law = PhysicalPrimal.countMeasure P.orderCap
          (PhysicalPrimal.withoutRegion P.laws {v | S.ρ v = a.val})
          (S.D ∩ S.rootNeighborhood a) (S.D \ S.rootNeighborhood a) := by
  obtain ⟨P, hfinite, hi, _, hfirstR, hfirstE, hfactorR, hfactorE, hcross⟩ :=
    S.exists_covered_residual_count_measure r a hW hd hgap hpair hzero hR hE
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hroot (n : ℕ) : ∀ᵐ v ∂P.laws n, ∃! i, label (v i) = 1 := by
    filter_upwards [P.ae_parent_meets_of_zero_body hzero n, P.unique_root n] with v hv hu
    have he (i : Fin n) : label (v i) = 1 ↔ S.ρ (v i) = r.val := by
      change v i ∈ label ⁻¹' {1} ↔ v i ∈ {v | S.ρ v = r.val}
      rw [hB]
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, (he i).mpr hi, fun j hj => hu j i ((he j).mp hj) hi⟩
  refine ⟨P, ?_⟩
  intro x hx hvalue
  have hcost : PhysicalPrimal.cost P.laws = TwoAtomCountGate.objective
      (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) x := by
    rw [hA, hB, hRl, hEl, hvalue, P.cost]
  have ht := TwoAtomCountGate.ae_residual_countTest P.orderCap P.laws
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.measurable_adjacency W m)
    label hlabel hgraph x hx P.feasible hroot hcost
  rw [hA, hRl, hEl] at ht
  refine ⟨{
    law := PhysicalPrimal.countMeasure P.orderCap
      (PhysicalPrimal.withoutRegion P.laws {v | S.ρ v = a.val})
      (S.D ∩ S.rootNeighborhood a) (S.D \ S.rootNeighborhood a)
    finite := hfinite
    integrable_first_R := hi _
    integrable_first_E := hi _
    integrable_factor_R := hi _
    integrable_factor_E := hi _
    integrable_cross := hi _
    first_R := hfirstR
    first_E := hfirstE
    factor_R := hfactorR
    factor_E := hfactorE
    cross := hcross
    tight := ht }, rfl⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
