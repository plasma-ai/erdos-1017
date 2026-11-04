module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatWitness
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyAtomFloor

/-!
# Violating completion test at every positive atom

Every positive original independent atom has a finite violating completion test
at the original shifted-neutral charge, using the original optimum and its
transverse direction (`exists_positive_completion_violation`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Every positive original independent atom has an actual finite
violating completion test at the old shifted-neutral charge. The original
optimum and its transverse direction rule out all-order feasibility. -/
theorem exists_positive_completion_violation
    (S : SelectedHighLowStructure W m) (u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let D := {x | S.ρ x = u.val}
    ∃ n, 2 ≤ n ∧ 0 < (Measure.pi (fun _ : Fin n => μ))
      {v | FiniteArity.TupleClique
          (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D) v ∧
        1 < FiniteArity.tupleCharge
          (FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
            (PhysicalRepresentative.charge W m) D (-m)) v} := by
  classical
  let D := {x | S.ρ x = u.val}
  have hD : MeasurableSet D := (S.hfibers u.val u.property).1
  have hs := hW.strict_gap_structure hd hgap
  apply FiniteArity.exists_positive_violation_of_not_all_feasible μ
  intro hcap
  obtain ⟨v, hL, hQ⟩ := hW.exists_transverse_positive_direction hd hgap
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmass := ZeroCompletion.missingMass_eq_zero_of_full_optimum W hopt m
    (2 * (c - m * d)) hW.multiplier_mem hs.strict_support hW.stationary
    v hL hQ D hD hcap
  have hcomplete := ZeroCompletion.ae_complete_of_missingMass_eq_zero W m D hD
    hs.strict_support hmass
  have hind := (S.hfibers u.val u.property).2.2.1
  rw [Measure.prod_restrict] at hind
  have hind' := (ae_restrict_iff' (hD.prod hD)).mp hind
  have hfalse : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → False := by
    filter_upwards [hcomplete, hind'] with p hc hi hx hy
    have he := hc hx hy
    have hz := hi ⟨hx, hy⟩
    change W.moment CappedColor.adjacency p = 0 at hz
    linarith
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hfalse))
  obtain ⟨y, hy, hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' (ae_restrict_of_ae hrow)
  exact hxy hx hy

end Erdos1017.CappedModel.SelectedHighLowStructure
