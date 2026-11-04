module

public import Erdos1017.Exclusions.Common.HomogeneousCompletionWitness
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredRepeatWitness
public import Erdos1017.Exclusions.Common.SelectedAtomCopy

/-!
# Two-copy completion witness for an exterior atom

An exterior independent atom in the zero-body branch has a two-copy completion
witness with strict incidence above the optimum's own `ell`, with and without an
additional tuple event.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- An actual exterior independent atom in the zero-body branch has a
two-copy completion witness with strict incidence above its own ell.
Homogeneity, original subset tests, and the violating event are derived
from the same selected model. -/
theorem exists_two_copy_completion_witness_with_good
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (Good : ∀ n, (Fin n → Ω) → Prop)
    (hGood : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v) :
    let A := PhysicalRepresentative.adjacency W m
    let Y := PhysicalRepresentative.charge W m
    let D := {x | S.ρ x = u.val}
    ∃ n, 2 ≤ n ∧ ∃ v : Fin n → Ω,
      FiniteArity.TupleClique (FiniteArity.completeAdjacency A D) v ∧
      Good n v ∧
      ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => v i ∈ D) ∧ T.card = 2 ∧
        1 < FiniteArity.pairCharge (T ∪ Finset.univ.filter (fun i => v i ∉ D))
          (fun i j => if i = j then 0 else FiniteArity.completeCharge A Y D (-m) (v i) (v j)) ∧
        -m < ∑ i ∈ Finset.univ.filter (fun i => v i ∉ D), S.rootChargeRow u (v i) := by
  let Y := PhysicalRepresentative.charge W m
  let R := {x | S.ρ x = r.val}
  let D := {x | S.ρ x = u.val}
  have hs := hW.strict_gap_structure hd hgap
  have hdisj : Disjoint R D := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hb he hx hy
    exact he.trans_le (hb hx hy)
  obtain ⟨n, hn, hpositive⟩ := S.exists_positive_completion_violation u hW hd hgap
  have hgood := FiniteArity.ae_two_copy_subset_of_homogeneous_completion μ
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
    (fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2)
    {x | S.ρ x = r.val} {x | S.ρ x = u.val} hdisj (-m) hell (S.rootChargeRow u)
    (S.ae_root_fiber_physical_independent r hW hd hgap)
    (S.ae_root_fiber_physical_independent u hW hd hgap) hbody
    (S.ae_root_charge u hW hd hgap)
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic) n
  obtain ⟨v, hv, htest⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpositive.ne'
    (ae_restrict_of_ae (hgood.and (hGood n)))
  obtain ⟨T, hTD, hcard, hbad, hincidence⟩ := htest.1 hv.1 hv.2
  exact ⟨n, hn, v, hv.1, htest.2, T, hTD, hcard, hbad, hincidence⟩

/-- The actual two-copy witness without an additional tuple event. -/
theorem exists_two_copy_completion_witness
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    let A := PhysicalRepresentative.adjacency W m
    let Y := PhysicalRepresentative.charge W m
    let D := {x | S.ρ x = u.val}
    ∃ n, 2 ≤ n ∧ ∃ v : Fin n → Ω,
      FiniteArity.TupleClique (FiniteArity.completeAdjacency A D) v ∧
      ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => v i ∈ D) ∧ T.card = 2 ∧
        1 < FiniteArity.pairCharge (T ∪ Finset.univ.filter (fun i => v i ∉ D))
          (fun i j => if i = j then 0 else FiniteArity.completeCharge A Y D (-m) (v i) (v j)) ∧
        -m < ∑ i ∈ Finset.univ.filter (fun i => v i ∉ D), S.rootChargeRow u (v i) := by
  obtain ⟨n, hn, v, hclique, _, T, hTD, hcard, hbad, hincidence⟩ :=
    S.exists_two_copy_completion_witness_with_good r u hru hW hd hgap hell hzero
      (fun _ _ => True) (fun _ => Eventually.of_forall (fun _ => True.intro))
  exact ⟨n, hn, v, hclique, T, hTD, hcard, hbad, hincidence⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
