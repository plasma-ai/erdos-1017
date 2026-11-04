module

public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientBounds
public import Erdos1017.Exclusions.Common.FullCrossCompletionObstruction

/-!
# The covered `E` star exceeds ell

The `E` star coefficient of `coveredCoefficient` exceeds the original `ell`; the
own stationary averaged model and the cross-only root-canceling insertion it
needs are constructed inside the proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The literal actual E star exceeds the original ell. Its own
stationary averaged model and actual cross-only root-cancelling insertion
are constructed internally; neither a completion nor a star bound is an
input. Both original diffuse regions remain positive and labeled. -/
theorem coveredCoefficient_root_E_gt (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    -m < S.coveredCoefficient a (Sum.inl r) (Sum.inr false) := by
  obtain ⟨V, hV, hmom, _, _⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  let R := {x | S.ρ x = r.val}
  let C := {x | S.ρ x = a.val}
  let F := S.D \ S.rootNeighborhood a
  have hlabel (u : S.I) (x : Ω) (hx : S.ρ x = u.val) :
      S.coveredLabel a x = Sum.inl u := (S.coveredLabel_eq_inl_iff a u x).mpr hx
  have hlabelF (x : Ω) (hx : x ∈ F) : S.coveredLabel a x = Sum.inr false := by
    have hx' : x ∈ S.coveredLabel a ⁻¹' {Sum.inr false} := by
      rw [S.coveredLabel_fiber_false]
      exact hx
    exact hx'
  have hRC : Disjoint R C := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hpair.1 (Subtype.ext (hx.symm.trans hy))
  have hRF : Disjoint R F := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact S.row_ne_atom_of_mem_diffuse x hy.1 r hx
  have hCF : Disjoint C F := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact S.row_ne_atom_of_mem_diffuse x hy.1 a hx
  have hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → adjacencyKernel V p.1 p.2 = 0 := by
    filter_upwards with p hx hy
    change V.moment CappedColor.adjacency p = 0
    rw [(hmom p).1, hlabel r p.1 hx, hlabel r p.2 hy]
    simp [coveredGraph]
  have hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → adjacencyKernel V p.1 p.2 = 0 := by
    filter_upwards with p hx hy
    change V.moment CappedColor.adjacency p = 0
    rw [(hmom p).1, hlabel a p.1 hx, hlabelF p.2 hy]
    simp [coveredGraph]
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → chargeKernel V p.1 p.2 ≤ 0 := by
    filter_upwards with p hx hy
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    apply S.coveredCoefficient_nonpositive r a hzero
    · intro he
      exact hx ((S.coveredLabel_eq_inl_iff a r p.1).mp he)
    · intro he
      exact hy ((S.coveredLabel_eq_inl_iff a r p.2).mp he)
  have hconstant : ∀ᵐ p ∂μ.prod μ, p.1 ∈ F → p.2 ∈ R → chargeKernel V p.1 p.2 =
      S.coveredCoefficient a (Sum.inl r) (Sum.inr false) := by
    filter_upwards with p hx hy
    change V.moment CappedColor.charge p = _
    rw [(hmom p).2]
    change S.coveredCoefficient a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = _
    rw [hlabelF p.1 hx, hlabel r p.2 hy]
    exact S.coveredCoefficient_symm a _ _
  exact cross_root_charge_gt_of_constant V hV hd hgap R C F
    (S.hfibers a.val a.property).1 (S.hD.diff (S.measurableSet_rootNeighborhood a))
    (S.hfibers a.val a.property).2.1 hE hRC hRF hCF hroot hcross hbody hconstant

end Erdos1017.CappedModel.SelectedHighLowStructure
