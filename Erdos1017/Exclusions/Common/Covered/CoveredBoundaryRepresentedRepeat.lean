module

public import Erdos1017.Exclusions.Common.Covered.CoveredBoundaryCoefficientBounds
public import Erdos1017.Exclusions.Common.FullIndependentCompletionWitness

/-!
# Repeat witness of a represented boundary model

A fixed represented conditional boundary model supplies its own repeat witness,
with the exceptional product events allowed to depend on the model so that no
uncountable family of events must be combined.
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

/-- A fixed actual represented conditional model supplies its own
repeat witness. Extra product-AE events may depend on this V, so no
intersection over an uncountable family of possible models is taken. -/
theorem covered_boundary_repeat_witness_of_model (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I)
    (V : Model Ω μ) {d c : ℝ} (hV : FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if S.coveredCountableBoundaryGraph mode r a
          (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = S.coveredCountableBoundaryCoefficient
        (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2))
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (u : S.I) (hru : r ≠ u) (hell : 1 / 2 < -m)
    (Good : ∀ n, (Fin n → Ω) → Prop)
    (hGood : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v) :
    ∃ n, 2 ≤ n ∧ ∃ v : Fin n → Ω,
      FiniteArity.TupleClique (FiniteArity.completeAdjacency
        (PhysicalRepresentative.adjacency V m) {x | S.ρ x = u.val}) v ∧ Good n v ∧
      ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => S.ρ (v i) = u.val) ∧
        T.card = 2 ∧ 1 < FiniteArity.pairCharge
          (T ∪ Finset.univ.filter (fun i => S.ρ (v i) ≠ u.val))
          (fun i j => if i = j then 0 else FiniteArity.completeCharge
            (PhysicalRepresentative.adjacency V m) (PhysicalRepresentative.charge V m)
            {x | S.ρ x = u.val} (-m) (v i) (v j)) ∧
        -m < ∑ i ∈ Finset.univ.filter (fun i => S.ρ (v i) ≠ u.val),
          S.coveredCountableBoundaryCoefficient (Sum.inl u) (S.coveredCountableBoundaryLabel (v i)) := by
  have hlabel (k : S.I) (x : Ω) (hx : S.ρ x = k.val) :
      S.coveredCountableBoundaryLabel x = Sum.inl k := (S.coveredCountableBoundaryLabel_eq_inl_iff k x).mpr hx
  have hind (k : S.I) : ∀ p : Ω × Ω, S.ρ p.1 = k.val → S.ρ p.2 = k.val →
      adjacencyKernel V p.1 p.2 = 0 := by
    intro p hx hy
    change V.moment CappedColor.adjacency p = 0
    rw [(hmom p).1, hlabel k p.1 hx, hlabel k p.2 hy]
    simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph]
  have hbody : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      chargeKernel V p.1 p.2 ≤ 0 := by
    filter_upwards with p hx hy
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    exact S.coveredCountableBoundaryCoefficient_nonpositive r hzero _ _
      (fun he => hx ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.1).mp he))
      (fun he => hy ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.2).mp he))
  have hdisj : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hD := (S.hfibers u.val u.property).1
  have hindD : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = u.val}).prod
      (μ.restrict {x | S.ρ x = u.val}), adjacencyKernel V p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hD.prod hD)).mpr
    exact Eventually.of_forall (fun p hp => hind u p hp.1 hp.2)
  have hrow : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → chargeKernel V p.1 p.2 =
      S.coveredCountableBoundaryCoefficient (Sum.inl u) (S.coveredCountableBoundaryLabel p.2) := by
    filter_upwards with p hx
    change V.moment CappedColor.charge p = _
    rw [(hmom p).2, hlabel u p.1 hx]
  simpa only [mem_ofPred_eq] using exists_two_copy_witness_of_independent V hV hd hgap
    {x | S.ρ x = r.val} {x | S.ρ x = u.val} hdisj hD
    (S.hfibers u.val u.property).2.1 hindD (Eventually.of_forall (hind r)) hbody
    (fun y => S.coveredCountableBoundaryCoefficient (Sum.inl u) (S.coveredCountableBoundaryLabel y)) hrow hell Good hGood

end Erdos1017.CappedModel.SelectedHighLowStructure
