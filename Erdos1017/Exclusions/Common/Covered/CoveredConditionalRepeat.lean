module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredStationaryAveraging
public import Erdos1017.Exclusions.Common.FullIndependentCompletionWitness

/-!
# Covered coefficients and repeat witnesses

This module defines `coveredCoefficient`, the original conditional pair charges
indexed by every atom and the two diffuse region labels, and shows that
own-stationary covered averaging gives every original atom a finite two-copy
witness with conditional block incidences.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The literal original conditional pair charges, indexed by every old
atom and the two diffuse region labels. -/
def coveredCoefficient (S : SelectedHighLowStructure W m) (a : S.I)
    (i j : S.I ⊕ Bool) : ℝ :=
  FiniteArity.regionPairCharge μ (chargeKernel W)
    (fun k => S.coveredLabel a ⁻¹' {k}) i j

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Actual own-stationary covered averaging gives every original atom
its own finite two-copy witness with literal conditional block incidences.
No selected structure is manufactured for the averaged model. -/
theorem exists_covered_average_repeat_witnesses
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (hell : 1 / 2 < -m)
    (Good : ∀ n, (Fin n → Ω) → Prop)
    (hGood : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p = S.coveredCoefficient a
          (S.coveredLabel a p.1) (S.coveredLabel a p.2)) ∧
      ∀ u : S.I, r ≠ u →
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
              S.coveredCoefficient a (Sum.inl u) (S.coveredLabel a (v i)) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨V, hV, hmom, _, _⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  have hcharge (x y : Ω) : chargeKernel V x y =
      S.coveredCoefficient a (S.coveredLabel a x) (S.coveredLabel a y) := (hmom (x, y)).2
  have hlabel (u : S.I) (x : Ω) (hx : S.ρ x = u.val) :
      S.coveredLabel a x = Sum.inl u := (S.coveredLabel_eq_inl_iff a u x).mpr hx
  have hind (u : S.I) : ∀ p : Ω × Ω, S.ρ p.1 = u.val → S.ρ p.2 = u.val →
      adjacencyKernel V p.1 p.2 = 0 := by
    intro p hx hy
    change V.moment CappedColor.adjacency p = 0
    rw [(hmom p).1, hlabel u p.1 hx, hlabel u p.2 hy]
    simp [coveredGraph]
  have hbody : ∀ p : Ω × Ω, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      chargeKernel V p.1 p.2 ≤ 0 := by
    intro p hx hy
    rw [hcharge]
    let q := S.coveredLabel a
    have hqx : q p.1 ≠ Sum.inl r := fun he => hx ((S.coveredLabel_eq_inl_iff a r p.1).mp he)
    have hqy : q p.2 ≠ Sum.inl r := fun he => hy ((S.coveredLabel_eq_inl_iff a r p.2).mp he)
    have hfx : MeasurableSet (q ⁻¹' {q p.1}) :=
      (S.measurable_coveredLabel a) (measurableSet_singleton _)
    have hfy : MeasurableSet (q ⁻¹' {q p.2}) :=
      (S.measurable_coveredLabel a) (measurableSet_singleton _)
    have hac : (cond μ (q ⁻¹' {q p.1})).prod (cond μ (q ⁻¹' {q p.2})) ≪ μ.prod μ :=
      cond_absolutelyContinuous.prod cond_absolutelyContinuous
    apply integral_nonpos_of_ae
    filter_upwards [hac.ae_le (S.zero_body_ae_charge_nonpositive r hzero),
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem hfx),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem hfy)] with z hz hzx hzy
    have heqx : q z.1 = q p.1 := hzx
    have heqy : q z.2 = q p.2 := hzy
    exact hz (fun he => hqx (heqx.symm.trans (hlabel r z.1 he)))
      (fun he => hqy (heqy.symm.trans (hlabel r z.2 he)))
  refine ⟨V, hV, fun p => ⟨(hmom p).1, (hmom p).2⟩, ?_⟩
  intro u hru
  have hD := (S.hfibers u.val u.property).1
  have hpos := (S.hfibers u.val u.property).2.1
  have hdisj : Disjoint {x | S.ρ x = r.val} {x | S.ρ x = u.val} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hindD : ∀ᵐ p ∂(μ.restrict {x | S.ρ x = u.val}).prod
      (μ.restrict {x | S.ρ x = u.val}), adjacencyKernel V p.1 p.2 = 0 := by
    have hglobal : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = u.val →
        adjacencyKernel V p.1 p.2 = 0 := Eventually.of_forall (hind u)
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hD.prod hD)).mpr
    exact hglobal.mono (fun _ hp h => hp h.1 h.2)
  have hrow : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → chargeKernel V p.1 p.2 =
      S.coveredCoefficient a (Sum.inl u) (S.coveredLabel a p.2) := by
    filter_upwards with p hx
    rw [hcharge, hlabel u p.1 hx]
  simpa only [mem_ofPred_eq] using exists_two_copy_witness_of_independent V hV hd hgap
    {x | S.ρ x = r.val} {x | S.ρ x = u.val} hdisj hD hpos hindD
    (Eventually.of_forall (hind r)) (Eventually.of_forall hbody)
    (fun y => S.coveredCoefficient a (Sum.inl u) (S.coveredLabel a y)) hrow hell Good hGood

end Erdos1017.CappedModel.SelectedHighLowStructure
