module

public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientBounds

/-!
# Clique tests for the covered coefficients

Every original-label clique obeys the averaged charge test of
`coveredCoefficient` pointwise at every order, with repeated diffuse labels
sampled independently, so the conditional triangle inequality follows even for
countably many atoms, and strict support places every positive joined block
above the model's own `m`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Every literal original-label clique obeys its averaged charge test
pointwise at every order. Repeated diffuse labels use fresh independent
conditional samples, not a repeated physical point. -/
theorem coveredCoefficient_tuple_le_one (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    {n : ℕ} (v : Fin n → S.I ⊕ Bool) (hv : FiniteArity.TupleClique (S.coveredGraph r a) v) :
    FiniteArity.tupleCharge (S.coveredCoefficient a) v ≤ 1 := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hgraph : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) := by
    filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with p hg hp
    change W.moment CappedColor.adjacency p = _ at hg
    have he := hp.symm.trans hg
    cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
      cases hH : S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) <;>
      simp_all [A]
  have ht := FiniteArity.conditional_clique_average_le_one
    (fun i : Fin n => S.coveredLabel a ⁻¹' {v i})
    (fun i => (S.measurable_coveredLabel a) (measurableSet_singleton (v i)))
    (fun i => S.coveredLabel_fibers_positive a hR hE (v i)) A Y
    (PhysicalRepresentative.measurable_charge W m) 3 (PhysicalRepresentative.charge_bound W m)
    (PhysicalRepresentative.full_feasible W hW.full m hs hW.deterministic n)
    (fun i j hij => hgraph.mono (fun p hp hx hy => by
      change S.coveredLabel a p.1 = v i at hx
      change S.coveredLabel a p.2 = v j at hy
      rw [hp, hx, hy]
      exact hv i j hij))
  have heq : (fun i j : Fin n => if i = j then 0 else S.coveredCoefficient a (v i) (v j)) =
      (fun i j => if i = j then 0 else ∫ p, Y p.1 p.2
        ∂(cond μ (S.coveredLabel a ⁻¹' {v i})).prod (cond μ (S.coveredLabel a ⁻¹' {v j}))) := by
    funext i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false, coveredCoefficient, FiniteArity.regionPairCharge]
      apply integral_congr_ae
      exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        ((PhysicalRepresentative.charge_ae_eq W m hs).mono (fun _ h => h.symm))
  change FiniteArity.pairCharge Finset.univ
    (fun i j : Fin n => if i = j then 0 else S.coveredCoefficient a (v i) (v j)) ≤ 1
  rw [heq]
  exact ht

/-- The original conditional triangle is a consequence of the actual
all-order label tests, even for a countably infinite old atom family. -/
theorem coveredCoefficient_triangle (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i j k : S.I ⊕ Bool)
    (hij : S.coveredGraph r a i j = true) (hik : S.coveredGraph r a i k = true)
    (hjk : S.coveredGraph r a j k = true) :
    S.coveredCoefficient a i j + S.coveredCoefficient a i k + S.coveredCoefficient a j k ≤ 1 := by
  have hclique : FiniteArity.TupleClique (S.coveredGraph r a) ![i, j, k] := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp at * <;>
      first | exact hij | exact hik | exact hjk |
        simpa only [S.coveredGraph_symm r a] using hij |
        simpa only [S.coveredGraph_symm r a] using hik |
        simpa only [S.coveredGraph_symm r a] using hjk
  have ht := S.coveredCoefficient_tuple_le_one r a hW hd hgap hpair hzero hR hE
    ![i, j, k] hclique
  have heq : FiniteArity.tupleCharge (S.coveredCoefficient a) ![i, j, k] =
      S.coveredCoefficient a i j + S.coveredCoefficient a i k + S.coveredCoefficient a j k := by
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, S.coveredCoefficient_symm a j i,
      S.coveredCoefficient_symm a k i, S.coveredCoefficient_symm a k j]
    ring
  rwa [heq] at ht

/-- Actual strict support of the independently constructed own averaged
record puts every positive joined conditional block above its own m. -/
theorem coveredCoefficient_present_gt_m (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i j : S.I ⊕ Bool)
    (hjoined : S.coveredGraph r a i j = true) : m < S.coveredCoefficient a i j := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨V, hV, hmom, _, _⟩ :=
    S.exists_covered_stationary_average r a hW hd hgap hpair hzero hR hE
  let ν := (cond μ (S.coveredLabel a ⁻¹' {i})).prod (cond μ (S.coveredLabel a ⁻¹' {j}))
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE j).ne'
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hlabels : ∀ᵐ p ∂ν, S.coveredLabel a p.1 = i ∧ S.coveredLabel a p.2 = j :=
    (Measure.quasiMeasurePreserving_fst.ae
      (ae_cond_mem ((S.measurable_coveredLabel a) (measurableSet_singleton i)))).and
      (Measure.quasiMeasurePreserving_snd.ae
        (ae_cond_mem ((S.measurable_coveredLabel a) (measurableSet_singleton j))))
  obtain ⟨p, hp, hstrict⟩ := (hlabels.and (hac.ae_le (hV.strict_gap_structure hd hgap).strict_support)).exists
  have hG : V.moment CappedColor.adjacency p = 1 := by
    rw [(hmom p).1, hp.1, hp.2, hjoined]
    rfl
  have hM : 0 < shiftedMoment V m p := by
    by_contra hnot
    rw [ite_eq_right hnot, hG] at hstrict
    norm_num at hstrict
  rw [shiftedMoment_eq, hG, (hmom p).2] at hM
  change 0 < S.coveredCoefficient a (S.coveredLabel a p.1) (S.coveredLabel a p.2) - m * 1 at hM
  rw [hp.1, hp.2] at hM
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
