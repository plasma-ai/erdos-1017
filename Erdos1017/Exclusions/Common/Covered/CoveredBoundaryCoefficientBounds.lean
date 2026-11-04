module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredBoundaryAverage
public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientBounds

/-!
# Bounds on the covered boundary coefficients

The boundary coefficients `coveredCountableBoundaryCoefficient` keep the
atom-atom conditional means, the charge cap, symmetry, the zero-body sign, the
whole-atom star floor, the strict `m` lower bound on positive joined blocks, the
half-delta penalty on exterior blocks and the three-label triangle constraint.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

theorem coveredCountableBoundaryLabel_fiber_inl (S : SelectedHighLowStructure W m) (u : S.I) :
    S.coveredCountableBoundaryLabel ⁻¹' {Sum.inl u} = {x | S.ρ x = u.val} := by
  ext x
  exact S.coveredCountableBoundaryLabel_eq_inl_iff u x

theorem coveredCountableBoundaryLabel_fiber_inr (S : SelectedHighLowStructure W m) :
    S.coveredCountableBoundaryLabel ⁻¹' {Sum.inr ()} = S.D := by
  ext x
  exact S.coveredCountableBoundaryLabel_eq_inr_iff x

/-- The original atom-atom conditional means do not change when the
null diffuse region is collapsed. No boundary hypothesis is needed. -/
theorem coveredCountableBoundaryCoefficient_atoms (S : SelectedHighLowStructure W m)
    (a u v : S.I) :
    S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl v) =
      S.coveredCoefficient a (Sum.inl u) (Sum.inl v) := by
  unfold coveredCountableBoundaryCoefficient coveredCoefficient FiniteArity.regionPairCharge
  dsimp only
  rw [S.coveredCountableBoundaryLabel_fiber_inl u, S.coveredCountableBoundaryLabel_fiber_inl v,
    S.coveredLabel_fiber_inl a u, S.coveredLabel_fiber_inl a v]

theorem coveredCountableBoundaryCoefficient_symm (S : SelectedHighLowStructure W m)
    (i j : S.I ⊕ Unit) :
    S.coveredCountableBoundaryCoefficient i j = S.coveredCountableBoundaryCoefficient j i := by
  unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
  rw [← integral_prod_swap (fun p : Ω × Ω => chargeKernel W p.1 p.2)]
  apply integral_congr_ae
  exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
    (W.moment_symm CappedColor.charge)

private theorem boundary_labels (S : SelectedHighLowStructure W m) (i j : S.I ⊕ Unit) :
    ∀ᵐ p ∂(cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})).prod
      (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j})),
      S.coveredCountableBoundaryLabel p.1 = i ∧ S.coveredCountableBoundaryLabel p.2 = j := by
  let : MeasurableSpace (S.I ⊕ Unit) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem
    (S.measurable_coveredCountableBoundaryLabel (measurableSet_singleton i)))).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem
      (S.measurable_coveredCountableBoundaryLabel (measurableSet_singleton j))))

private theorem boundary_charge_integrable (S : SelectedHighLowStructure W m)
    (i j : S.I ⊕ Unit) : Integrable (Function.uncurry (chargeKernel W))
      ((cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})).prod
        (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j}))) := by
  apply Integrable.of_bound
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).aestronglyMeasurable 3
  exact Eventually.of_forall (fun p => by
    have hG := adjacency_moment_mem W p
    have hlo := neg_three_adjacency_moment_le_charge W p
    have hhi := charge_moment_le_adjacency W p
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    change -3 ≤ W.moment CappedColor.charge p ∧ W.moment CappedColor.charge p ≤ 3
    constructor <;> linarith [hG.1, hG.2])

private theorem integral_gt_of_boundary_ae_gt {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] (f : α → ℝ) (hf : Integrable f ν)
    (a : ℝ) (hgt : ∀ᵐ x ∂ν, a < f x) : a < ∫ x, f x ∂ν := by
  have hi : Integrable (fun x => f x - a) ν := hf.sub (integrable_const a)
  have hp : ∀ᵐ x ∂ν, 0 < f x - a := hgt.mono (fun _ h => sub_pos.mpr h)
  by_contra hnot
  have hz : (∫ x, f x - a ∂ν) = 0 := by
    have hn := integral_nonneg_of_ae (hp.mono (fun _ h => h.le))
    rw [integral_sub hf (integrable_const a), integral_const, probReal_univ, one_smul] at hn ⊢
    linarith
  have he := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi).mp hz
  obtain ⟨x, hx, hzero⟩ := (hp.and he).exists
  exact (ne_of_gt hx) hzero

/-- The literal boundary coefficients retain the actual original cap. -/
theorem coveredCountableBoundaryCoefficient_mem (S : SelectedHighLowStructure W m)
    (hD : 0 < μ S.D) (i j : S.I ⊕ Unit) :
    S.coveredCountableBoundaryCoefficient i j ∈ Icc (-3 : ℝ) 1 := by
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD j).ne'
  have hi := boundary_charge_integrable S i j
  have hlo (p : Ω × Ω) : -3 ≤ chargeKernel W p.1 p.2 := by
    have hG := adjacency_moment_mem W p
    have h := neg_three_adjacency_moment_le_charge W p
    change -3 ≤ W.moment CappedColor.charge p
    linarith [hG.2]
  have hhi (p : Ω × Ω) : chargeKernel W p.1 p.2 ≤ 1 :=
    (charge_moment_le_adjacency W p).trans (adjacency_moment_mem W p).2
  constructor
  · have h := integral_mono_ae (integrable_const (-3 : ℝ)) hi (Eventually.of_forall hlo)
    simp only [integral_const, probReal_univ, one_smul] at h
    unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
    dsimp only [Function.uncurry] at h ⊢
    linarith
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ)) (Eventually.of_forall hhi)
    simp only [integral_const, probReal_univ, one_smul] at h
    unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
    dsimp only [Function.uncurry] at h ⊢
    linarith

/-- The original zero-body sign survives conditioning on the entire D
fiber, whether the R-null or E-null boundary is used later. -/
theorem coveredCountableBoundaryCoefficient_nonpositive (S : SelectedHighLowStructure W m)
    (r : S.I)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (i j : S.I ⊕ Unit) (hi : i ≠ Sum.inl r) (hj : j ≠ Sum.inl r) :
    S.coveredCountableBoundaryCoefficient i j ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
      (S.zero_body_ae_charge_nonpositive r hzero), boundary_labels S i j] with p hp hl
  apply hp
  · intro hx
    exact hi (hl.1.symm.trans ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.1).mpr hx))
  · intro hy
    exact hj (hl.2.symm.trans ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.2).mpr hy))

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The old whole-atom star floor is unchanged by collapsing diffuse labels. -/
theorem coveredCountableBoundaryCoefficient_root_atom_gt (S : SelectedHighLowStructure W m)
    (r a u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    -m < S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) := by
  rw [S.coveredCountableBoundaryCoefficient_atoms a r u]
  exact S.coveredCoefficient_root_atom_gt r a u hru hW hd hgap hzero

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Actual own strict support places every positive joined boundary
block above m. The own record is constructed, not transferred by fiat. -/
theorem coveredCountableBoundaryCoefficient_present_gt_m (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (i j : S.I ⊕ Unit) (hjoined : S.coveredCountableBoundaryGraph mode r a i j = true) :
    m < S.coveredCountableBoundaryCoefficient i j := by
  let : MeasurableSpace (S.I ⊕ Unit) := ⊤
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨V, hV, hmom, _, _⟩ :=
    S.exists_covered_countable_boundary_stationary_average mode r a hW hd hgap hpair hzero hD hnull
  let ν := (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})).prod
    (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j}))
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD j).ne'
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  obtain ⟨p, hp, hs⟩ := ((boundary_labels S i j).and
    (hac.ae_le (hV.strict_gap_structure hd hgap).strict_support)).exists
  have hG : V.moment CappedColor.adjacency p = 1 := by
    rw [(hmom p).1, hp.1, hp.2, hjoined]
    rfl
  have hM : 0 < shiftedMoment V m p := by
    by_contra hnot
    rw [ite_eq_right hnot, hG] at hs
    norm_num at hs
  rw [shiftedMoment_eq, hG, (hmom p).2, hp.1, hp.2] at hM
  linarith

/-- Every joined exterior boundary block has its actual strict
half-delta penalty, integrated under the original conditional pair law. -/
theorem coveredCountableBoundaryCoefficient_penalty_gt_half_delta
    (S : SelectedHighLowStructure W m) (mode : Bool) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (i j : S.I ⊕ Unit) (hi : i ≠ Sum.inl r) (hj : j ≠ Sum.inl r)
    (hjoined : S.coveredCountableBoundaryGraph mode r a i j = true) :
    (1 + m) / 2 < -S.coveredCountableBoundaryCoefficient i j := by
  let ν := (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})).prod
    (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j}))
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredCountableBoundaryLabel_fibers_positive hD j).ne'
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hgt : ∀ᵐ p ∂ν, (1 + m) / 2 < -chargeKernel W p.1 p.2 := by
    filter_upwards [hac.ae_le (S.ae_body_penalty_gt_half_delta_of_zero_body r hW hd hgap hzero hratio),
      hac.ae_le (S.ae_covered_countable_boundary_graph mode r a hW hd hgap hpair hzero hnull),
      boundary_labels S i j] with p hp hg hl
    have hx : S.ρ p.1 ≠ r.val := fun he => hi
      (hl.1.symm.trans ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.1).mpr he))
    have hy : S.ρ p.2 ≠ r.val := fun he => hj
      (hl.2.symm.trans ((S.coveredCountableBoundaryLabel_eq_inl_iff r p.2).mpr he))
    have hG : adjacencyKernel W p.1 p.2 = 1 := by
      change W.moment CappedColor.adjacency p = 1
      rw [hg, hl.1, hl.2, hjoined]
      rfl
    exact hp hx hy hG
  have h := integral_gt_of_boundary_ae_gt (fun p : Ω × Ω => -chargeKernel W p.1 p.2)
    (boundary_charge_integrable S i j).neg ((1 + m) / 2) hgt
  rw [integral_neg] at h
  exact h

/-- The actual three-label boundary constraint is a direct consequence
of independently licensed original all-order conditional tests. -/
theorem coveredCountableBoundaryCoefficient_triangle (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (i j k : S.I ⊕ Unit)
    (hij : S.coveredCountableBoundaryGraph mode r a i j = true)
    (hik : S.coveredCountableBoundaryGraph mode r a i k = true)
    (hjk : S.coveredCountableBoundaryGraph mode r a j k = true) :
    S.coveredCountableBoundaryCoefficient i j + S.coveredCountableBoundaryCoefficient i k +
      S.coveredCountableBoundaryCoefficient j k ≤ 1 := by
  have hc : FiniteArity.TupleClique (S.coveredCountableBoundaryGraph mode r a) ![i, j, k] := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp at * <;>
      first | exact hij | exact hik | exact hjk |
        simpa only [S.coveredCountableBoundaryGraph_symm mode r a] using hij |
        simpa only [S.coveredCountableBoundaryGraph_symm mode r a] using hik |
        simpa only [S.coveredCountableBoundaryGraph_symm mode r a] using hjk
  have ht := S.coveredCountableBoundaryCoefficient_tuple_le_one mode r a hW hd hgap hpair
    hzero hD hnull ![i, j, k] hc
  have heq : FiniteArity.tupleCharge S.coveredCountableBoundaryCoefficient ![i, j, k] =
      S.coveredCountableBoundaryCoefficient i j + S.coveredCountableBoundaryCoefficient i k +
      S.coveredCountableBoundaryCoefficient j k := by
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, S.coveredCountableBoundaryCoefficient_symm j i,
      S.coveredCountableBoundaryCoefficient_symm k i, S.coveredCountableBoundaryCoefficient_symm k j]
    ring
  rwa [heq] at ht

end Erdos1017.CappedModel.SelectedHighLowStructure
