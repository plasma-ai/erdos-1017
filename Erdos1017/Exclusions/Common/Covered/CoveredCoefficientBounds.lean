module

public import Erdos1017.Exclusions.Common.Covered.CoveredConditionalRepeat
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredCopyBonuses

/-!
# Bounds on the covered conditional coefficients

The conditional coefficients `coveredCoefficient` stay in the capped charge box,
are symmetric, keep the strict star floor on whole fibers, are nonpositive on
every exterior block by the zero-body sign, and keep the strict half-delta
penalty on joined exterior blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem integral_gt_of_ae_gt {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] (f : α → ℝ) (hf : Integrable f ν)
    (a : ℝ) (hgt : ∀ᵐ x ∂ν, a < f x) : a < ∫ x, f x ∂ν := by
  have hi : Integrable (fun x => f x - a) ν := hf.sub (integrable_const a)
  have hpos : ∀ᵐ x ∂ν, 0 < f x - a := hgt.mono (fun _ h => sub_pos.mpr h)
  by_contra hnot
  have hzero : (∫ x, f x - a ∂ν) = 0 := by
    have hnonneg := integral_nonneg_of_ae (hpos.mono (fun _ h => h.le))
    rw [integral_sub hf (integrable_const a), integral_const, probReal_univ,
      one_smul] at hnonneg ⊢
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hpos.mono (fun _ h => h.le)) hi).mp hzero
  obtain ⟨x, hx, he⟩ := (hpos.and hz).exists
  exact (ne_of_gt hx) he

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

omit [IsProbabilityMeasure μ] in
private theorem raw_charge_mem (W : Model Ω μ) (x y : Ω) :
    chargeKernel W x y ∈ Icc (-3 : ℝ) 1 := by
  have ha := adjacency_moment_mem W (x, y)
  have hlo := neg_three_adjacency_moment_le_charge W (x, y)
  have hhi := charge_moment_le_adjacency W (x, y)
  change W.moment CappedColor.charge (x, y) ∈ Icc (-3 : ℝ) 1
  constructor <;> linarith [ha.1, ha.2]

private theorem conditional_charge_integrable (S : SelectedHighLowStructure W m)
    (a : S.I) (i j : S.I ⊕ Bool) :
    Integrable (Function.uncurry (chargeKernel W))
      ((cond μ (S.coveredLabel a ⁻¹' {i})).prod (cond μ (S.coveredLabel a ⁻¹' {j}))) := by
  apply Integrable.of_bound
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).aestronglyMeasurable 3
  exact Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(raw_charge_mem W p.1 p.2).1,
      (raw_charge_mem W p.1 p.2).2.trans (by norm_num)⟩)

private theorem ae_conditional_labels (S : SelectedHighLowStructure W m) (a : S.I)
    (i j : S.I ⊕ Bool) :
    ∀ᵐ p ∂(cond μ (S.coveredLabel a ⁻¹' {i})).prod (cond μ (S.coveredLabel a ⁻¹' {j})),
      S.coveredLabel a p.1 = i ∧ S.coveredLabel a p.2 = j := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  have hi : MeasurableSet (S.coveredLabel a ⁻¹' {i}) :=
    (S.measurable_coveredLabel a) (measurableSet_singleton i)
  have hj : MeasurableSet (S.coveredLabel a ⁻¹' {j}) :=
    (S.measurable_coveredLabel a) (measurableSet_singleton j)
  exact (Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem hi)).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem hj))

/-- Literal original conditional coefficients retain the actual capped
charge box on every positive original label fiber. -/
theorem coveredCoefficient_mem (S : SelectedHighLowStructure W m) (a : S.I)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i j : S.I ⊕ Bool) :
    S.coveredCoefficient a i j ∈ Icc (-3 : ℝ) 1 := by
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE j).ne'
  have hi := conditional_charge_integrable S a i j
  constructor
  · have h := integral_mono_ae (integrable_const (-3 : ℝ)) hi
      (Eventually.of_forall (fun p => (raw_charge_mem W p.1 p.2).1))
    simp only [integral_const, probReal_univ, one_smul] at h
    unfold coveredCoefficient FiniteArity.regionPairCharge
    dsimp only [Function.uncurry] at h ⊢
    linarith
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun p => (raw_charge_mem W p.1 p.2).2))
    simp only [integral_const, probReal_univ, one_smul] at h
    unfold coveredCoefficient FiniteArity.regionPairCharge
    dsimp only [Function.uncurry] at h ⊢
    linarith

/-- Original AE kernel symmetry suffices for exact symmetry of every
literal conditional coefficient; no pointwise representative is assumed. -/
theorem coveredCoefficient_symm (S : SelectedHighLowStructure W m) (a : S.I)
    (i j : S.I ⊕ Bool) : S.coveredCoefficient a i j = S.coveredCoefficient a j i := by
  unfold coveredCoefficient FiniteArity.regionPairCharge
  rw [← integral_prod_swap (fun p : Ω × Ω => chargeKernel W p.1 p.2)]
  apply integral_congr_ae
  exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
    (W.moment_symm CappedColor.charge)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The strict original star floor survives genuine independent
conditioning on the two positive original whole fibers. -/
theorem coveredCoefficient_root_atom_gt (S : SelectedHighLowStructure W m)
    (r a u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    -m < S.coveredCoefficient a (Sum.inl r) (Sum.inl u) := by
  let ν := (cond μ (S.coveredLabel a ⁻¹' {Sum.inl r})).prod
    (cond μ (S.coveredLabel a ⁻¹' {Sum.inl u}))
  have hfr := S.coveredLabel_fiber_inl a r
  have hfu := S.coveredLabel_fiber_inl a u
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {Sum.inl r})) :=
    cond_isProbabilityMeasure (by rw [hfr]; exact (S.hfibers r.val r.property).2.1.ne')
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {Sum.inl u})) :=
    cond_isProbabilityMeasure (by rw [hfu]; exact (S.hfibers u.val u.property).2.1.ne')
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hfloor := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
    (S.ae_rootChargeRow_gt_of_zero_body r u hru hW hd hgap hzero)
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      -m < chargeKernel W p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support,
      Measure.quasiMeasurePreserving_snd.ae hfloor] with p hr hy hf hx hu
    have he := hr hx
    rw [hy] at he
    rw [he]
    exact hf hu
  have hgt : ∀ᵐ p ∂ν, -m < chargeKernel W p.1 p.2 := by
    have hmr : MeasurableSet (S.coveredLabel a ⁻¹' {Sum.inl r}) := by
      rw [hfr]
      exact (S.hfibers r.val r.property).1
    have hmu : MeasurableSet (S.coveredLabel a ⁻¹' {Sum.inl u}) := by
      rw [hfu]
      exact (S.hfibers u.val u.property).1
    filter_upwards [hac.ae_le hpair,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem hmr),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem hmu)] with p hp hx hy
    exact hp ((S.coveredLabel_eq_inl_iff a r p.1).mp hx)
      ((S.coveredLabel_eq_inl_iff a u p.2).mp hy)
  exact integral_gt_of_ae_gt (Function.uncurry (chargeKernel W))
    (conditional_charge_integrable S a (Sum.inl r) (Sum.inl u)) (-m) hgt

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Averaging the original zero-body sign gives actual nonpositive
charges on every exterior label block, including absent graph blocks. -/
theorem coveredCoefficient_nonpositive (S : SelectedHighLowStructure W m)
    (r a : S.I)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (i j : S.I ⊕ Bool) (hi : i ≠ Sum.inl r) (hj : j ≠ Sum.inl r) :
    S.coveredCoefficient a i j ≤ 0 := by
  have hac : (cond μ (S.coveredLabel a ⁻¹' {i})).prod
      (cond μ (S.coveredLabel a ⁻¹' {j})) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  apply integral_nonpos_of_ae
  filter_upwards [hac.ae_le (S.zero_body_ae_charge_nonpositive r hzero),
    ae_conditional_labels S a i j] with p hp hlabels
  apply hp
  · intro hx
    exact hi (hlabels.1.symm.trans ((S.coveredLabel_eq_inl_iff a r p.1).mpr hx))
  · intro hy
    exact hj (hlabels.2.symm.trans ((S.coveredLabel_eq_inl_iff a r p.2).mpr hy))

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Every genuine joined exterior conditional block retains the strict
half-delta penalty, proved by its actual original pair law and copy bonus. -/
theorem coveredCoefficient_penalty_gt_half_delta (S : SelectedHighLowStructure W m)
    (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (i j : S.I ⊕ Bool) (hi : i ≠ Sum.inl r) (hj : j ≠ Sum.inl r)
    (hjoined : S.coveredGraph r a i j = true) :
    (1 + m) / 2 < -S.coveredCoefficient a i j := by
  let ν := (cond μ (S.coveredLabel a ⁻¹' {i})).prod (cond μ (S.coveredLabel a ⁻¹' {j}))
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {i})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE i).ne'
  let : IsProbabilityMeasure (cond μ (S.coveredLabel a ⁻¹' {j})) :=
    cond_isProbabilityMeasure (S.coveredLabel_fibers_positive a hR hE j).ne'
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hgt : ∀ᵐ p ∂ν, (1 + m) / 2 < -chargeKernel W p.1 p.2 := by
    filter_upwards [hac.ae_le (S.ae_body_penalty_gt_half_delta_of_zero_body r hW hd hgap hzero hratio),
      hac.ae_le (S.ae_covered_graph r a hW hd hgap hpair hzero),
      ae_conditional_labels S a i j] with p hp hg hlabels
    have hx : S.ρ p.1 ≠ r.val := fun he =>
      hi (hlabels.1.symm.trans ((S.coveredLabel_eq_inl_iff a r p.1).mpr he))
    have hy : S.ρ p.2 ≠ r.val := fun he =>
      hj (hlabels.2.symm.trans ((S.coveredLabel_eq_inl_iff a r p.2).mpr he))
    have hG : adjacencyKernel W p.1 p.2 = 1 := by
      rw [hg, hlabels.1, hlabels.2, hjoined]
      rfl
    exact hp hx hy hG
  have h := integral_gt_of_ae_gt (fun p : Ω × Ω => -chargeKernel W p.1 p.2)
    (conditional_charge_integrable S a i j).neg ((1 + m) / 2) hgt
  rw [integral_neg] at h
  exact h

end Erdos1017.CappedModel.SelectedHighLowStructure
