module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedCommonNeighbors
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedHeadScore
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence

/-!
# Common-neighbor mass of a saturated pair

Common neighbors of a saturated atom pair spend at least `1 + m` of the
integrated saturated-head deficit per unit of mass, and joined whole blocks put
the entire atom into the common-neighbor budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

private theorem row_pos_on_joined_atom (S : SelectedHighLowStructure W m) (r k : S.I)
    (hjoined : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, 0 < r.val x := by
  have hIr := S.hfibers r.val r.property
  have hIk := S.hfibers k.val k.property
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hjoined
  have hreverse : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = k.val →
      adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [hswap, adjacencyKernel_symm W] with p hp hs hr hk
    exact hs.trans (hp hk hr)
  have hrows := hIr.2.2.2.rows.mono (fun _ hx => hx.2.1)
  obtain ⟨x, hx, hrow, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIr.2.1.ne'
    (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hreverse)))
  filter_upwards [ae_restrict_of_ae hrow, ae_restrict_of_ae hsection,
    ae_restrict_mem hIk.1] with y hy hj hk
  have heq : (if 0 < r.val y then (1 : ℝ) else 0) = 1 := hy.symm.trans (hj hx hk)
  by_contra hn
  simp only [hn, ↓reduceIte] at heq
  norm_num at heq

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

private theorem score_region_mass_bound
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (T : Set Ω) (hT : MeasurableSet T)
    (hscore : ∀ᵐ x ∂μ.restrict T, r.val x + u.val x ≤ -2 * m) :
    (1 + m) * μ.real T ≤ 1 - m - 2 * (2 * (c - m * d)) := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hglobal := S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2
  have hraw := (ae_restrict_iff' hT).mp hscore
  have hi : (∫ x, T.indicator (fun _ => 1 + m) x ∂μ) ≤
      ∫ x, (1 - m) - (r.val x + u.val x) ∂μ := by
    apply integral_mono_ae ((integrable_const (1 + m)).indicator hT)
      ((integrable_const (1 - m)).sub (hr.add hu))
    filter_upwards [hglobal, hraw] with x hg ht
    change T.indicator (fun _ => 1 + m) x ≤ (1 - m) - (r.val x + u.val x)
    by_cases hx : x ∈ T
    · rw [indicator_of_mem hx]
      linarith [ht hx]
    · rw [indicator_of_notMem hx]
      linarith
  have hsub := integral_sub (integrable_const (1 - m)) (hr.add hu)
  simp only [Pi.add_apply] at hsub
  rw [integral_indicator hT, setIntegral_const, hsub, integral_add hr hu,
    S.row_integral_of_stationary r hW, S.row_integral_of_stationary u hW] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  nlinarith

/-- Original common neighbors spend at least `1+m` of the integrated
saturated-head deficit per unit of original mass. -/
theorem IsSaturatedAtomPair.common_neighbor_mass_bound
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (1 + m) * μ.real {x | 0 < r.val x ∧ 0 < u.val x} ≤
      1 - m - 2 * (2 * (c - m * d)) := by
  have hT : MeasurableSet {x | 0 < r.val x ∧ 0 < u.val x} :=
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable r.val).measurable).inter
      (measurableSet_lt measurable_const (Lp.stronglyMeasurable u.val).measurable)
  apply score_region_mass_bound hpair hW hd hgap hell _ hT
  filter_upwards [ae_restrict_of_ae (hpair.ae_common_neighbor_score_le hW hd hgap),
    ae_restrict_mem hT] with x hx ht
  exact hx ht.1 ht.2

/-- Actual joined whole blocks put the entire original atom in the
common-neighbor budget. Row positivity is derived from their original
homogeneous adjacency rows on a common good section. -/
theorem IsSaturatedAtomPair.joined_atom_mass_bound
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (k : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hr : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 1)
    (hu : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 1) :
    (1 + m) * S.originalAtomMass k ≤ 1 - m - 2 * (2 * (c - m * d)) := by
  apply score_region_mass_bound hpair hW hd hgap hell _ (S.hfibers k.val k.property).1
  filter_upwards [row_pos_on_joined_atom S r k hr, row_pos_on_joined_atom S u k hu,
    ae_restrict_of_ae (hpair.ae_common_neighbor_score_le hW hd hgap)] with x hx hy hc
  exact hc hx hy

end Erdos1017.CappedModel.SelectedHighLowStructure
