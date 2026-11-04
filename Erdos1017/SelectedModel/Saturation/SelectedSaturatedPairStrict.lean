module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedHeadScore
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairDegree

/-!
# Strict positivity of the saturated-pair gap

The saturated-pair deficit is strictly positive (`gap_pos`): equality would make
the two-head direction a null vector of the shifted operator and force both
adjacency variations to vanish. The resulting degree bound needs no
positive-energy premise and is used in the missing-score and deficit-tangent
modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r u : S.I}

theorem gap_nonnegative (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    0 ≤ 1 - m - 2 * (2 * (c - m * d)) := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hscore := S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2
  have hi := integral_mono_ae (hr.add hu) (integrable_const (1 - m)) hscore
  change (∫ x, r.val x + u.val x ∂μ) ≤ ∫ _ : Ω, 1 - m ∂μ at hi
  rw [integral_add hr hu, S.row_integral_of_stationary r hW,
    S.row_integral_of_stationary u hW] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

/-- Equality in the actual saturated score bound would make the original
bounded two-head direction a genuine null vector of the shifted operator. -/
theorem direction_null_of_gap_zero (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hzero : 1 - m - 2 * (2 * (c - m * d)) = 0) :
    shiftedOperator W m (S.saturatedDirection r u) = 0 := by
  let ν := 2 * (c - m * d)
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hscore := S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ (1 - m) - (r.val x + u.val x) :=
    hscore.mono (fun _ hx => sub_nonneg.mpr hx)
  have hi : Integrable (fun x => (1 - m) - (r.val x + u.val x)) μ :=
    (integrable_const (1 - m)).sub (hr.add hu)
  have hint : (∫ x, (1 - m) - (r.val x + u.val x) ∂μ) = 0 := by
    have hexp := integral_sub (integrable_const (1 - m)) (hr.add hu)
    simp only [Pi.add_apply] at hexp
    rw [hexp, integral_add hr hu,
      S.row_integral_of_stationary r hW, S.row_integral_of_stationary u hW]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hint
  have hvec : r.val + u.val = (2 * ν) • Lp.const 2 μ (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [heq, Lp.coeFn_add r.val u.val,
      Lp.coeFn_smul (2 * ν) (Lp.const 2 μ (1 : ℝ)), Lp.coeFn_const 2 μ (1 : ℝ)]
      with x hx ha hs hc
    rw [ha, hs]
    change r.val x + u.val x = (2 * ν) * (Lp.const 2 μ (1 : ℝ)) x
    rw [hc]
    change (1 - m) - (r.val x + u.val x) = 0 at hx
    change r.val x + u.val x = (2 * ν) * 1
    dsimp only [ν]
    linarith
  rw [S.shiftedOperator_saturatedDirection r u hW]
  change r.val + u.val - (2 * ν) • Lp.const 2 μ (1 : ℝ) = 0
  rw [hvec, sub_self]

/-- Actual full optimality and its own positive eigenvector pay both
adjacency null identities; regularity is derived from the strict gap. -/
theorem adjacency_null_of_gap_zero (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hzero : 1 - m - 2 * (2 * (c - m * d)) = 0) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.saturatedDirection r u⟫ = 0 ∧
      ⟪adjacencyOperator W (S.saturatedDirection r u), S.saturatedDirection r u⟫ = 0 := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hnull := hpair.direction_null_of_gap_zero hW hd hgap hell hzero
  exact (full_null_vector_density_rigidity_of_positive_eigenvector W hW.full hopt m _
    hs.stationary_pos hW.stationary hs.regular w hw hmean σ hσ heigen
    (S.saturatedDirection r u) (S.saturatedDirection_bounded r u) hnull).2

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem inner_eq_integral_mul (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)

/-- The original saturated-pair deficit is strictly positive. Equality
would force both original adjacency variations to vanish, contradicting
the actual quarter-density two-head identity. -/
theorem gap_pos (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    0 < 1 - m - 2 * (2 * (c - m * d)) := by
  by_contra hnot
  have hzero : 1 - m - 2 * (2 * (c - m * d)) = 0 :=
    le_antisymm (le_of_not_gt hnot) (hpair.gap_nonnegative hW hd hgap hell)
  obtain ⟨hlinear, hquadratic⟩ := hpair.adjacency_null_of_gap_zero hW hd hgap hell hzero
  rw [inner_eq_integral_mul, hpair.adjacency_first_variation hW] at hlinear
  have henergy := hpair.adjacency_energy hW
  rw [hquadratic] at henergy
  linarith [hd.1]

theorem shifted_energy_pos (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    0 < ⟪shiftedOperator W m (S.saturatedDirection r u), S.saturatedDirection r u⟫ := by
  rw [hpair.shifted_energy hW]
  exact mul_pos (by norm_num) (hpair.gap_pos hW hd hgap hell)

/-- No positive-energy or degree-sign premise remains in this actual
saturated-pair degree bound. -/
theorem degree_sum_lt_four_density_of_multiplier_lt_one (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    wholeRowDegree r.val + wholeRowDegree u.val < 4 * d :=
  hpair.degree_sum_lt_four_density hW hd hgap (hpair.shifted_energy_pos hW hd hgap hell)

theorem degree_inner_neg (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.saturatedDirection r u⟫ < 0 := by
  rw [inner_eq_integral_mul, hpair.adjacency_first_variation hW]
  linarith [hpair.degree_sum_lt_four_density_of_multiplier_lt_one hW hd hgap hell]

end Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair
