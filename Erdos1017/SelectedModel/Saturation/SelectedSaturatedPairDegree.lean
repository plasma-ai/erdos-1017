module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.SelectedModel.Flows.IntegrableDensityReturn
public import Erdos1017.SelectedModel.Structure.L1KernelTangent

/-!
# Degree variation along a saturated pair

The first variation and unhalved energy of the original adjacency degree along
the normalized two-head direction of a saturated atom pair, and the degree-slope
bounds: nonpositive from positive shifted energy and the quarter-density
endpoint, strictly negative at a strict-gap full optimum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

omit [IsProbabilityMeasure μ] in
private theorem inner_eq_integral_mul (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)

/-- The original adjacency degree's first variation along the normalized
two-head direction. -/
theorem IsSaturatedAtomPair.adjacency_first_variation
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (_hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
      S.saturatedDirection r u x ∂μ) =
      wholeRowDegree r.val + wholeRowDegree u.val - 4 * d := by
  let o := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W o
  let v : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1
  let w : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = u.val}
    (S.hfibers u.val u.property).1
  have hrv : ⟪g, v⟫ = wholeRowDegree r.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers r.val r.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)
  have huw : ⟪g, w⟫ = wholeRowDegree u.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers u.val u.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ u.val (S.hfibers u.val u.property).2.2.2)
  have hgo : ⟪g, o⟫ = 2 * d := by
    change ⟪adjacencyOperator W o, o⟫ = _
    rw [← weighted_adjacency_eq, weightedPairIntegral_one]
    have hdW := hW.density_eq
    unfold density at hdW
    change (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at hdW
    linarith
  rw [← inner_eq_integral_mul, saturatedDirection]
  change ⟪g, v + w - (2 : ℝ) • o⟫ = _
  rw [inner_sub_right, inner_add_right, real_inner_smul_right, hrv, huw, hgo]
  ring

omit [IsProbabilityMeasure μ] in
private theorem two_head_energy (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : T.toLinearMap.IsSymmetric) (v w o : Lp ℝ 2 μ)
    (hv : ⟪T v, v⟫ = 0) (hw : ⟪T w, w⟫ = 0) :
    ⟪T (v + w - (2 : ℝ) • o), v + w - (2 : ℝ) • o⟫ =
      2 * ⟪T v, w⟫ - 4 * ⟪T o, v + w⟫ + 4 * ⟪T o, o⟫ := by
  have hvw : ⟪T w, v⟫ = ⟪T v, w⟫ := (hT w v).trans (real_inner_comm _ _)
  have hvo : ⟪T v, o⟫ = ⟪T o, v⟫ := (hT v o).trans (real_inner_comm _ _)
  have hwo : ⟪T w, o⟫ = ⟪T o, w⟫ := (hT w o).trans (real_inner_comm _ _)
  simp only [map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hv, hw, hvw, hvo, hwo]
  ring

/-- The original unhalved adjacency energy of the same saturated two-head
direction, with the original density and degree first variation. -/
theorem IsSaturatedAtomPair.adjacency_energy
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ⟪adjacencyOperator W (S.saturatedDirection r u), S.saturatedDirection r u⟫ =
      2 * (1 - 4 * d) -
        4 * (wholeRowDegree r.val + wholeRowDegree u.val - 4 * d) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let v : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 Ir
    (S.hfibers r.val r.property).1
  let w : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 Iu
    (S.hfibers u.val u.property).1
  let o := Lp.const 2 μ (1 : ℝ)
  let T := adjacencyOperator W
  have hv : ⟪T v, v⟫ = 0 :=
    KernelOperator.operator_inner_normalizedSetL2_eq_zero (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      Ir Ir (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).1
      (S.hfibers r.val r.property).2.2.1
  have hw : ⟪T w, w⟫ = 0 :=
    KernelOperator.operator_inner_normalizedSetL2_eq_zero (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      Iu Iu (S.hfibers u.val u.property).1 (S.hfibers u.val u.property).1
      (S.hfibers u.val u.property).2.2.1
  have hblock : ∀ᵐ p ∂(μ.restrict Ir).prod (μ.restrict Iu),
      adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) hpair.shifted_block,
      Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (S.hfibers r.val r.property).1),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem (S.hfibers u.val u.property).1)] with p hp hr hu
    exact (hp hr hu).1
  have hcross : ⟪T v, w⟫ = 1 := by
    have heq := KernelOperator.operator_inner_normalizedSetL2 (adjacencyKernel W)
      (by norm_num) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      Ir Iu (S.hfibers r.val r.property).1 (S.hfibers u.val u.property).1
    change ⟪T w, v⟫ = _ at heq
    rw [integral_congr_ae hblock, integral_const] at heq
    have hmass : ((μ.restrict Ir).prod (μ.restrict Iu)).real univ =
        μ.real Ir * μ.real Iu := by
      rw [← Set.univ_prod_univ, measureReal_prod_prod,
        measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]
    rw [hmass, smul_eq_mul, mul_one] at heq
    have hrpos : μ.real Ir ≠ 0 :=
      (ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne'
        (measure_ne_top μ Ir)).ne'
    have hupos : μ.real Iu ≠ 0 :=
      (ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne'
        (measure_ne_top μ Iu)).ne'
    have hvalue : (μ.real Ir)⁻¹ * (μ.real Iu)⁻¹ *
        (μ.real Ir * μ.real Iu) = 1 := by
      field_simp
    rw [hvalue] at heq
    exact ((adjacencyOperator_symmetric W v w).trans
      (real_inner_comm _ _)).trans heq
  have hdegree (t : S.I) :
      ⟪T o, KernelOperator.normalizedSetL2 {x | S.ρ x = t.val}
        (S.hfibers t.val t.property).1⟫ = wholeRowDegree t.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers t.val t.property).2.1 (T o) _
      (wholeRowFiber_degree W m S.ρ t.val (S.hfibers t.val t.property).2.2.2)
  have hgo : ⟪T o, o⟫ = 2 * d := by
    change ⟪adjacencyOperator W o, o⟫ = _
    rw [← weighted_adjacency_eq, weightedPairIntegral_one]
    have hdW := hW.density_eq
    unfold density at hdW
    change (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at hdW
    linarith
  change ⟪T (v + w - (2 : ℝ) • o), v + w - (2 : ℝ) • o⟫ = _
  rw [two_head_energy T (adjacencyOperator_symmetric W) v w o hv hw,
    hcross, inner_add_right, hdegree r, hdegree u, hgo]
  ring

private theorem kernelEnergy_half (K : Ω → Ω → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) (h : Lp ℝ 2 μ) :
    KernelOperator.kernelEnergy (μ := μ) K (fun x => h x / 2) =
      (1 / 4 : ℝ) * ⟪KernelOperator.operator K hB0 hK hB h, h⟫ := by
  unfold KernelOperator.kernelEnergy
  rw [KernelOperator.operator_inner K hB0 hK hB h h, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

private theorem saturatedHalf_integrable (S : SelectedHighLowStructure W m) (r u : S.I) :
    Integrable (fun x => S.saturatedDirection r u x / 2) μ :=
  ((Lp.memLp (S.saturatedDirection r u)).integrable (by norm_num)).div_const 2

private theorem saturatedHalf_integral (S : SelectedHighLowStructure W m) (r u : S.I) :
    (∫ x, S.saturatedDirection r u x / 2 ∂μ) = 0 := by
  rw [integral_div, S.saturatedDirection_integral]
  norm_num

private theorem saturatedHalf_below (S : SelectedHighLowStructure W m) (r u : S.I) :
    ∀ᵐ x ∂μ, -1 ≤ S.saturatedDirection r u x / 2 := by
  let a : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = r.val}
    (S.hfibers r.val r.property).1
  let b : Lp ℝ 2 μ := KernelOperator.normalizedSetL2 {x | S.ρ x = u.val}
    (S.hfibers u.val u.property).1
  let one : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  have ha := KernelOperator.normalizedSetL2_nonnegative (μ := μ)
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
  have hb := KernelOperator.normalizedSetL2_nonnegative (μ := μ)
    {x | S.ρ x = u.val} (S.hfibers u.val u.property).1
  filter_upwards [ha, hb, Lp.coeFn_add a b, Lp.coeFn_smul (2 : ℝ) one,
    Lp.coeFn_sub (a + b) ((2 : ℝ) • one), Lp.coeFn_const 2 μ (1 : ℝ)]
    with x hx hy hab htwo hsub hone
  change -1 ≤ ((a + b - (2 : ℝ) • one : Lp ℝ 2 μ) x) / 2
  rw [hsub, Pi.sub_apply, hab, Pi.add_apply, htwo, Pi.smul_apply, smul_eq_mul]
  change 0 ≤ a x at hx
  change 0 ≤ b x at hy
  change one x = 1 at hone
  rw [hone]
  linarith

private theorem IsSaturatedAtomPair.saturatedHalf_linear
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
      (S.saturatedDirection r u x / 2) ∂μ) =
      (wholeRowDegree r.val + wholeRowDegree u.val - 4 * d) / 2 := by
  calc
    _ = ∫ x, (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
      S.saturatedDirection r u x) / 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => by ring)
    _ = (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
      S.saturatedDirection r u x ∂μ) / 2 := by rw [integral_div]
    _ = _ := by rw [hpair.adjacency_first_variation hW]

/-- The genuine half-direction endpoint is the balanced two-atom mixture
and has original adjacency density exactly one quarter. -/
private theorem IsSaturatedAtomPair.saturatedHalf_endpoint_density
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    density (integrableTilt W (fun x => S.saturatedDirection r u x / 2)
      (saturatedHalf_integrable S r u) (saturatedHalf_integral S r u)
      (saturatedHalf_below S r u) 1 ⟨by norm_num, le_rfl⟩) = 1 / 4 := by
  have hL := hpair.saturatedHalf_linear hW
  have hQ := kernelEnergy_half (adjacencyKernel W) (by norm_num)
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
    (S.saturatedDirection r u)
  change KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W)
    (fun x => S.saturatedDirection r u x / 2) =
      (1 / 4 : ℝ) *
        ⟪adjacencyOperator W (S.saturatedDirection r u), S.saturatedDirection r u⟫ at hQ
  have hAdj := hpair.adjacency_energy hW
  have hdens := density_integrableTilt W
    (fun x => S.saturatedDirection r u x / 2)
    (saturatedHalf_integrable S r u) (saturatedHalf_integral S r u)
    (saturatedHalf_below S r u) 1 ⟨by norm_num, le_rfl⟩
  rw [hW.density_eq, hL, hQ, hAdj] at hdens
  norm_num at hdens ⊢
  linarith

private theorem IsSaturatedAtomPair.saturatedHalf_shifted_energy_pos
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (_hpair : S.IsSaturatedAtomPair r u)
    (hE : 0 < ⟪shiftedOperator W m (S.saturatedDirection r u),
      S.saturatedDirection r u⟫) :
    0 < KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (fun x => S.saturatedDirection r u x / 2) := by
  have heq := kernelEnergy_half (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    (S.saturatedDirection r u)
  change KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
    (fun x => S.saturatedDirection r u x / 2) =
      (1 / 4 : ℝ) * ⟪shiftedOperator W m (S.saturatedDirection r u),
        S.saturatedDirection r u⟫ at heq
  rw [heq]
  positivity

/-- Positive shifted energy and the actual quarter-density endpoint force
the original saturated two-head degree slope to be nonpositive. -/
theorem IsSaturatedAtomPair.degree_sum_le_four_density
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hdq : (1 / 4 : ℝ) < d)
    (hE : 0 < ⟪shiftedOperator W m (S.saturatedDirection r u),
      S.saturatedDirection r u⟫) :
    wholeRowDegree r.val + wholeRowDegree u.val ≤ 4 * d := by
  have hsign := hW.endpoint_density_sign_of_positive_energy
    (fun x => S.saturatedDirection r u x / 2)
    (saturatedHalf_integrable S r u) (saturatedHalf_integral S r u)
    (saturatedHalf_below S r u)
    (hpair.saturatedHalf_shifted_energy_pos hE)
  rw [hpair.saturatedHalf_linear hW,
    hpair.saturatedHalf_endpoint_density hW] at hsign
  by_contra hn
  have hpos : 0 < (wholeRowDegree r.val + wholeRowDegree u.val - 4 * d) / 2 := by
    have hgt := lt_of_not_ge hn
    linarith
  have hneg : (1 / 4 : ℝ) - d < 0 := by linarith
  exact (not_le_of_gt (mul_neg_of_pos_of_neg hpos hneg)) hsign

/-- At an actual strict-gap full optimum, positive shifted energy makes the
original two-head degree slope strictly negative. Regularity is derived from
the benchmark gap; the theorem assumes no tangent inequality. -/
theorem IsSaturatedAtomPair.degree_sum_lt_four_density
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hE : 0 < ⟪shiftedOperator W m (S.saturatedDirection r u),
      S.saturatedDirection r u⟫) :
    wholeRowDegree r.val + wholeRowDegree u.val < 4 * d := by
  have hle := hpair.degree_sum_le_four_density hW hd.1 hE
  by_contra hnot
  have heq : wholeRowDegree r.val + wholeRowDegree u.val = 4 * d :=
    le_antisymm hle (le_of_not_gt hnot)
  have hL := hpair.saturatedHalf_linear hW
  rw [heq] at hL
  have hLzero : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
      (S.saturatedDirection r u x / 2) ∂μ) = 0 := by
    simpa using hL
  have hnonpos := hW.integrable_tangent_nonpositive_of_strict_gap hd hgap
    (fun x => S.saturatedDirection r u x / 2)
    (saturatedHalf_integrable S r u) (saturatedHalf_integral S r u) hLzero
  exact (not_le_of_gt (hpair.saturatedHalf_shifted_energy_pos hE)) hnonpos

end Erdos1017.CappedModel.SelectedHighLowStructure
