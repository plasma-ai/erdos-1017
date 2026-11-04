module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurData
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairStrict

/-!
# Deficit tangents of atoms in the partner hole

The normalized physical deficit on a positive whole atom equals the shifted
Schur deficit when the universal root is adjacent to it, and a positive whole
atom in the partner's hole obeys the bounded degree-tangent deficit inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The bounded degree tangent gives a deficit bound for a genuine
shifted-zero partner-to-third-atom block. The geometric terminal below
derives that block and both strict degree signs. -/
private theorem atomic_schur_tangent
    (S : SelectedHighLowStructure W m) (r p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r p)
    (hzero : S.headPairing p j = 0)
    (ht : wholeRowDegree p.val < wholeRowDegree j.val)
    (hv0 : wholeRowDegree r.val + wholeRowDegree p.val < 4 * d) :
    (1 - m - 4 * (c - m * d)) *
        (wholeRowDegree j.val - wholeRowDegree p.val) /
        (4 * d - wholeRowDegree r.val - wholeRowDegree p.val) ≤
      (1 - m) - S.headPairing r j := by
  let a := S.normalizedHead r
  let b := S.normalizedHead p
  let z := S.normalizedHead j
  let o := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W o
  let B := schurForm W m
  let f := S.saturatedDirection r p
  let w := b - z
  let t := wholeRowDegree j.val - wholeRowDegree p.val
  let v0 := 4 * d - wholeRowDegree r.val - wholeRowDegree p.val
  let v := f - (v0 / t) • w
  have htpos : 0 < t := sub_pos.mpr ht
  have hv0pos : 0 < v0 := by dsimp [v0]; linarith
  have hsym (x y : Lp ℝ 2 μ) : B x y = B y x := schurForm_symm x y
  have haa : B a a = 0 := S.schurForm_head_self r
  have hbb : B b b = 0 := S.schurForm_head_self p
  have hzz : B z z = 0 := S.schurForm_head_self j
  have hab : B a b = 1 - m := by
    change ⟪shiftedOperator W m a, b⟫ = 1 - m
    rw [S.operator_normalizedHead r, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers p.val p.property).2.1 r.val (1 - m) hpair.row_on_other
  have hbz : B b z = 0 := hzero
  have hzb : B z b = 0 := (hsym z b).trans hbz
  have hba : B b a = 1 - m := (hsym b a).trans hab
  have hbe : B b o = 2 * (c - m * d) := by
    rw [hsym b o]
    exact S.schurForm_constant_head p hW
  have hze : B z o = 2 * (c - m * d) := by
    rw [hsym z o]
    exact S.schurForm_constant_head j hW
  have hob : B o b = 2 * (c - m * d) := (hsym o b).trans hbe
  have hoz : B o z = 2 * (c - m * d) := (hsym o z).trans hze
  have hff : B f f = 2 * (1 - m - 4 * (c - m * d)) := by
    change ⟪shiftedOperator W m f, f⟫ = _
    convert hpair.shifted_energy hW using 1; ring
  have hww : B w w = 0 := by
    dsimp only [w]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hbb, hbz, hzb, hzz]
    ring
  have hfw : B f w = (1 - m) - B a z := by
    change B (a + b - (2 : ℝ) • o) (b - z) = _
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hab, hbb, hbz, hob, hoz]
    ring
  have hwf : B w f = B f w := hsym w f
  have hfmean : (∫ x, f x ∂μ) = 0 := S.saturatedDirection_integral r p
  have hwmean : (∫ x, w x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    change ⟪o, b - z⟫ = 0
    rw [inner_sub_right]
    have hbo : ⟪o, b⟫ = 1 := by
      rw [KernelOperator.inner_constant_one]
      exact KernelOperator.normalizedSetL2_integral _ _
        (S.hfibers p.val p.property).2.1
    have hzo : ⟪o, z⟫ = 1 := by
      rw [KernelOperator.inner_constant_one]
      exact KernelOperator.normalizedSetL2_integral _ _
        (S.hfibers j.val j.property).2.1
    rw [hbo, hzo]
    ring
  have hvmean : (∫ x, v x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    simp only [v, inner_sub_right, real_inner_smul_right,
      KernelOperator.inner_constant_one]
    rw [hfmean, hwmean]
    ring
  have hfbound : f ∈ KernelOperator.boundedL2Submodule μ :=
    S.saturatedDirection_bounded r p
  have hwbound : w ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      (KernelOperator.normalizedSetL2_bounded _ _)
      (KernelOperator.normalizedSetL2_bounded _ _)
  have hvbound : v ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem hfbound
      ((KernelOperator.boundedL2Submodule μ).smul_mem _ hwbound)
  have hdegp : ⟪g, b⟫ = wholeRowDegree p.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers p.val p.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ p.val (S.hfibers p.val p.property).2.2.2)
  have hdegj : ⟪g, z⟫ = wholeRowDegree j.val := by
    rw [real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant _ _
      (S.hfibers j.val j.property).2.1 g _
      (wholeRowFiber_degree W m S.ρ j.val (S.hfibers j.val j.property).2.2.2)
  have hwdegree : ⟪g, w⟫ = -t := by
    dsimp only [w, t]
    rw [inner_sub_right, hdegp, hdegj]
    ring
  have hfdegree : ⟪g, f⟫ = -v0 := by
    have heq : ⟪g, f⟫ = ∫ x, g x * f x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring)
    rw [heq]
    have hfirst := hpair.adjacency_first_variation hW
    change (∫ x, g x * f x ∂μ) =
      wholeRowDegree r.val + wholeRowDegree p.val - 4 * d at hfirst
    dsimp [v0]
    linarith
  have hvdegree : ⟪g, v⟫ = 0 := by
    rw [show v = f - (v0 / t) • w from rfl,
      inner_sub_right, real_inner_smul_right, hfdegree, hwdegree]
    have hcancel : (v0 / t) * t = v0 := by field_simp
    linarith
  have hQ : B v v ≤ 0 :=
    hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
      v hvbound hvmean hvdegree
  have hQexp : B v v = 2 * (1 - m - 4 * (c - m * d)) -
      2 * (v0 / t) * ((1 - m) - B a z) := by
    dsimp only [v]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hff, hww, hwf, hfw]
    ring
  have hbound : (1 - m - 4 * (c - m * d)) * t / v0 ≤
      (1 - m) - B a z := by
    rw [hQexp] at hQ
    have hmul : (1 - m - 4 * (c - m * d)) * t ≤
        ((1 - m) - B a z) * v0 := by
      have hstep : 1 - m - 4 * (c - m * d) ≤
          (v0 / t) * ((1 - m) - B a z) := by linarith
      calc
        _ ≤ ((v0 / t) * ((1 - m) - B a z)) * t :=
          mul_le_mul_of_nonneg_right hstep htpos.le
        _ = ((1 - m) - B a z) * v0 := by
          field_simp
    exact (div_le_iff₀ hv0pos).mpr hmul
  exact hbound

/-- The original physical root-charge average is the original whole
shifted row plus its adjacency price, on the same probability law. -/
private theorem ae_universal_charge_row_eq_shifted_plus
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y =
      r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  have hIpos : 0 < μ I := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict I,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I →
      PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2 ∧
      PhysicalRepresentative.charge W m p.1 p.2 = chargeKernel W p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hr hp hi
    exact ⟨hr hi, hp⟩
  obtain ⟨x, hxI, hxrows, hxpair⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hIpos.ne' (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)))
  filter_upwards [hxrows, hxpair] with y hy hp
  exact (hp hxI).1.symm.trans ((hp hxI).2.trans hy)

/-- The normalized physical deficit on a positive original whole atom
equals the actual shifted Schur deficit when the universal root is
adjacent to that atom. -/
theorem universal_root_deficit_average_eq_schur
    (S : SelectedHighLowStructure W m) (r p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hj : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) :
    (μ.real {x | S.ρ x = j.val})⁻¹ *
        ∫ x in {x | S.ρ x = j.val}, S.universalRootDeficit r x ∂μ =
      (1 - m) - S.headPairing r j := by
  let J : Set Ω := {x | S.ρ x = j.val}
  have hJ : MeasurableSet J := (S.hfibers j.val j.property).1
  have hJpos : 0 < μ.real J := ENNReal.toReal_pos
    (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ J)
  have hJnotr : ∀ᵐ x ∂μ.restrict J, S.ρ x ≠ r.val := by
    filter_upwards [hj, ae_restrict_mem hJ] with x hx hJx hEq
    exact hx (Or.inl (Or.inl hEq))
  have hrowpos : ∀ᵐ x ∂μ.restrict J, 0 < r.val x := by
    filter_upwards [ae_restrict_of_ae (S.ae_universal_rootNeighborhood_iff r hW hd hgap hN),
      hJnotr] with x hx hne
    exact (hx.mpr hne).2
  have hcharge : ∀ᵐ x ∂μ.restrict J,
      S.rootChargeRow r x = r.val x + m := by
    filter_upwards [ae_restrict_of_ae
      (S.ae_universal_charge_row_eq_shifted_plus r hW hd hgap), hrowpos]
      with x hx hpos
    simpa only [ite_eq_left hpos, mul_one] using hx
  have hdeficit : ∀ᵐ x ∂μ.restrict J,
      S.universalRootDeficit r x = (1 - m) - r.val x :=
    hcharge.mono (fun _ hx => by simp [universalRootDeficit, hx]; ring)
  have hrint : Integrable (r.val : Ω → ℝ) (μ.restrict J) :=
    ((Lp.memLp r.val).integrable (by norm_num)).integrableOn
  have hint : (∫ x in J, S.universalRootDeficit r x ∂μ) =
      μ.real J * (1 - m) - ∫ x in J, r.val x ∂μ := by
    rw [integral_congr_ae hdeficit]
    rw [integral_sub (integrable_const _) hrint,
      setIntegral_const, smul_eq_mul]
  have hpairing : S.headPairing r j =
      (μ.real J)⁻¹ * ∫ x in J, r.val x ∂μ := by
    change ⟪shiftedOperator W m (S.normalizedHead r), S.normalizedHead j⟫ = _
    rw [S.operator_normalizedHead r, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner J hJ r.val
  change (μ.real J)⁻¹ * (∫ x in J, S.universalRootDeficit r x ∂μ) =
    (1 - m) - S.headPairing r j
  rw [hint, hpairing]
  field_simp [ne_of_gt hJpos]

/-- The actual positive whole atom in the partner's entire hole obeys
the original bounded degree-tangent deficit inequality. All degree signs,
the missing cross block, and the physical-charge normalization are derived
from the same selected model. -/
theorem IsSaturatedAtomPair.universal_atomic_deficit_tangent
    {S : SelectedHighLowStructure W m} {r p : S.I}
    (hpair : S.IsSaturatedAtomPair r p) (j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hj : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) :
    0 < wholeRowDegree j.val - wholeRowDegree p.val ∧
      0 < 4 * d - wholeRowDegree r.val - wholeRowDegree p.val ∧
      (1 - m - 4 * (c - m * d)) *
          (wholeRowDegree j.val - wholeRowDegree p.val) /
          (4 * d - wholeRowDegree r.val - wholeRowDegree p.val) ≤
        (μ.real {x | S.ρ x = j.val})⁻¹ *
          ∫ x in {x | S.ρ x = j.val}, S.universalRootDeficit r x ∂μ := by
  let J : Set Ω := {x | S.ρ x = j.val}
  let H := S.universalPartnerHoleRegion r p
  have hJ : MeasurableSet J := (S.hfibers j.val j.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hJpos : 0 < μ J := (S.hfibers j.val j.property).2.1
  have hzeroH : ∀ᵐ x ∂μ, x ∈ H → p.val x = 0 :=
    (ae_restrict_iff' hH).mp (S.ae_partner_row_zero_on_universalHole r p hW)
  have hjglobal : ∀ᵐ x ∂μ, x ∈ J → x ∈ H := (ae_restrict_iff' hJ).mp hj
  have hJzero : ∀ᵐ x ∂μ.restrict J, p.val x = 0 :=
    (ae_restrict_iff' hJ).mpr
      ((hzeroH.and hjglobal).mono (fun x hx hxJ => hx.1 (hx.2 hxJ)))
  have hzero : S.headPairing p j = 0 := by
    change ⟪shiftedOperator W m (S.normalizedHead p), S.normalizedHead j⟫ = 0
    rw [S.operator_normalizedHead p, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant J hJ hJpos p.val 0 hJzero
  have ht := S.universalPartnerHole_atom_degree_gt r p j hpair hW hd hgap hell hj
  have hv0 := hpair.degree_sum_lt_four_density_of_multiplier_lt_one hW hd hgap hell
  have hschur := atomic_schur_tangent S r p j hW hd hgap hpair hzero ht hv0
  have hphysical := S.universal_root_deficit_average_eq_schur r p j hW hd hgap hN hj
  refine ⟨sub_pos.mpr ht, ?_, ?_⟩
  · linarith
  · exact hschur.trans_eq hphysical.symm

end Erdos1017.CappedModel.SelectedHighLowStructure
