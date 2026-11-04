module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedJoined
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpDiffuseCap
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpMissingCap

/-!
# Source peak of the no-saturation entry

The sharp radius is below `13/100` on the closed joined domain, and the middle
`E₂` no-saturation entry with its joined alternative excluded follows from the
model, contact, global maximum and product-null saturated set alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MiddleUnsaturatedJoinedScalar

open LowerE2Scalar

/-- The gap floor exceeds `361/6600` on the closed range `[187/1000, 1/5]`. -/
private theorem gapFloor_gt_floor {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    361 / 6600 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  unfold gapFloor
  rw [lt_div_iff₀ (by positivity)]
  unfold denominator
  norm_num at hq2
  nlinarith [hq.1]

/-- The sharp radius is below `13/100` on the whole closed joined domain:
`D_ell(A) <= D_{9/11}(1/3) = 17/297`, `gamma > 361/6600` and
`ell - 2/3 >= 5/33` give `T^2 < 4983/297000 < (13/100)^2`. -/
theorem sharp_radius_lt {q A γ T : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hA : A ∈ Icc (3 / 10 : ℝ) (1 / 3)) (hγ : gapFloor q < γ)
    (hcap : (multiplier q - 2 / 3) * T ^ 2 ≤
      (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 - γ) :
    T < 13 / 100 := by
  have hden : 0 < 2 + q := by linarith [hq.1]
  have hell : 9 / 11 ≤ multiplier q := by
    unfold multiplier
    rw [le_div_iff₀ hden]
    linarith [hq.2]
  have hg := (gapFloor_gt_floor hq).trans hγ
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hell9 : (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 ≤
      (-1 + 8 * A - 131 / 11 * A ^ 2) / 6 := by
    nlinarith [mul_nonneg (show 0 ≤ multiplier q - 9 / 11 by linarith) hA2]
  have hbracket : 0 ≤ 8 - 131 / 11 * (1 / 3 + A) := by linarith [hA.2]
  have hmono : (-1 + 8 * A - 131 / 11 * A ^ 2) / 6 ≤ 17 / 297 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA.2) hbracket]
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hcoef : 5 / 33 * T ^ 2 ≤ (multiplier q - 2 / 3) * T ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hT2
  have hsq : T ^ 2 < (13 / 100) ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

end Erdos1017.MiddleUnsaturatedJoinedScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every fixed original adjacency row is integrable. -/
private theorem integrable_adjacency_row' (x : Ω) :
    Integrable (adjacencyKernel W x) μ := by
  have hmeas : StronglyMeasurable (adjacencyKernel W x) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  exact Eventually.of_forall (fun z => by
    change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
    exact (adjacency_moment_mem W (x, z)).2)

/-- On almost every genuine diffuse point, the original missing row is at
most the actual outside missing-section mass: a missing pair either lies in
the actual zero relation or would join two diffuse points, which the
original diffuse carrier forbids. -/
theorem ae_diffuse_missing_row_le_outside (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.D → (∫ y, 1 - adjacencyKernel W x y ∂μ) ≤ S.outsideSectionMass x := by
  let Z := actualZeroRelation W m S.ρ
  have hZ : MeasurableSet Z := measurableSet_actualZeroRelation W m S.ρ S.hρ
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hpair : ∀ᵐ z ∂μ.prod μ, z.1 ∈ S.D →
      1 - adjacencyKernel W z.1 z.2 ≤
        {y | (y, z.1) ∈ Z}.indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [hs, shiftedMoment_symm W m, hW.moment_mem, S.hDcomplete]
      with z hsup hsym hmem hcomp hxD
    by_cases hz : (z.2, z.1) ∈ Z
    · rw [indicator_of_mem (show z.2 ∈ {y | (y, z.1) ∈ Z} from hz)]
      have h0 : 0 ≤ adjacencyKernel W z.1 z.2 := (adjacency_moment_mem W z).1
      linarith only [h0]
    · rw [indicator_of_notMem (show z.2 ∉ {y | (y, z.1) ∈ Z} from hz)]
      have hone : adjacencyKernel W z.1 z.2 = 1 := by
        by_cases hρ : S.ρ z.2 = S.ρ z.1
        · have hyD : z.2 ∈ S.D := by
            rw [S.hDeq] at hxD ⊢
            intro hy
            apply hxD
            simp only [mem_iUnion] at hy ⊢
            obtain ⟨r, hrI, hyr⟩ := hy
            exact ⟨r, hrI, hρ.symm.trans hyr⟩
          exact hcomp hxD hyD
        · have hM : shiftedMoment W m z.swap ≠ 0 := fun h => hz ⟨h, hρ⟩
          have hpos : 0 < shiftedMoment W m z :=
            lt_of_le_of_ne hmem.1 (fun h => hM (hsym.trans h.symm))
          change W.moment CappedColor.adjacency z = 1
          simp only [hsup, hpos, ↓reduceIte]
      rw [hone]
      norm_num
  filter_upwards [Measure.ae_ae_of_ae_prod hpair] with x hx hxD
  have hV : MeasurableSet {y | (y, x) ∈ Z} := measurable_prodMk_right hZ
  calc (∫ y, 1 - adjacencyKernel W x y ∂μ) ≤
        ∫ y, {y | (y, x) ∈ Z}.indicator (fun _ => (1 : ℝ)) y ∂μ :=
        integral_mono_ae ((integrable_const 1).sub (integrable_adjacency_row' x))
          ((integrable_const 1).indicator hV) (hx.mono fun _ hy => hy hxD)
    _ = S.outsideSectionMass x := by
        rw [integral_indicator hV, setIntegral_const, smul_eq_mul, mul_one]
        rfl

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual middle-E2 no-saturation entry with its joined alternative
excluded, from the actual model, contact, global maximum and product-null
saturated set only. The source row cap is derived: atomic source points use
the sharp atomic missing cap, and genuine source dust uses the sharp
diffuse threshold cap at every radius in `(T, A]`, with `T < 13/100 < A`,
followed by the limit to `T`. The selected peak exceeds `3/10` and lies in
the positive one-center source with its exact private row. -/
theorem exists_middle_unsaturated_source_peak_actual (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    m = -LowerE2Scalar.multiplier q ∧ 187 / 1000 < q ∧ 3 * c ≤ d ∧
      ∃ (R : S.ReverseRecovery) (p k : S.I), R.plateau = {p} ∧
        0 < μ (S.reverseCompulsorySource {p}) ∧ k ≠ p ∧
        S.IsCommonForwardPeak d c k ∧ 3 / 10 < S.originalAtomMass k ∧
        (∀ j : S.I, j ≠ k → S.originalAtomMass j < S.originalAtomMass k) ∧
        (2 * (c - m * d) + m + (-m) * (∑' j, (S.originalAtomMass j) ^ 2) ≤
          2 * (S.originalAtomMass k) ^ 2) ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.reverseCompulsorySource {p}) ∧
        ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
          adjacencyKernel W z.1 z.2 = if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hqgt, hcount, hγ, R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve,
    hloc⟩ := S.exists_middle_unsaturated_entry hW hq hdq hvalue hderiv hgap hglobal hnull
  refine ⟨hm, hqgt, hcount, R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve, ?_⟩
  rcases hloc with hsrc | ⟨hjoin, _, _, _, hthird, _, _⟩
  · exact hsrc
  exfalso
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell : 2 / 3 ≤ -m := by
    rw [hneg]
    unfold LowerE2Scalar.multiplier
    rw [le_div_iff₀ (by linarith only [hq.1])]
    linarith only [hq.2]
  have hAI : S.originalAtomMass k ∈ Icc (1 / 4 : ℝ) (1 / 3) :=
    ⟨by linarith only [hA], hthird.le⟩
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∉ S.L := by
    obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
    have hjk : j = k := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
    subst hjk
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  have hgapD := S.middle_common_peak_sharp_gap_bound k hW hd hgap hpeak hnonlow hAI hell
  set A := S.originalAtomMass k with hAdef
  set γ := 2 * (c - m * d) + m with hγdef
  set D := (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 with hDdef
  have hcoef : 0 < -m - 2 / 3 := by
    rw [hneg]
    unfold LowerE2Scalar.multiplier
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by linarith only [hq.1])]
    linarith only [hq.2]
  have hrad : 0 ≤ (D - γ) / (-m - 2 / 3) := div_nonneg (by linarith only [hgapD]) hcoef.le
  set T := Real.sqrt ((D - γ) / (-m - 2 / 3)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = (D - γ) / (-m - 2 / 3) := Real.sq_sqrt hrad
  have hTcap : (-m - 2 / 3) * T ^ 2 = D - γ := by
    rw [hTsq, mul_div_cancel₀ _ hcoef.ne']
  have hTsmall : T < 13 / 100 := by
    apply MiddleUnsaturatedJoinedScalar.sharp_radius_lt ⟨hqgt.le, hq.2.le⟩
      ⟨hA.le, hthird.le⟩ hγ
    rw [← hneg]
    change (-m - 2 / 3) * T ^ 2 ≤ D - γ
    exact hTcap.le
  have hTA : T < A := by linarith only [hTsmall, hA]
  -- Genuine diffuse HIGH points have outside section mass at most `T`.
  have hdust : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ T := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ S.D → x ∈ S.H →
        S.outsideSectionMass x ≤ T + (A - T) / ((n : ℝ) + 2) := by
      rw [ae_all_iff]
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hstep : 0 < (A - T) / ((n : ℝ) + 2) := div_pos (by linarith only [hTA]) hn
      have hstepA : (A - T) / ((n : ℝ) + 2) ≤ A - T := by
        rw [div_le_iff₀ hn]
        nlinarith only [hTA, hn, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hRpos : 0 < T + (A - T) / ((n : ℝ) + 2) := by linarith only [hT0, hstep]
      have hmargin : D < γ + (-m - 2 / 3) * (T + (A - T) / ((n : ℝ) + 2)) ^ 2 := by
        have hsq : T ^ 2 < (T + (A - T) / ((n : ℝ) + 2)) ^ 2 := by nlinarith only [hT0, hstep]
        nlinarith only [hTcap, mul_lt_mul_of_pos_left hsq hcoef]
      exact S.ae_middle_diffuse_high_outside_le k hW hd hgap hpeak hnonlow hAI hell hRpos
        (by linarith only [hstepA]) hmargin
    filter_upwards [hall] with x hx hxD hxH
    by_contra hlt
    have hδ : 0 < S.outsideSectionMass x - T := by linarith only [lt_of_not_ge hlt]
    obtain ⟨n, hn⟩ := exists_nat_gt ((A - T) / (S.outsideSectionMass x - T))
    have hbound := hx n hxD hxH
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hlarge : A - T < (S.outsideSectionMass x - T) * ((n : ℝ) + 2) := by
      rw [div_lt_iff₀ hδ] at hn
      nlinarith only [hn, hδ]
    have hsmall : (A - T) / ((n : ℝ) + 2) < S.outsideSectionMass x - T := by
      rw [div_lt_iff₀ hn2]
      exact hlarge
    linarith only [hbound, hsmall]
  have hC : MeasurableSet (S.reverseCompulsorySource {p}) := R.singleton_measurableSet_source p hp
  have hrows := S.ae_diffuse_missing_row_le_outside hW hd hgap
  have hrow := S.ae_source_sharp_row_of_caps R hW hd hgap p k hp hjoin
    (γ := γ) (ell := -m) (D := D)
    (fun j hjk hH => S.middle_high_atom_closed_missing_sq_bound k j hjk hW hd hgap hpeak
      hnonlow hH hAI hell)
    (by
      filter_upwards [ae_restrict_of_ae hdust, ae_restrict_of_ae hrows, ae_restrict_mem hC]
        with x hxd hxr hxC hxI
      have hxD : x ∈ S.D := by
        rw [S.hDeq]
        intro hx
        simp only [mem_iUnion] at hx
        obtain ⟨r, hrI, hxr⟩ := hx
        exact hxI (by rw [show S.ρ x = r from hxr]; exact hrI)
      have hr := (hxr hxD).trans (hxd hxD hxC.1)
      have hr0 : 0 ≤ ∫ y, 1 - adjacencyKernel W x y ∂μ := integral_nonneg (fun y =>
        sub_nonneg.mpr (adjacency_moment_mem W (x, y)).2)
      have hsq : (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤ T ^ 2 :=
        pow_le_pow_left₀ hr0 hr 2
      nlinarith only [hTcap, mul_le_mul_of_nonneg_left hsq hcoef.le])
  exact S.not_middle_unsaturated_joined R hW hq hdq hvalue hderiv hgap hglobal hnull
    p k hp hkp hsource hpeak hjoin hrow

end Erdos1017.CappedModel.SelectedHighLowStructure
