module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateSoleSourceCovariance
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateSector
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedSourcePeak
public import Erdos1017.Exclusions.E2.Middle.MiddlePrivateUnsaturatedScalar
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateUnsaturatedTail

/-!
# Sole-source boundary on the no-saturation branch

At the single-atom source boundary the recovered height is `b + A` and the
reverse source budget gives `c ≤ (A + b)²`; a private common peak is impossible
given the hole exposure, and every remaining no-saturation configuration reduces
to this residual (`exists_middle_unsaturated_sole_source_residual`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem whole_row_le (S : SelectedHighLowStructure W m) (r : S.I)
    (hm : m ≤ 1) : ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property] with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

/-- The original flat whole row of an actual atom is carried by its
neighborhood with value at most `1 - m`: `ν <= (1 - m) n`. -/
theorem stationary_row_le_neighborhood (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) :
    2 * (c - m * d) ≤ (1 - m) * μ.real (S.rootNeighborhood r) := by
  let N := S.rootNeighborhood r
  have hN := S.measurableSet_rootNeighborhood r
  have hf : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hoff : (r.val : Ω → ℝ) =ᵐ[μ.restrict Nᶜ] fun _ => 0 := by
    filter_upwards [ae_restrict_mem hN.compl, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
      ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
    exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg
  have hoffint : (∫ x in Nᶜ, (r.val : Ω → ℝ) x ∂μ) = 0 := integral_eq_zero_of_ae hoff
  have hNint : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) = 2 * (c - m * d) := by
    have hpart := integral_add_compl hN hf
    rw [hoffint, add_zero, S.row_integral_of_stationary r hW] at hpart
    exact hpart
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  have hbound : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) ≤ (∫ x in N, (1 - m : ℝ) ∂μ) :=
    integral_mono_ae hf.integrableOn (integrable_const (1 - m)).integrableOn
      (ae_restrict_of_ae (whole_row_le S r hm))
  rw [hNint, setIntegral_const, smul_eq_mul] at hbound
  simpa only [N, mul_comm] using hbound

/-- At the single-atom source boundary the recovered height is `b + A`, and
the actual reverse source budget gives `c <= (A + b)^2`. -/
theorem ReverseRecovery.middle_private_sole_source_cost {S : SelectedHighLowStructure W m}
    (R : S.ReverseRecovery)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (i p : S.I) (hp : R.plateau = {p})
    (hsrc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p})
    (hsole : μ (S.reverseCompulsorySource {p} \ {x | S.ρ x = i.val}) = 0) :
    c ≤ (S.originalAtomMass i + S.originalAtomMass p) ^ 2 := by
  let C := S.reverseCompulsorySource {p}
  let I : Set Ω := {x | S.ρ x = i.val}
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hCI : μ.real C ≤ μ.real I := by
    have hsub : C ⊆ I ∪ (C \ I) := fun x hx => by
      by_cases h : x ∈ I
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    calc μ.real C ≤ μ.real (I ∪ (C \ I)) := measureReal_mono hsub
      _ ≤ μ.real I + μ.real (C \ I) := measureReal_union_le _ _
      _ = μ.real I := by
        rw [show μ.real (C \ I) = 0 from by
          change (μ (C \ I)).toReal = 0
          rw [show μ (C \ I) = 0 from hsole, ENNReal.toReal_zero], add_zero]
  have hIC : μ.real I ≤ μ.real C :=
    ENNReal.toReal_mono (measure_ne_top μ C)
      (measure_mono_ae ((ae_restrict_iff' hI).mp hsrc))
  have hheight := R.singleton_height_eq_mass_add_source p hp
  have hbudget := R.singleton_source_credit hW hd hgap p hp
  have hG : 0 ≤ ∫ z in C ×ˢ C, adjacencyKernel W z.1 z.2 ∂μ.prod μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae
      (Eventually.of_forall (fun z => (adjacency_moment_mem W z).1)))
  have hM : 0 ≤ ∫ z in C ×ˢ C, shiftedKernel W m z.1 z.2 ∂μ.prod μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hW.moment_mem.mono (fun _ hz => hz.1)))
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hCeq : μ.real C = S.originalAtomMass i := le_antisymm hCI hIC
  change c + (-m) * ((∫ z in C ×ˢ C, adjacencyKernel W z.1 z.2 ∂μ.prod μ) / 2) +
    (∫ z in C ×ˢ C, shiftedKernel W m z.1 z.2 ∂μ.prod μ) / 2 ≤
      (S.originalAtomMass p + μ.real C) ^ 2 at hbudget
  rw [hCeq] at hbudget
  nlinarith [mul_nonneg (show 0 ≤ -m by linarith) hG]

/-- A private common peak at a middle-E2 contact is not LOW. -/
private theorem private_peak_nonlow (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L := by
  obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ := S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst hji
  rcases hside with hH | hN
  · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
  · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual private peak data on the no-saturation middle-E2 branch:
`q > 187/1000`, `3/10 < A < 1/3`, the sharp gap `gamma <= D_ell(A)` and the
strengthened floor `A > 61/200`. -/
theorem middle_private_peak_bounds (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (i p : S.I) (hip : i ≠ p) (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    187 / 1000 < q ∧ 61 / 200 < S.originalAtomMass i ∧ S.originalAtomMass i < 1 / 3 ∧
      2 * (c - m * d) + m ≤
        (-1 + 8 * S.originalAtomMass i -
          (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hγ⟩ := hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hqgt := hW.middle_unsaturated_q_gt hq hdq hvalue hgap hnull
  have hq2 : q ∈ Icc (187 / 1000 : ℝ) (1 / 5) := ⟨hqgt.le, hq.2.le⟩
  have hA310 := S.middle_unsaturated_peak_gt_three_tenths hW hq2 hdq hvalue hderiv hgap
    hglobal i hpeak
  have hsector := S.private_peak_large_sector i p hip hW hq hdq hvalue hderiv hgap hglobal
    hpeak hprivate
  have hb : 0 < μ.real {x | S.ρ x = p.val} :=
    ENNReal.toReal_pos (S.hfibers p.val p.property).2.1.ne' (measure_ne_top μ _)
  have hthird : S.originalAtomMass i < 1 / 3 := by
    change μ.real {x | S.ρ x = i.val} < 1 / 3
    linarith
  have hell : 2 / 3 ≤ -m := by
    rw [hneg]
    linarith [MiddlePrivateSoleSourceScalar.multiplier_ge hq2]
  have hgapD := S.middle_common_peak_sharp_gap_bound i hW hd hgap hpeak
    (private_peak_nonlow S i hW hd hgap hpeak) ⟨by linarith, hthird.le⟩ hell
  refine ⟨hqgt, ?_, hthird, hgapD⟩
  by_contra hn
  have hcert := MiddlePrivateSoleSourceScalar.selectorValue_lt_gapFloor_of_le hq2
    ⟨by linarith, le_of_not_gt hn⟩
  rw [← hneg] at hcert
  linarith

/-- The private sole-source case without saturation, conditional on the hole exposure.
At the single-atom source boundary `S = I`, an actual private common peak
with the scaled exposure `ell k < E_K = ∫_K ρ_I` is impossible: the scaled
curvature Schur bound, the sole-source cost `c <= (A+b)^2`, the flat head row
`ν <= (1+ell) n` and the closed scalar certificate `882/1163 < 9/11`
contradict each other. The exposure is the only hypothesis beyond the
actual model; it is the output required from the failed-insertion module. -/
theorem no_middle_private_sole_source_of_exposure (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (i p : S.I) (hip : i ≠ p)
    (hp : R.plateau = {p}) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hsrc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p})
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hsole : μ (S.reverseCompulsorySource {p} \ {x | S.ρ x = i.val}) = 0)
    (hexposure : (-m) * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p) <
      ∫ z in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p),
        (i.val : Ω → ℝ) z ∂μ) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hq5 : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hγ⟩ := hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  obtain ⟨hqgt, hA61, hthird, hgapD⟩ := S.middle_private_peak_bounds hW hq hdq hvalue hderiv
    hgap hglobal hnull i p hip hpeak hprivate
  have hq2 : q ∈ Icc (187 / 1000 : ℝ) (1 / 5) := ⟨hqgt.le, hq.2.le⟩
  have hell9 : 9 / 11 ≤ -m := by rw [hneg]; exact MiddlePrivateSoleSourceScalar.multiplier_ge hq2
  have hell83 : -m < 83 / 100 := by
    rw [hneg]
    exact MiddlePrivateUnsaturatedScalar.multiplier_lt hq2
  have hg27 := MiddlePrivateUnsaturatedScalar.gapFloor_gt hq2
  have hcurv := (hW.e2_contact_curvature hq5 hdq hgap hglobal).2
  have hCq := E2PrivateCurvature.curvature_pos_lt_six ⟨hq5.1.le, hq5.2⟩
  have hk := S.private_hole_measure_pos i p hip hW hd hgap hprivate
  have hschur := S.private_curvature_covariance_scaled i p hip hW hd hgap hprivate hCq.1
    (by linarith) hcurv hk hexposure
  have hdeg := (S.private_wholeRowDegrees_sector i p hip hW hd hgap hprivate).2
  have hrow := S.stationary_row_le_neighborhood hW hd hgap p
  have hcost := R.middle_private_sole_source_cost hW hd hgap i p hp hsrc hsole
  have hc8 : 1 / 8 < c := by
    have h := MiddleE2Parameter.twoHeadValue_gt_eighth hq
    rw [← hvalue] at h
    linarith
  have hh : 1 - 2 * d < 1 / 4 := by
    have h := MiddlePrivateSoleSourceScalar.missingMass_lt_quarter hq2
    linarith [hdq]
  set A := μ.real {x | S.ρ x = i.val} with hAdef
  set b := μ.real {x | S.ρ x = p.val} with hbdef
  set k := μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)
    with hkdef
  set n := μ.real (S.rootNeighborhood p) with hndef
  set ν := 2 * (c - m * d) with hνdef
  have hk0 : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ _)
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hA0 : 0 < A := by change 0 < S.originalAtomMass i; linarith
  change c ≤ (A + b) ^ 2 at hcost
  change 2 * (c - m * d) + m ≤ (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 at hgapD
  change A < 1 / 3 at hthird
  -- `ν < 1`: `ν = gamma + ell <= (4 - 3 ell)/27 + ell`.
  have hDthird : (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6 ≤ (4 - 3 * (-m)) / 27 := by
    have hbr : 0 ≤ 8 - (7 + 6 * (-m)) * (1 / 3 + A) := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ 1 / 3 - A by linarith) hbr]
  have hν1 : ν < 1 := by linarith
  have hν0 : 0 < ν := (hW.strict_gap_structure hd hgap).stationary_pos
  -- `α = A + b > 7/20` from `c <= α^2` and `c > 1/8`.
  have hα : 7 / 20 < A + b := by
    by_contra hn
    have hle : A + b ≤ 7 / 20 := le_of_not_gt hn
    have hsq : (A + b) ^ 2 ≤ (7 / 20) ^ 2 := pow_le_pow_left₀ (by linarith) hle 2
    nlinarith
  -- `z = 1 - n < 21/40` from `ν <= (1 + ell) n` and `ν > ell + 27/500`.
  have hz : A + b + k < 21 / 40 := by
    have hn : 19 / 40 < n := by
      by_contra hn
      have hle : n ≤ 19 / 40 := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 1 - m by linarith)
      linarith
    linarith
  exact MiddlePrivateSoleSourceScalar.sole_source_false hell9 hCq.1 hCq.2 hν0 hν1 hh hA0 hb0
    hk0 hα hz hschur

/-- The actual no-saturation middle-E2 residual. From the actual model,
contact, global maximum and product-null saturated set only, every remaining
configuration is the single-atom source boundary: an actual one-center
recovery whose private common peak `I` fills the entire source up to a null
set, with `61/200 < A < 1/3`, and whose hole exposure is not above
`ell k`. The joined peak and every positive secondary source are excluded.
Proving `ell k < E_K` for this same data closes the no-saturation branch. -/
theorem exists_middle_unsaturated_sole_source_residual (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0) :
    m = -LowerE2Scalar.multiplier q ∧ 187 / 1000 < q ∧
      ∃ (R : S.ReverseRecovery) (p i : S.I), R.plateau = {p} ∧ i ≠ p ∧
        S.IsCommonForwardPeak d c i ∧
        61 / 200 < S.originalAtomMass i ∧ S.originalAtomMass i < 1 / 3 ∧
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p}) ∧
        (∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
          adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) ∧
        μ (S.reverseCompulsorySource {p} \ {x | S.ρ x = i.val}) = 0 ∧
        (∫ z in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p),
            (i.val : Ω → ℝ) z ∂μ) ≤
          (-m) * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
            S.rootNeighborhood p) := by
  obtain ⟨hm, hqgt, _, R, p, i, hp, _, hip, hpeak, _, _, _, hsrc, hprivate⟩ :=
    S.exists_middle_unsaturated_source_peak_actual hW hq hdq hvalue hderiv hgap hglobal hnull
  obtain ⟨_, hA61, hthird, _⟩ := S.middle_private_peak_bounds hW hq hdq hvalue hderiv hgap
    hglobal hnull i p hip hpeak hprivate
  have hsole : μ (S.reverseCompulsorySource {p} \ {x | S.ρ x = i.val}) = 0 := by
    by_contra hne
    exact S.no_middle_private_positive_secondary_source R i p hip hp hW hq hdq hvalue hderiv
      hgap hglobal hnull hpeak hsrc hprivate (pos_iff_ne_zero.mpr hne)
  refine ⟨hm, hqgt, R, p, i, hp, hip, hpeak, hA61, hthird, hsrc, hprivate, hsole, ?_⟩
  by_contra hexp
  exact S.no_middle_private_sole_source_of_exposure R i p hip hp hW hq hdq hvalue hderiv hgap
    hglobal hnull hpeak hsrc hprivate hsole (lt_of_not_ge hexp)


end Erdos1017.CappedModel.SelectedHighLowStructure
