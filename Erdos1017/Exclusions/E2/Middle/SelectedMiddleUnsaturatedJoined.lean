module

public import Erdos1017.Exclusions.E2.Middle.MiddleUnsaturatedJoinedScalar
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedPeak

/-!
# Exclusion of the unsaturated joined alternative

The unsaturated joined alternative of the middle `E₂` one-center entry is
impossible given the sharp missing-row cap on the entire source
(`not_middle_unsaturated_joined`), which leaves the no-saturation entry with
that alternative excluded (`exists_middle_unsaturated_source_peak`); the row
form of the sharp source cap is proved on the way.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every fixed original adjacency row is integrable. -/
private theorem integrable_adjacency_row (x : Ω) :
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

/-- On almost every point of an actual whole fiber, the original missing
row is exactly the fiber mass plus its whole missing region. This is the
row form of an atomic missing-mass cap. -/
theorem ae_missing_row_eq_on_fiber (S : SelectedHighLowStructure W m) (j : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      (∫ y, 1 - adjacencyKernel W x y ∂μ) =
        S.originalAtomMass j + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
  let I : Set Ω := {x | S.ρ x = j.val}
  let N := S.rootNeighborhood j
  have hI : MeasurableSet I := (S.hfibers j.val j.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood j
  have hsec := Measure.ae_ae_of_ae_prod (S.ae_original_root_adjacency j hW hd hgap)
  have hpart : μ.real I + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) +
      μ.real N = 1 := by
    have hmiss : KernelOperator.wholeFiberMissingSet S.ρ j.val = Iᶜ \ N := by
      ext x
      change (S.ρ x ≠ j.val ∧ j.val x ≤ 0) ↔ (S.ρ x ≠ j.val ∧ ¬(S.ρ x ≠ j.val ∧ 0 < j.val x))
      constructor
      · intro hx
        exact ⟨hx.1, fun h => not_lt_of_ge hx.2 h.2⟩
      · intro hx
        exact ⟨hx.1, le_of_not_gt (fun h => hx.2 ⟨hx.1, h⟩)⟩
    have hNI : N ⊆ Iᶜ := fun x hx => hx.1
    rw [hmiss, measureReal_sdiff hNI hN, measureReal_compl hI, probReal_univ]
    ring
  filter_upwards [ae_restrict_of_ae hsec, ae_restrict_mem hI] with x hx hxI
  have hrow : (fun y => 1 - adjacencyKernel W x y) =ᵐ[μ]
      fun y => 1 - N.indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hx] with y hy
    rw [hy hxI]
    by_cases hyN : y ∈ N <;> simp [N, hyN]
  rw [integral_congr_ae hrow, integral_sub (integrable_const 1)
    ((integrable_const 1).indicator hN), integral_const, integral_indicator hN,
    setIntegral_const]
  simp only [probReal_univ, smul_eq_mul, mul_one]
  change 1 - μ.real N = μ.real I + _
  linarith only [hpart]

/-- The source edge bound in scalar form: missing mass at most `s(T-b)`
inside the source square gives `G(S,S) >= s(t-T)` with `t = b+s`. -/
private theorem source_edge_lower {s b t T GSS : ℝ} (ht : t = b + s)
    (hmissing : s ^ 2 - GSS ≤ s * (T - b)) : s * (t - T) ≤ GSS := by
  subst ht
  nlinarith only [hmissing]

/-- The final reverse-budget comparison in scalar form. -/
private theorem joined_budget_false {c ell GSS MSS t b s T : ℝ}
    (hbudget : c + ell * (GSS / 2) + MSS / 2 ≤ t ^ 2) (hMSS : 0 ≤ MSS) (hell : 0 < ell)
    (ht : t = b + s) (hbT : b ≤ T) (hTt : T < t) (hGSS : s * (t - T) ≤ GSS)
    (hcost : t ^ 2 - ell / 2 * (t - T) ^ 2 < 1 / 8) (hc : 1 / 8 < c) : False := by
  have hst : t - T ≤ s := by linarith only [ht, hbT]
  have htT : 0 ≤ t - T := by linarith only [hTt]
  have hprod : (t - T) ^ 2 ≤ s * (t - T) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hst htT
  have h1 := mul_le_mul_of_nonneg_left hprod hell.le
  have h2 := mul_le_mul_of_nonneg_left hGSS hell.le
  nlinarith only [hbudget, hMSS, h1, h2, hcost, hc]

/-- A nonnegative height whose square exceeds a value above `1/8`
exceeds `1/3`. -/
private theorem height_gt_third {c ell GSS MSS t : ℝ}
    (hbudget : c + ell * (GSS / 2) + MSS / 2 ≤ t ^ 2) (hMSS : 0 ≤ MSS)
    (hGSS : 0 ≤ ell * GSS) (ht : 0 ≤ t) (hc : 1 / 8 < c) : 1 / 3 < t := by
  by_contra hn
  have hle : t ≤ 1 / 3 := le_of_not_gt hn
  have hsq : t ^ 2 ≤ 1 / 9 := by nlinarith only [hle, ht]
  nlinarith only [hbudget, hMSS, hGSS, hsq, hc]

/-- Each actual source point misses the whole head fiber, so its missing
row inside the source is at most its whole missing row minus `b`. -/
private theorem ae_source_row_le (S : SelectedHighLowStructure W m) (R : S.ReverseRecovery)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (p : S.I) (hp : R.plateau = {p}) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      (∫ y in S.reverseCompulsorySource {p}, 1 - adjacencyKernel W x y ∂μ) +
          S.originalAtomMass p ≤ ∫ y, 1 - adjacencyKernel W x y ∂μ := by
  let C := S.reverseCompulsorySource {p}
  let P : Set Ω := {x | S.ρ x = p.val}
  have hC : MeasurableSet C := R.singleton_measurableSet_source p hp
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hCP : Disjoint C P := (S.disjoint_singleton_fiber_source p).symm
  have hcol : ∀ᵐ z ∂μ.prod μ, S.ρ z.2 = p.val → z.1 ∉ S.rootNeighborhood p →
      adjacencyKernel W z.1 z.2 = 0 := by
    filter_upwards [adjacencyKernel_symm W,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae
        (S.ae_original_root_adjacency p hW hd hgap)] with z hsym hz hzp hx
    simpa [hx] using hsym.trans (hz hzp)
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hcol), ae_restrict_mem hC]
    with x hx hxC
  have hxN : x ∉ S.rootNeighborhood p := by
    intro hN
    exact not_lt_of_ge (S.mem_singleton_compulsorySource_missing p hxC).2 hN.2
  have hf : Integrable (fun y => 1 - adjacencyKernel W x y) μ :=
    (integrable_const 1).sub (integrable_adjacency_row x)
  have hf0 : 0 ≤ᵐ[μ] fun y => 1 - adjacencyKernel W x y :=
    Eventually.of_forall (fun y => sub_nonneg.mpr (adjacency_moment_mem W (x, y)).2)
  have hProw : (∫ y in P, 1 - adjacencyKernel W x y ∂μ) = S.originalAtomMass p := by
    have heq : ∀ᵐ y ∂μ.restrict P, 1 - adjacencyKernel W x y = 1 := by
      filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem hP] with y hy hyP
      rw [hy hyP hxN]
      ring
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have hle := setIntegral_le_integral (s := C ∪ P) hf hf0
  rw [setIntegral_union hCP hP hf.integrableOn hf.integrableOn, hProw] at hle
  exact hle

/-- Row form of the sharp source cap from its atomic and diffuse parts.
Atomic source points carry the exact fiber row `a_j + wholeMissing_j`,
so an atomic cap for every other HIGH atom applies. The joined peak fiber
meets the source only in a null set, LOW and neutral fibers cannot meet
the HIGH source, and genuine source dust needs its own diffuse cap. -/
theorem ae_source_sharp_row_of_caps (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (p k : S.I) (hp : R.plateau = {p})
    (hjoin : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p)
    {γ ell D : ℝ}
    (hatom : ∀ j : S.I, j ≠ k → (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) →
      γ + (ell - 2 / 3) * (S.originalAtomMass j +
        μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) ^ 2 ≤ D)
    (hdiffuse : ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}), S.ρ x ∉ S.I →
      γ + (ell - 2 / 3) * (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤ D) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      γ + (ell - 2 / 3) * (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤ D := by
  let : Countable S.I := S.hI.to_subtype
  have hC : MeasurableSet (S.reverseCompulsorySource {p}) :=
    R.singleton_measurableSet_source p hp
  have hfib (j : S.I) : ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}), S.ρ x = j.val →
      γ + (ell - 2 / 3) * (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤ D := by
    have hjI : MeasurableSet {x | S.ρ x = j.val} := (S.hfibers j.val j.property).1
    rcases S.hfiberClass j.val j.property with hH | hL | hN
    · by_cases hjk : j = k
      · subst hjk
        have hjoin' := (ae_restrict_iff' hjI).mp hjoin
        filter_upwards [ae_restrict_of_ae hjoin', ae_restrict_mem hC] with x hx hxC hxj
        exact absurd (hx hxj).2
          (not_lt_of_ge (S.mem_singleton_compulsorySource_missing p hxC).2)
      · have hrowj := (ae_restrict_iff' hjI).mp (S.ae_missing_row_eq_on_fiber j hW hd hgap)
        filter_upwards [ae_restrict_of_ae hrowj] with x hx hxj
        rw [hx hxj]
        exact hatom j hjk hH
    · have hL' := (ae_restrict_iff' hjI).mp hL
      filter_upwards [ae_restrict_of_ae hL', ae_restrict_mem hC] with x hx hxC hxj
      exact absurd (hx hxj) (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hxC.1)
    · have hN' := (ae_restrict_iff' hjI).mp hN
      filter_upwards [ae_restrict_of_ae hN', ae_restrict_mem hC] with x hx hxC hxj
      exact absurd (hx hxj) (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hxC.1)
  filter_upwards [ae_all_iff.mpr hfib, hdiffuse] with x hx hdust
  by_cases hxI : S.ρ x ∈ S.I
  · exact hx ⟨S.ρ x, hxI⟩ rfl
  · exact hdust hxI

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The unsaturated joined alternative of the actual middle-E2 one-center
entry is impossible, given the sharp missing-row cap on the entire
source: almost every source point has
`gamma + (ell-2/3) r(x)^2 <= D_ell(A)` for its original missing row
`r(x) = ∫ (1-G(x,·))`. Every source point misses the whole head `P`, so its
missing mass inside the source is at most `T-b`; this gives
`G(S,S) >= s(t-T)` and `b <= T` for atoms and genuine dust alike. The
actual reverse source budget, the joined masses and the exact closed
certificate then give `c < 1/8 < B_q < c`. -/
theorem not_middle_unsaturated_joined (S : SelectedHighLowStructure W m)
    (R : S.ReverseRecovery) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0)
    (p k : S.I) (hp : R.plateau = {p}) (hkp : k ≠ p)
    (hsource : 0 < μ (S.reverseCompulsorySource {p}))
    (hpeak : S.IsCommonForwardPeak d c k)
    (hjoin : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p)
    (hrow : ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
      2 * (c - m * d) + m + (-m - 2 / 3) * (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤
        (-1 + 8 * S.originalAtomMass k - (7 + 6 * (-m)) * S.originalAtomMass k ^ 2) / 6) :
    False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hellI, hγ⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hqgt := hW.middle_unsaturated_q_gt hq hdq hvalue hgap hnull
  have hA310 := S.middle_unsaturated_peak_gt_three_tenths hW ⟨hqgt.le, hq.2.le⟩ hdq hvalue
    hderiv hgap hglobal k hpeak
  have hnot := S.not_saturated_atom_pair_of_saturation_null hW hd hgap hellI.2 hnull k p
  obtain ⟨_, _, hmass, hthird⟩ :
      ¬S.IsSaturatedAtomPair k p ∧ 2 * S.originalAtomMass k ≤ μ.real (S.rootNeighborhood p) ∧
        2 * S.originalAtomMass k + R.height ≤ 1 ∧ S.originalAtomMass k < 1 / 3 := by
    rcases R.middle_e2_joined_peak_alternatives hW hq hdq hvalue hderiv hgap hglobal
        p k hp hkp hpeak hjoin with hsat | hunsat
    · exact absurd hsat.1 hnot
    · exact hunsat
  have hheight := R.singleton_height_eq_mass_add_source p hp
  have hbudget := R.singleton_source_credit hW hd hgap p hp
  rw [← hheight] at hbudget
  have hc8 : 1 / 8 < c := by
    have h := MiddleE2Parameter.twoHeadValue_gt_eighth hq
    rw [← hvalue] at h
    linarith only [h, hgap]
  have hrows := S.ae_source_row_le R hW hd hgap p hp
  have hC : MeasurableSet (S.reverseCompulsorySource {p}) := R.singleton_measurableSet_source p hp
  have hG : Integrable (fun z : Ω × Ω => adjacencyKernel W z.1 z.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  set C := S.reverseCompulsorySource {p} with hCdef
  set A := S.originalAtomMass k with hAdef
  set γ := 2 * (c - m * d) + m with hγdef
  set ell := -m with hell_def
  set t := R.height with htdef
  set b := S.originalAtomMass p with hbdef
  set s := μ.real C with hsdef
  set GSS := ∫ z in C ×ˢ C, adjacencyKernel W z.1 z.2 ∂μ.prod μ with hGSSdef
  set MSS := ∫ z in C ×ˢ C, shiftedKernel W m z.1 z.2 ∂μ.prod μ with hMSSdef
  set r : Ω → ℝ := fun x => ∫ y, 1 - adjacencyKernel W x y ∂μ with hrdef
  have hneg : ell = LowerE2Scalar.multiplier q := by rw [hell_def, hm]; ring
  have hMSS : 0 ≤ MSS :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hW.moment_mem.mono (fun _ hz => hz.1)))
  have hGSS0 : 0 ≤ GSS :=
    integral_nonneg_of_ae (ae_restrict_of_ae
      (Eventually.of_forall (fun z => (adjacency_moment_mem W z).1)))
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hell0 : 0 < ell := by linarith only [hellI.1]
  have hellthird : 2 / 3 < ell := by
    rw [hneg]
    unfold LowerE2Scalar.multiplier
    rw [lt_div_iff₀ (by linarith only [hq.1])]
    linarith only [hq.2]
  have ht0 : 0 ≤ t := by rw [hheight]; exact add_nonneg hb0 hs0
  have htthird := height_gt_third hbudget hMSS (mul_nonneg hell0.le hGSS0) ht0 hc8
  -- The sharp cap radius from one actual source point.
  obtain ⟨x0, _, hx0row, hx0cap⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show μ C ≠ 0 from hsource.ne') (hrows.and hrow)
  have hr0 (x : Ω) : 0 ≤ r x := integral_nonneg (fun y =>
    sub_nonneg.mpr (adjacency_moment_mem W (x, y)).2)
  set D := (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 with hDdef
  have hD0 : 0 ≤ (D - γ) / (ell - 2 / 3) := by
    apply div_nonneg _ (by linarith only [hellthird])
    nlinarith only [hx0cap, mul_nonneg (show 0 ≤ ell - 2 / 3 by linarith only [hellthird])
      (sq_nonneg (r x0))]
  set T := Real.sqrt ((D - γ) / (ell - 2 / 3)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = (D - γ) / (ell - 2 / 3) := Real.sq_sqrt hD0
  have hrT (x : Ω) (hx : γ + (ell - 2 / 3) * r x ^ 2 ≤ D) : r x ≤ T := by
    apply (le_abs_self (r x)).trans
    apply Real.abs_le_sqrt
    rw [le_div_iff₀ (by linarith only [hellthird])]
    linarith only [hx]
  have hcapT : (LowerE2Scalar.multiplier q - 2 / 3) * T ^ 2 ≤
      (-1 + 8 * A - (7 + 6 * LowerE2Scalar.multiplier q) * A ^ 2) / 6 - γ := by
    rw [← hneg, hTsq, mul_div_cancel₀ _ (by linarith only [hellthird])]
  obtain ⟨hTthird, _, hcost⟩ := MiddleUnsaturatedJoinedScalar.joined_cost_lt
    ⟨hqgt.le, hq.2.le⟩ ⟨hA310.le, hthird.le⟩ hγ hT0 hcapT
  -- `b <= T` from the same actual source point.
  have hbT : b ≤ T := by
    have hin : 0 ≤ ∫ y in C, 1 - adjacencyKernel W x0 y ∂μ :=
      setIntegral_nonneg hC (fun y _ => sub_nonneg.mpr (adjacency_moment_mem W (x0, y)).2)
    linarith only [hx0row, hrT x0 hx0cap, hin]
  -- The source square misses at most `s(T-b)`.
  have hmissing : (∫ z in C ×ˢ C, 1 - adjacencyKernel W z.1 z.2 ∂μ.prod μ) ≤ s * (T - b) := by
    have hint : IntegrableOn (fun z : Ω × Ω => 1 - adjacencyKernel W z.1 z.2) (C ×ˢ C)
        (μ.prod μ) := ((integrable_const 1).sub hG).integrableOn
    have hint' : Integrable (fun z : Ω × Ω => 1 - adjacencyKernel W z.1 z.2)
        ((μ.restrict C).prod (μ.restrict C)) := by
      rw [Measure.prod_restrict]
      exact hint
    rw [setIntegral_prod _ hint]
    have hinner : ∀ᵐ x ∂μ.restrict C, (∫ y in C, 1 - adjacencyKernel W x y ∂μ) ≤ T - b := by
      filter_upwards [hrows, hrow] with x hx hcap
      linarith only [hx, hrT x hcap]
    have hmono := setIntegral_mono_ae_restrict hint'.integral_prod_left
      (integrable_const (T - b)).integrableOn hinner
    rw [setIntegral_const, smul_eq_mul] at hmono
    exact hmono
  have hsplit : (∫ z in C ×ˢ C, 1 - adjacencyKernel W z.1 z.2 ∂μ.prod μ) = s ^ 2 - GSS := by
    rw [integral_sub (integrable_const 1).integrableOn hG.integrableOn, setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul,
      ← measureReal_def, sq]
  rw [hsplit] at hmissing
  have hGSS := source_edge_lower hheight hmissing
  have hfinal := hcost t htthird.le (by linarith only [hmass])
  rw [← hneg] at hfinal
  exact joined_budget_false hbudget hMSS hell0 hheight hbT
    (by linarith only [hTthird, htthird]) hGSS hfinal hc8

/-- The actual middle-E2 no-saturation entry with its joined alternative
excluded. Given the sharp missing-row cap on the entire source of every
actual one-center recovery around an actual common peak, the selected peak
exceeds `3/10` and lies in the positive source with its exact private row.
The cap is the only input beyond the selected global contact; its atomic
part is the fiber row of `ae_source_sharp_row_of_caps`. -/
theorem exists_middle_unsaturated_source_peak (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0)
    (hcap : ∀ (R : S.ReverseRecovery) (p k : S.I), R.plateau = {p} →
      S.IsCommonForwardPeak d c k →
        ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {p}),
          2 * (c - m * d) + m + (-m - 2 / 3) * (∫ y, 1 - adjacencyKernel W x y ∂μ) ^ 2 ≤
            (-1 + 8 * S.originalAtomMass k - (7 + 6 * (-m)) * S.originalAtomMass k ^ 2) / 6) :
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
  obtain ⟨hm, hqgt, hcount, _, R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve,
    hloc⟩ := S.exists_middle_unsaturated_entry hW hq hdq hvalue hderiv hgap hglobal hnull
  refine ⟨hm, hqgt, hcount, R, p, k, hp, hsource, hkp, hpeak, hA, hlargest, hreserve, ?_⟩
  rcases hloc with hsrc | hjoined
  · exact hsrc
  · exact (S.not_middle_unsaturated_joined R hW hq hdq hvalue hderiv hgap hglobal hnull
      p k hp hkp hsource hpeak hjoined.1 (hcap R p k hp hpeak)).elim

end Erdos1017.CappedModel.SelectedHighLowStructure
