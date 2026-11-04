module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceCredits

/-!
# Degree-tangent bound for the cusp source remainder

The cusp source peak has its exact original adjacency degree, the whole original
fiber being retained, and the original degree-tangent inequality controls the
entire source remainder with every degree and energy input derived on the
original law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open WholeSourceChild KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

private theorem original_peak_row_event (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ R.cuspSourcePeak i → adjacencyKernel W p.1 p.2 =
      1 - ({x | S.ρ x = r.val} ∪ R.cuspSourcePeak i).indicator (fun _ => 1) p.2 := by
  have hs := S.ae_collapsed_half_support hW hd hgap true
  rw [Measure.prod_restrict] at hs
  have hs := (ae_restrict_iff' ((S.measurableSet_half true).prod
    (S.measurableSet_half true))).mp hs
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hg
  have hi := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hinside
  filter_upwards [hs, hg.joined_CO, adjacencyKernel_symm W,
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
    singleton_zero_II (S := S) i, Measure.quasiMeasurePreserving_snd.ae hi]
    with p hh hjoin hsym hzrev hind hiy hx
  have hlabel : S.collapsedPartLabel p.1 = some i := by
    change p.1 ∈ S.collapsedPartLabel ⁻¹' {some i}
    rw [S.collapsedPartLabel_fiber]
    exact hx.2
  by_cases hp : S.ρ p.2 = r.val
  · rw [indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from Or.inl hp)]
    rw [hsym.trans (hzrev hp hx.1)]
    norm_num
  · by_cases hy : p.2 ∈ R.cuspSourcePeak i
    · rw [indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from Or.inr hy),
        hind hx.2 hy.2]
      norm_num
    · rw [indicator_of_notMem (show p.2 ∉ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from
        fun h => h.elim hp hy)]
      simp only [sub_zero]
      by_cases hH : p.2 ∈ S.H
      · have hh := hh ⟨show p.1 ∈ S.half true from Or.inl hx.1.1,
            show p.2 ∈ S.half true from Or.inl hH⟩
        have hne : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 := by
          intro he
          have hyi : S.ρ p.2 = i.val := by
            have hf : p.2 ∈ S.collapsedPartLabel ⁻¹' {some i} := he.symm.trans hlabel
            rwa [S.collapsedPartLabel_fiber] at hf
          exact hy ⟨hiy hyi, hyi⟩
        change adjacencyKernel W p.1 p.2 = _ at hh
        simpa only [ite_eq_left (Or.inl hne)] using hh
      · exact hjoin hx.1 ⟨hH, hp⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem degree_eq_integral :
    ∀ᵐ x ∂μ, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x =
      ∫ y, adjacencyKernel W x y ∂μ := by
  filter_upwards [onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))] with x hx
  change onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)) x = _
  rw [hx, applyKernel]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
  simp only [hy, Function.const_apply, mul_one]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem degree_le_of_missing (C T : Set Ω) (hT : MeasurableSet T)
    (hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ T → adjacencyKernel W p.1 p.2 = 0) :
    ∀ᵐ x ∂μ, x ∈ C → adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x ≤ 1 - μ.real T := by
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  filter_upwards [degree_eq_integral (W := W), Measure.ae_ae_of_ae_prod hzero,
    hG.prod_right_ae] with x hx hz hi hC
  rw [hx]
  have hle : (∫ y, adjacencyKernel W x y ∂μ) ≤
      ∫ y, 1 - T.indicator (fun _ => (1 : ℝ)) y ∂μ := by
    apply integral_mono_ae hi ((integrable_const 1).sub ((integrable_const 1).indicator hT))
    filter_upwards [hz] with y hy
    change adjacencyKernel W x y ≤ 1 - T.indicator (fun _ => (1 : ℝ)) y
    by_cases ht : y ∈ T
    · rw [hy hC ht, indicator_of_mem ht]; norm_num
    · rw [indicator_of_notMem ht, sub_zero]
      exact (adjacency_moment_mem W (x, y)).2
  rw [integral_sub (integrable_const (1 : ℝ)) ((integrable_const (1 : ℝ)).indicator hT),
    integral_indicator hT, setIntegral_const] at hle
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] using hle

/-- The source peak has its exact original adjacency degree. The entire
original whole fiber is retained, so there is no missing same-label mass. -/
theorem cusp_source_peak_degree (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    ∀ᵐ x ∂μ, x ∈ R.cuspSourcePeak i →
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x =
        1 - S.originalAtomMass r - S.originalAtomMass i := by
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hg
  have hdis : Disjoint {x | S.ρ x = r.val} (R.cuspSourcePeak i) :=
    hg.disjoint_IC.mono_right (inter_subset_left (s := R.cuspSource)
      (t := {x | S.ρ x = i.val}))
  have hm := (S.hfibers r.val r.property).1.union (R.measurableSet_cuspSourcePeak i)
  filter_upwards [degree_eq_integral (W := W),
    Measure.ae_ae_of_ae_prod (R.original_peak_row_event r i hW hd hgap hr hinside)]
    with x hx he hi
  rw [hx, integral_congr_ae (he.mono (fun _ h => h hi)),
    integral_sub (integrable_const 1) ((integrable_const 1).indicator hm),
    integral_indicator hm, setIntegral_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [measureReal_union hdis (R.measurableSet_cuspSourcePeak i),
    R.cuspSourcePeak_mass_original i hinside]
  change 1 - (S.originalAtomMass r + S.originalAtomMass i) = _
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem integral_sourceDirection (P T : Set Ω) (hP : MeasurableSet P)
    (hT : MeasurableSet T) (hPpos : 0 < μ.real P) :
    (∫ x, MissingFlow.OneCenter.sourceDirection μ P T x ∂μ) = 0 := by
  unfold MissingFlow.OneCenter.sourceDirection
  rw [integral_sub ((MissingFlow.OneCenter.integrable_recipientDensity hP).const_mul _)
      ((integrable_const 1).indicator hT), integral_const_mul,
    MissingFlow.OneCenter.integral_recipientDensity hP hPpos, integral_indicator hT,
    setIntegral_const, smul_eq_mul]
  ring

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem degree_sourceDirection (g : Ω → ℝ) (hg : Integrable g μ)
    (P T : Set Ω) (hP : MeasurableSet P) (hT : MeasurableSet T) :
    (∫ x, g x * MissingFlow.OneCenter.sourceDirection μ P T x ∂μ) =
      μ.real T / μ.real P * (∫ x in P, g x ∂μ) - ∫ x in T, g x ∂μ := by
  have he : (fun x => g x * MissingFlow.OneCenter.sourceDirection μ P T x) =
      fun x => μ.real T / μ.real P * P.indicator g x - T.indicator g x := by
    funext x
    by_cases hp : x ∈ P <;> by_cases ht : x ∈ T <;>
      simp [MissingFlow.OneCenter.sourceDirection,
        MissingFlow.AtomicAssignment.recipientDensity, hp, ht, div_eq_mul_inv] <;> ring
  rw [he, integral_sub ((hg.indicator hP).const_mul _) (hg.indicator hT),
    integral_const_mul, integral_indicator hP, integral_indicator hT]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem pairing_sourceDirections (K : Ω → Ω → ℝ)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (P T U : Set Ω) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hPP : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 0)
    (hPT : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ T → K p.1 p.2 = 0)
    (hPU : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ U → K p.1 p.2 = 0) :
    kernelPairing (μ := μ) K (MissingFlow.OneCenter.sourceDirection μ P T)
      (MissingFlow.OneCenter.sourceDirection μ P U) = crossIntegral μ K U T := by
  rw [← pairing_indicator K U T hU hT]
  apply integral_congr_ae
  filter_upwards [hPP, hPT, hsym,
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hPU]
    with p hpp hpt hs hup
  change p.2 ∈ P → p.1 ∈ U → K p.2 p.1 = 0 at hup
  by_cases hp : p.1 ∈ P <;> by_cases hq : p.2 ∈ P <;>
    by_cases ht : p.2 ∈ T <;> by_cases hu : p.1 ∈ U <;>
    first
    | simp [hpp hp hq]
    | simp [hpt hp ht]
    | simp [hs.trans (hup hq hu)]
    | simp [MissingFlow.OneCenter.sourceDirection,
        MissingFlow.AtomicAssignment.recipientDensity, hp, hq, ht, hu]

private theorem tangent_bound {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (x y : Ω → ℝ) (hx : Integrable x μ) (hy : Integrable y μ)
    (hxm : (∫ a, x a ∂μ) = 0) (hym : (∫ a, y a ∂μ) = 0)
    (A s Phi : ℝ) (hPhi : 0 ≤ Phi)
    (hyq : kernelEnergy (μ := μ) (shiftedKernel W m) y = 0)
    (hxy : kernelPairing (μ := μ) (shiftedKernel W m) x y = A * Phi)
    (hLy : (∫ a, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) a * y a ∂μ) < 0)
    (hcomp : s * (∫ a, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) a * y a ∂μ) ≤
      A * (∫ a, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) a * x a ∂μ)) :
    kernelEnergy (μ := μ) (shiftedKernel W m) x / 2 ≤ s * Phi := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  obtain ⟨B, _, hB⟩ := operator_range_bounded (adjacencyKernel W) (by norm_num)
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))
  have hgx := integrable_bounded_mul (Lp.memLp g).aestronglyMeasurable hB hx
  have hgy := integrable_bounded_mul (Lp.memLp g).aestronglyMeasurable hB hy
  let t := (∫ a, g a * x a ∂μ) / (∫ a, g a * y a ∂μ)
  have ht : t * (∫ a, g a * y a ∂μ) = ∫ a, g a * x a ∂μ :=
    div_mul_cancel₀ _ (ne_of_lt hLy)
  have htA : t * A ≤ s := by
    have he : (t * A - s) * (∫ a, g a * y a ∂μ) =
        A * (∫ a, g a * x a ∂μ) - s * (∫ a, g a * y a ∂μ) := by
      linear_combination A * ht
    nlinarith
  have hmean : (∫ a, x a - t * y a ∂μ) = 0 := by
    rw [integral_sub hx (hy.const_mul t), integral_const_mul, hxm, hym]
    ring
  have hdegree : (∫ a, g a * (x a - t * y a) ∂μ) = 0 := by
    have he : (fun a => g a * (x a - t * y a)) =
        fun a => g a * x a - t * (g a * y a) := by funext a; ring
    rw [he, integral_sub hgx (hgy.const_mul t), integral_const_mul, ht, sub_self]
  have he := hW.integrable_tangent_nonpositive_of_strict_gap hd hgap _
    (hx.sub (hy.const_mul t)) hmean hdegree
  have hsym := (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  change kernelEnergy (μ := μ) (shiftedKernel W m) (fun a => x a - t * y a) ≤ 0 at he
  rw [kernelEnergy_sub_mul _ (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    hsym x y hx hy t, hyq, hxy] at he
  nlinarith [mul_le_mul_of_nonneg_right htA hPhi]

/-- The original degree-tangent inequality controls the entire source
remainder. Every degree and energy input is derived on the original law;
no multiplier or stationarity is assigned to the partial endpoint. -/
theorem cusp_source_tangent_energy_le (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) :
    R.cuspRemainderEnergy i / 2 ≤ μ.real R.cuspSource * R.cuspCrossEnergy i := by
  let P := {x | S.ρ x = r.val}
  let I := R.cuspSourcePeak i
  let J := R.cuspSourceRemainder i
  let A := S.originalAtomMass i
  let b := S.originalAtomMass r
  let z := μ.real J
  let s := μ.real R.cuspSource
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  let u := MissingFlow.OneCenter.sourceDirection μ P I
  let v := MissingFlow.OneCenter.sourceDirection μ P J
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hI : MeasurableSet I := R.measurableSet_cuspSourcePeak i
  have hJ : MeasurableSet J := R.measurableSet_cuspSourceRemainder i
  have hA : 0 < A :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  have hb : 0 < b :=
    ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)
  have hz : 0 < z := R.cuspSourceRemainder_mass_pos i hsourceEdge
  have hmass : μ.real I = A := R.cuspSourcePeak_mass_original i hinside
  have hs : s = A + z := by
    have hm := R.cuspSource_mass_decomposition i
    rw [R.cuspSourcePeak_mass_original i hinside] at hm
    exact hm.symm
  have hg : Integrable (g : Ω → ℝ) μ := (Lp.memLp g).integrable (by norm_num)
  have hu : Integrable u μ := MissingFlow.OneCenter.integrable_sourceDirection hP hI
  have hv : Integrable v μ := MissingFlow.OneCenter.integrable_sourceDirection hP hJ
  have hum : (∫ x, u x ∂μ) = 0 := integral_sourceDirection P I hP hI hb
  have hvm : (∫ x, v x ∂μ) = 0 := integral_sourceDirection P J hP hJ hb
  have hgeom := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hgeom
  have hPP := singleton_zero_II (S := S) r
  have hPJ : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ J → adjacencyKernel W p.1 p.2 = 0 :=
    hgeom.zero_IC.mono (fun _ hp hx hy => hp hx hy.1)
  have hPI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ I → adjacencyKernel W p.1 p.2 = 0 :=
    hgeom.zero_IC.mono (fun _ hp hx hy => hp hx hy.1)
  have hPall : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P ∪ R.cuspSource →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [hPP, hgeom.zero_IC] with p hp hc hx hy
    exact hy.elim (hp hx) (hc hx)
  have hJP : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∈ P → adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [adjacencyKernel_symm W,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hPJ] with p hs hp hx hy
    exact hs.trans (hp hy hx)
  have hgp : (∫ x in P, g x ∂μ) ≤ b * (1 - b - s) := by
    have he := degree_le_of_missing P (P ∪ R.cuspSource)
      (hP.union R.measurableSet_cuspSource) hPall
    have hbnd := integral_mono_ae hg.integrableOn (integrable_const (1 - μ.real
      (P ∪ R.cuspSource))).integrableOn ((ae_restrict_iff' hP).mpr he)
    rw [setIntegral_const, measureReal_union hgeom.disjoint_IC R.measurableSet_cuspSource,
      smul_eq_mul] at hbnd
    change (∫ x in P, g x ∂μ) ≤ b * (1 - (b + s)) at hbnd
    linarith
  have hgj : (∫ x in J, g x ∂μ) ≤ z * (1 - b) := by
    have he := degree_le_of_missing J P hP hJP
    have hbnd := integral_mono_ae hg.integrableOn (integrable_const (1 - μ.real P)).integrableOn
      ((ae_restrict_iff' hJ).mpr he)
    simpa only [setIntegral_const, smul_eq_mul, P, z, b, originalAtomMass] using hbnd
  have hgi : (∫ x in I, g x ∂μ) = A * (1 - b - A) := by
    rw [integral_congr_ae ((ae_restrict_iff' hI).mpr
      (R.cusp_source_peak_degree r i hW hd hgap hr hinside)), setIntegral_const,
      smul_eq_mul, hmass]
  let dp := (∫ x in P, g x ∂μ) / b
  have hdp : dp ≤ 1 - b - s := (div_le_iff₀ hb).mpr (by nlinarith [hgp])
  have hdu : (∫ x, g x * u x ∂μ) = A * (dp - (1 - b - A)) := by
    rw [degree_sourceDirection _ hg P I hP hI, hmass, hgi]
    change A / b * (∫ x in P, g x ∂μ) - A * (1 - b - A) = _
    dsimp [dp]
    ring
  have hdv : (∫ x, g x * v x ∂μ) = z * dp - ∫ x in J, g x ∂μ := by
    rw [degree_sourceDirection _ hg P J hP hJ]
    change z / b * (∫ x in P, g x ∂μ) - _ = _
    dsimp [dp]
    ring
  have hduNeg : (∫ x, g x * u x ∂μ) < 0 := by
    rw [hdu]
    apply mul_neg_of_pos_of_neg hA
    linarith
  have hcompare : s * (∫ x, g x * u x ∂μ) ≤ A * (∫ x, g x * v x ∂μ) := by
    rw [hdu, hdv]
    have hbnd : 0 ≤ s * (1 - b - A) - A * dp - ∫ x in J, g x ∂μ := by
      nlinarith [mul_le_mul_of_nonneg_left hdp hA.le]
    rw [hs] at hbnd ⊢
    nlinarith only [mul_nonneg hA.le hbnd]
  have hzero (C D : Set Ω)
      (h : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ D → adjacencyKernel W p.1 p.2 = 0) :
      ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ D → shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, h] with p hp hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hp
    simpa only [hz hx hy, sub_zero, one_mul] using hp
  have hMPP := hzero P P hPP
  have hMPI := hzero P I hPI
  have hMPJ := hzero P J hPJ
  have hMII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → shiftedKernel W m p.1 p.2 = 0 :=
    hzero I I ((singleton_zero_II (S := S) i).mono (fun _ hp hx hy => hp hx.2 hy.2))
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  have huq : kernelEnergy (μ := μ) (shiftedKernel W m) u = 0 := by
    rw [MissingFlow.OneCenter.energy_sourceDirection _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) hsym hP hI hMPP hMPI]
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff' (hI.prod hI)).mpr (hMII.mono (fun _ hp hx => hp hx.1 hx.2))
  have hvq : kernelEnergy (μ := μ) (shiftedKernel W m) v = R.cuspRemainderEnergy i :=
    MissingFlow.OneCenter.energy_sourceDirection _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) hsym hP hJ hMPP hMPJ
  have hvu : kernelPairing (μ := μ) (shiftedKernel W m) v u = A * R.cuspCrossEnergy i := by
    rw [kernelPairing_symm _ hsym v u,
      pairing_sourceDirections _ hsym P I J hI hJ hMPP hMPI hMPJ]
    change crossIntegral μ (shiftedKernel W m) J I =
      A * (crossIntegral μ (shiftedKernel W m) J I / A)
    field_simp
  have he := tangent_bound hW hd hgap v u hv hu hvm hum A s (R.cuspCrossEnergy i)
    (R.cuspCrossEnergy_nonnegative hW i) huq hvu hduNeg hcompare
  rwa [hvq] at he

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
