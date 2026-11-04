module

public import Erdos1017.Exclusions.Cusp.CuspSourceFinitePivot
public import Erdos1017.Exclusions.Cusp.SelectedCuspOriginalSourceRows
public import Erdos1017.Exclusions.Common.Flows.DiffuseFlowEnergyCredit

/-!
# Finite pivot bound for the remainder energy

A finite comparison on the original probability law gives the radical
remainder-energy bound, the constructed competitor having exact original density
(`cusp_source_finite_pivot_energy_le`).
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

set_option maxHeartbeats 800000 in
/-- A genuine finite comparison on the original probability law gives
its radical remainder-energy bound. The constructed competitor has exact
original density and an unchanged full-feasible dual; it receives no
stationarity or selected-model properties. -/
theorem cusp_source_finite_pivot_energy_le (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) :
    R.cuspRemainderEnergy i / 2 ≤
      ((μ.real (R.cuspSourceRemainder i) + Real.sqrt
        ((μ.real (R.cuspSourceRemainder i)) ^ 2 +
          2 * S.originalAtomMass i * μ.real (R.cuspSourceRemainder i))) / 2) *
        R.cuspCrossEnergy i := by
  let P := {x | S.ρ x = r.val}
  let I := R.cuspSourcePeak i
  let J := R.cuspSourceRemainder i
  let A := S.originalAtomMass i
  let b := S.originalAtomMass r
  let z := μ.real J
  let s := μ.real R.cuspSource
  let q := R.cuspRemainderMissing i
  let deg := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
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
  have hdeg : Integrable (deg : Ω → ℝ) μ := (Lp.memLp deg).integrable (by norm_num)
  have hu : Integrable u μ := MissingFlow.OneCenter.integrable_sourceDirection hP hI
  have hv : Integrable v μ := MissingFlow.OneCenter.integrable_sourceDirection hP hJ
  have hum : (∫ x, u x ∂μ) = 0 := integral_sourceDirection P I hP hI hb
  have hvm : (∫ x, v x ∂μ) = 0 := integral_sourceDirection P J hP hJ hb
  have hgeom := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hgeom
  have hPI : Disjoint P I := hgeom.disjoint_IC.mono_right inter_subset_left
  have hPJ : Disjoint P J := hgeom.disjoint_IC.mono_right sdiff_subset
  have hIJ : Disjoint I J := R.cuspSource_disjoint_peak_remainder i
  have hPP := singleton_zero_II (S := S) r
  have hGPJ : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ J → adjacencyKernel W p.1 p.2 = 0 :=
    hgeom.zero_IC.mono (fun _ hp hx hy => hp hx hy.1)
  have hGPI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ I → adjacencyKernel W p.1 p.2 = 0 :=
    hgeom.zero_IC.mono (fun _ hp hx hy => hp hx hy.1)
  have hGII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → adjacencyKernel W p.1 p.2 = 0 :=
    (singleton_zero_II (S := S) i).mono (fun _ hp hx hy => hp hx.2 hy.2)
  have hPall : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P ∪ R.cuspSource →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [hPP, hgeom.zero_IC] with p hp hc hx hy
    exact hy.elim (hp hx) (hc hx)
  have hgp : (∫ x in P, deg x ∂μ) ≤ b * (1 - b - s) := by
    have he := degree_le_of_missing P (P ∪ R.cuspSource)
      (hP.union R.measurableSet_cuspSource) hPall
    have hbnd := integral_mono_ae hdeg.integrableOn (integrable_const (1 - μ.real
      (P ∪ R.cuspSource))).integrableOn ((ae_restrict_iff' hP).mpr he)
    rw [setIntegral_const, measureReal_union hgeom.disjoint_IC R.measurableSet_cuspSource,
      smul_eq_mul] at hbnd
    change (∫ x in P, deg x ∂μ) ≤ b * (1 - (b + s)) at hbnd
    linarith
  have hgi : (∫ x in I, deg x ∂μ) = A * (1 - b - A) := by
    rw [integral_congr_ae ((ae_restrict_iff' hI).mpr
      (R.cusp_source_peak_degree r i hW hd hgap hr hinside)), setIntegral_const,
      smul_eq_mul, hmass]
  have hgj : (∫ x in J, deg x ∂μ) = z * (1 - b) - q := by
    calc
      _ = rowIntegral μ (adjacencyKernel W) J := integral_congr_ae
        (ae_restrict_of_ae (degree_eq_integral (W := W)))
      _ = _ := R.cusp_original_adjacency_row_remainder r i hW hd hgap hr
  have hq0 : 0 ≤ q := integral_nonneg_of_ae (Eventually.of_forall (fun p =>
    sub_nonneg.mpr (adjacency_moment_mem W p).2))
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hGJJ : crossIntegral μ (adjacencyKernel W) J J = z ^ 2 - q := by
    have hq : q = (∫ p in J ×ˢ J, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) := rfl
    rw [integral_sub (integrable_const 1).integrableOn hG.integrableOn,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod] at hq
    dsimp [crossIntegral, z]
    linarith
  have hqSq : q ≤ z ^ 2 := by
    have hn : 0 ≤ crossIntegral μ (adjacencyKernel W) J J :=
      integral_nonneg_of_ae (Eventually.of_forall (fun p => (adjacency_moment_mem W p).1))
    rw [hGJJ] at hn
    linarith
  have hqAz : q < A * z := R.cusp_remainder_missing_lt_peak_mul_mass i hW hd hgap hpeak hz
  let g := 1 - q / z ^ 2
  let dp := (∫ x in P, deg x ∂μ) / b
  let κ := 1 - b - s - dp
  have hκ : 0 ≤ κ := by
    have hdp : dp ≤ 1 - b - s := (div_le_iff₀ hb).mpr (by nlinarith [hgp])
    dsimp [κ]
    linarith
  have hg : g ∈ Icc (0 : ℝ) 1 := by
    have hqdiv : q / z ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hz)).mpr hqSq
    have hn : 0 ≤ q / z ^ 2 := div_nonneg hq0 (sq_nonneg z)
    constructor <;> dsimp [g] <;> linarith
  have hgEq : g * z ^ 2 = z ^ 2 - q := by dsimp [g]; field_simp
  have hD : 0 < A - (1 - g) * z := by
    have he : (A - (1 - g) * z) * z = A * z - q := by nlinarith only [hgEq]
    nlinarith only [he, hqAz, hz]
  obtain ⟨x, y, hy, hxA, hx0, hxy, hdensity, hprice⟩ :=
    CuspSourceFinitePivot.exists_shift hA hz hg hκ hD
  let f := fun a => -(x / A) * u a - (y / z) * v a
  have hf : Integrable f μ := (hu.const_mul (-(x / A))).sub (hv.const_mul (y / z))
  have hfm : (∫ a, f a ∂μ) = 0 := by
    rw [integral_sub (hu.const_mul _) (hv.const_mul _), integral_const_mul,
      integral_const_mul, hum, hvm]
    ring
  have hfe (a : Ω) : f a = (x / A) * I.indicator (fun _ => 1) a +
      (y / z) * J.indicator (fun _ => 1) a - ((x + y) / b) * P.indicator (fun _ => 1) a := by
    dsimp [f, u, v, MissingFlow.OneCenter.sourceDirection,
      MissingFlow.AtomicAssignment.recipientDensity]
    rw [hmass]
    change -(x / A) * (A * P.indicator (fun _ => b⁻¹) a - I.indicator (fun _ => 1) a) -
      (y / z) * (z * P.indicator (fun _ => b⁻¹) a - J.indicator (fun _ => 1) a) = _
    by_cases ha : a ∈ P
    · rw [indicator_of_mem ha, indicator_of_mem ha]
      field_simp
      ring
    · rw [indicator_of_notMem ha, indicator_of_notMem ha]
      ring
  have hbelow : ∀ᵐ a ∂μ, -1 ≤ f a := Eventually.of_forall (fun a => by
    rw [hfe]
    by_cases haI : a ∈ I
    · have haP : a ∉ P := fun hp => disjoint_left.mp hPI hp haI
      have haJ : a ∉ J := fun hj => disjoint_left.mp hIJ haI hj
      rw [indicator_of_mem haI, indicator_of_notMem haP, indicator_of_notMem haJ]
      simp only [mul_one, mul_zero, add_zero, sub_zero]
      exact (le_div_iff₀ hA).mpr (by linarith)
    · rw [indicator_of_notMem haI]
      have hj : 0 ≤ (y / z) * J.indicator (fun _ => (1 : ℝ)) a :=
        mul_nonneg (div_nonneg hy.le hz.le) (indicator_nonneg (fun _ _ => by norm_num) a)
      have hp : 0 ≤ -((x + y) / b) * P.indicator (fun _ => (1 : ℝ)) a := by
        apply mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hxy hb.le))
        exact indicator_nonneg (fun _ _ => by norm_num) a
      nlinarith)
  have hdu : (∫ a, deg a * u a ∂μ) = -A * (z + κ) := by
    rw [degree_sourceDirection _ hdeg P I hP hI, hmass, hgi]
    change A / b * (∫ a in P, deg a ∂μ) - A * (1 - b - A) = _
    dsimp [κ, dp]
    rw [hs]
    ring
  have hdv : (∫ a, deg a * v a ∂μ) = -z * (A + g * z + κ) := by
    rw [degree_sourceDirection _ hdeg P J hP hJ, hgj]
    change z / b * (∫ a in P, deg a ∂μ) - (z * (1 - b) - q) = _
    dsimp [κ, dp]
    rw [hs]
    linear_combination hgEq
  obtain ⟨B, _, hB⟩ := operator_range_bounded (adjacencyKernel W) (by norm_num)
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))
  have hdegU := integrable_bounded_mul (Lp.memLp deg).aestronglyMeasurable hB hu
  have hdegV := integrable_bounded_mul (Lp.memLp deg).aestronglyMeasurable hB hv
  have hdf : (∫ a, deg a * f a ∂μ) = x * (z + κ) + y * (A + g * z + κ) := by
    have he : (fun a => deg a * f a) =
        fun a => -(x / A) * (deg a * u a) - (y / z) * (deg a * v a) := by
      funext a
      dsimp [f]
      ring
    rw [he, integral_sub (hdegU.const_mul _) (hdegV.const_mul _), integral_const_mul,
      integral_const_mul, hdu, hdv]
    field_simp
    ring
  have hzero (C D : Set Ω)
      (h : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ D → adjacencyKernel W p.1 p.2 = 0) :
      ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ D → shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, h] with p hp hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hp
    simpa only [hz hx hy, sub_zero, one_mul] using hp
  have hMpp := hzero P P hPP
  have hMpi := hzero P I hGPI
  have hMpj := hzero P J hGPJ
  have hMii := hzero I I hGII
  have hMsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hp => hp.symm)
  have hqu (K : Ω → Ω → ℝ)
      (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ)) {B : ℝ}
      (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
      (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
      (hpp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 0)
      (hpi : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ I → K p.1 p.2 = 0)
      (hii : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0) :
      kernelEnergy (μ := μ) K u = 0 := by
    rw [MissingFlow.OneCenter.energy_sourceDirection _ hK hB hsym hP hI hpp hpi]
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff' (hI.prod hI)).mpr (hii.mono (fun _ hp hx => hp hx.1 hx.2))
  have hGIJ : crossIntegral μ (adjacencyKernel W) J I = A * z := by
    unfold crossIntegral
    have he : (∫ p in J ×ˢ I, adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
        ∫ _p in J ×ˢ I, (1 : ℝ) ∂μ.prod μ := by
      apply integral_congr_ae
      apply (ae_restrict_iff' (hJ.prod hI)).mpr
      filter_upwards [R.cusp_original_remainder_row_event r i hW hd hgap hr] with p hp hx
      have hnP : p.2 ∉ P := fun hy => disjoint_left.mp hPI hy hx.2
      have hnJ : p.2 ∉ J := fun hy => disjoint_left.mp hIJ hx.2 hy
      have h := hp hx.1
      rw [indicator_of_notMem hnP, indicator_of_notMem hnJ] at h
      simpa only [sub_zero, zero_mul] using h
    rw [he, setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod, hmass]
    change z * A = A * z
    ring
  have hGvu : kernelPairing (μ := μ) (adjacencyKernel W) v u = A * z := by
    rw [kernelPairing_symm _ (adjacencyKernel_symm W) v u,
      pairing_sourceDirections _ (adjacencyKernel_symm W) P I J hI hJ hPP hGPI hGPJ]
    exact hGIJ
  have hMvu : kernelPairing (μ := μ) (shiftedKernel W m) v u = A * R.cuspCrossEnergy i := by
    rw [kernelPairing_symm _ hMsym v u,
      pairing_sourceDirections _ hMsym P I J hI hJ hMpp hMpi hMpj]
    change crossIntegral μ (shiftedKernel W m) J I =
      A * (crossIntegral μ (shiftedKernel W m) J I / A)
    field_simp
  have hGv : kernelEnergy (μ := μ) (adjacencyKernel W) v = g * z ^ 2 := by
    rw [MissingFlow.OneCenter.energy_sourceDirection _ (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (adjacencyKernel_symm W) hP hJ hPP hGPJ]
    change crossIntegral μ (adjacencyKernel W) J J = _
    rw [hGJJ, hgEq]
  have hMv : kernelEnergy (μ := μ) (shiftedKernel W m) v = R.cuspRemainderEnergy i :=
    MissingFlow.OneCenter.energy_sourceDirection _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) hMsym hP hJ hMpp hMpj
  let t := -x * z / (A * y)
  have hfs : f = fun a => (-y / z) * (v a - t * u a) := by
    funext a
    dsimp [f, t]
    field_simp
    ring
  have hGf : kernelEnergy (μ := μ) (adjacencyKernel W) f = 2 * x * y + g * y ^ 2 := by
    rw [hfs, kernelEnergy_const_mul, kernelEnergy_sub_mul _ (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (adjacencyKernel_symm W) v u hv hu t,
      hqu (adjacencyKernel W) (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
        (adjacencyKernel_symm W) hPP hGPI hGII, hGv, hGvu]
    dsimp [t]
    field_simp
    ring
  have hMf : kernelEnergy (μ := μ) (shiftedKernel W m) f =
      y ^ 2 / z ^ 2 * (R.cuspRemainderEnergy i + 2 * x * z / y * R.cuspCrossEnergy i) := by
    rw [hfs, kernelEnergy_const_mul, kernelEnergy_sub_mul _ (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) hMsym v u hv hu t,
      hqu (shiftedKernel W m) (shiftedKernel_measurable W m)
        (shiftedKernel_bound W m) hMsym hMpp hMpi hMii,
      hMv, hMvu]
    dsimp [t]
    field_simp
    ring
  have hreturn : density (integrableTilt W f hf hfm hbelow 1 (by norm_num)) = d := by
    rw [density_integrableTilt, hW.density_eq, hdf, hGf]
    nlinarith only [hdensity]
  have hMf0 : kernelEnergy (μ := μ) (shiftedKernel W m) f ≤ 0 := by
    by_contra hn
    exact hW.no_density_return_of_positive_energy f hf hfm hbelow (lt_of_not_ge hn)
      1 (by norm_num) (by norm_num) hreturn
  have hcore : R.cuspRemainderEnergy i + 2 * x * z / y * R.cuspCrossEnergy i ≤ 0 := by
    rw [hMf] at hMf0
    by_contra hn
    exact (not_lt_of_ge hMf0) (mul_pos
      (div_pos (sq_pos_of_pos hy) (sq_pos_of_pos hz)) (lt_of_not_ge hn))
  have hPhi := R.cuspCrossEnergy_nonnegative hW i
  have hbnd := mul_le_mul_of_nonneg_right hprice hPhi
  change R.cuspRemainderEnergy i / 2 ≤
    ((z + Real.sqrt (z ^ 2 + 2 * A * z)) / 2) * R.cuspCrossEnergy i
  have he : 2 * x * z / y * R.cuspCrossEnergy i =
      -2 * ((-z * x / y) * R.cuspCrossEnergy i) := by ring
  rw [he] at hcore
  linarith only [hcore, hbnd]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
