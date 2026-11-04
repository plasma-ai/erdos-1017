module

public import Erdos1017.Exclusions.Cusp.SelectedCuspEndpointRange
public import Erdos1017.Exclusions.Cusp.CuspOutsidePeakScalar
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.SelectedModel.SelectedHeadPeak

/-!
# No outside original peak at large cusps

A whole original common peak outside the entire singleton source is excluded by
the original reserve and the same full reverse budget, without identifying any
original atom (`no_cusp_outside_original_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

set_option maxHeartbeats 800000 in
private theorem outside_missing_blocks (R : S.ReverseRecovery) (r i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hout : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∉ {x | S.ρ x = r.val} ∪ R.cuspSource) :
    let b := S.originalAtomMass r
    let A := S.originalAtomMass i
    let s := μ.real R.cuspSource
    let qS := ∫ p in R.cuspSource ×ˢ R.cuspSource, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    b ^ 2 + 2 * b * s + qS + A ^ 2 ≤ 1 - 2 * d ∧
      b ^ 2 + qS + A ^ 2 ≤ ∑' j, (S.originalAtomMass j) ^ 2 := by
  classical
  let : Countable S.I := S.hI.to_subtype
  let P := {x | S.ρ x = r.val}
  let I := {x | S.ρ x = i.val}
  let C := R.cuspSource
  let Z := MultipartiteClassMasses.independentPairs S.collapsedPartLabel
  let K := fun p : Ω × Ω => 1 - adjacencyKernel W p.1 p.2
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hC : MeasurableSet C := R.measurableSet_cuspSource
  have hZ : MeasurableSet Z :=
    MultipartiteClassMasses.independentPairs_measurable _ S.measurable_collapsedPartLabel
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hK : Integrable K (μ.prod μ) := (integrable_const 1).sub hG
  have hPP := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hP.prod hP)
  have hII := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hI.prod hI)
  have hPC := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hP.prod hC)
  have hCP := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hC.prod hP)
  have hCC := hK.indicator (hC.prod hC)
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : C = S.reverseCompulsorySource {r} := by dsimp [C, cuspSource]; rw [hr]
  rw [← hSource] at hg
  have hout' : ∀ᵐ x ∂μ, x ∈ I → x ∉ P ∪ C := (ae_restrict_iff' hI).mp hout
  have hhalf := S.ae_collapsed_half_support hW hd hgap true
  rw [Measure.prod_restrict] at hhalf
  have hhalf' := (ae_restrict_iff' ((S.measurableSet_half true).prod
    (S.measurableSet_half true))).mp hhalf
  have hevents := (Measure.quasiMeasurePreserving_fst.ae hout').and
    (Measure.quasiMeasurePreserving_snd.ae hout')
  have hle : (∫ p, ((P ×ˢ P).indicator (fun _ => (1 : ℝ)) p +
      (C ×ˢ C).indicator K p + (I ×ˢ I).indicator (fun _ => (1 : ℝ)) p) +
      (P ×ˢ C).indicator (fun _ => (1 : ℝ)) p +
      (C ×ˢ P).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) ≤ ∫ p, K p ∂μ.prod μ := by
    apply integral_mono_ae ((((hPP.add hCC).add hII).add hPC).add hCP) hK
    filter_upwards [hevents, hg.zero_II, hg.zero_IC,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
      singleton_zero_II (S := S) i, adjacencyKernel_symm W] with p ho hpp hpc hcp hii hsym
    change (p.2 ∈ P → p.1 ∈ C → adjacencyKernel W p.2 p.1 = 0) at hcp
    have hdis : ∀ ⦃x⦄, x ∈ P → x ∉ C := Set.disjoint_left.mp hg.disjoint_IC
    have hnonneg : 0 ≤ K p := sub_nonneg.mpr (adjacency_moment_mem W p).2
    simp only [Pi.add_apply]
    repeat' rw [Set.indicator_apply]
    by_cases hxp : p.1 ∈ P <;> by_cases hyp : p.2 ∈ P <;>
      by_cases hxc : p.1 ∈ C <;> by_cases hyc : p.2 ∈ C <;>
      by_cases hxi : p.1 ∈ I <;> by_cases hyi : p.2 ∈ I
    all_goals first
      | exact False.elim (hdis hxp hxc)
      | exact False.elim (hdis hyp hyc)
      | exact False.elim (ho.1 hxi (Or.inl hxp))
      | exact False.elim (ho.1 hxi (Or.inr hxc))
      | exact False.elim (ho.2 hyi (Or.inl hyp))
      | exact False.elim (ho.2 hyi (Or.inr hyc))
      | skip
    all_goals try simp only [Set.mem_prod, hxp, hyp, hxc, hyc, hxi, hyi,
      and_self, and_true, and_false, ite_true, ite_false, zero_add, add_zero]
    all_goals first
      | exact le_rfl
      | exact hnonneg
      | dsimp [K]; rw [hpp hxp hyp]; norm_num
      | dsimp [K]; rw [hpc hxp hyc]; norm_num
      | have hz := hsym.trans (hcp hyp hxc); dsimp [K]; rw [hz]; norm_num
      | dsimp [K]; rw [hii hxi hyi]; norm_num
  have hleZ : (∫ p, (P ×ˢ P).indicator (fun _ => (1 : ℝ)) p +
      (C ×ˢ C).indicator K p + (I ×ˢ I).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) ≤
      ∫ p, Z.indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ := by
    apply integral_mono_ae ((hPP.add hCC).add hII) ((integrable_const 1).indicator hZ)
    filter_upwards [hevents, hhalf'] with p ho hh
    have hdis : ∀ ⦃x⦄, x ∈ P → x ∉ C := Set.disjoint_left.mp hg.disjoint_IC
    have hpZ : p.1 ∈ P → p.2 ∈ P → p ∈ Z := by
      intro hx hy
      apply mem_iUnion.mpr
      exact ⟨r, by simpa only [S.collapsedPartLabel_fiber] using (show p ∈ P ×ˢ P from ⟨hx, hy⟩)⟩
    have hiZ : p.1 ∈ I → p.2 ∈ I → p ∈ Z := by
      intro hx hy
      apply mem_iUnion.mpr
      exact ⟨i, by simpa only [S.collapsedPartLabel_fiber] using (show p ∈ I ×ˢ I from ⟨hx, hy⟩)⟩
    have hcK : p.1 ∈ C → p.2 ∈ C →
        K p = if p ∈ Z then 1 else 0 := by
      intro hx hy
      have he := hh ⟨Or.inl hx.1, Or.inl hy.1⟩
      change adjacencyKernel W p.1 p.2 = _ at he
      dsimp [K]
      rw [he]
      have hz := MultipartiteClassMasses.mem_independentPairs_iff S.collapsedPartLabel p
      change (p ∈ Z ↔ _) at hz
      split_ifs <;> simp_all
    simp only [Pi.add_apply]
    repeat' rw [Set.indicator_apply]
    by_cases hxp : p.1 ∈ P <;> by_cases hyp : p.2 ∈ P <;>
      by_cases hxc : p.1 ∈ C <;> by_cases hyc : p.2 ∈ C <;>
      by_cases hxi : p.1 ∈ I <;> by_cases hyi : p.2 ∈ I
    all_goals first
      | exact False.elim (hdis hxp hxc)
      | exact False.elim (hdis hyp hyc)
      | exact False.elim (ho.1 hxi (Or.inl hxp))
      | exact False.elim (ho.1 hxi (Or.inr hxc))
      | exact False.elim (ho.2 hyi (Or.inl hyp))
      | exact False.elim (ho.2 hyi (Or.inr hyc))
      | skip
    all_goals try simp only [Set.mem_prod, hxp, hyp, hxc, hyc, hxi, hyi,
      and_self, and_true, and_false, ite_true, ite_false, zero_add, add_zero]
    all_goals first
      | rw [ite_eq_left (hpZ hxp hyp)]
      | rw [ite_eq_left (hiZ hxi hyi)]
      | rw [hcK hxc hyc]
      | skip
    all_goals try split_ifs
    all_goals norm_num
  have hrect (D E : Set Ω) (hD : MeasurableSet D) (hE : MeasurableSet E) :
      (∫ p, (D ×ˢ E).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) = μ.real D * μ.real E := by
    rw [integral_indicator (hD.prod hE), setIntegral_const, smul_eq_mul, mul_one,
      measureReal_prod_prod]
  have hadd {f g : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ))
      (hg : Integrable g (μ.prod μ)) :
      (∫ p, (f + g) p ∂μ.prod μ) = (∫ p, f p ∂μ.prod μ) + ∫ p, g p ∂μ.prod μ :=
    integral_add' hf hg
  have hsum := hadd (((hPP.add hCC).add hII).add hPC) hCP
  rw [hadd ((hPP.add hCC).add hII) hPC, hadd (hPP.add hCC) hII,
    hadd hPP hCC] at hsum
  simp only [Pi.add_apply] at hsum
  rw [hsum, hrect P P hP hP, hrect I I hI hI, hrect P C hP hC, hrect C P hC hP,
    integral_indicator (hC.prod hC), integral_sub (integrable_const 1) hG] at hle
  have hsumZ := hadd (hPP.add hCC) hII
  rw [hadd hPP hCC] at hsumZ
  simp only [Pi.add_apply] at hsumZ
  rw [hsumZ, hrect P P hP hP, hrect I I hI hI, integral_indicator (hC.prod hC),
    integral_indicator hZ, setIntegral_const, smul_eq_mul, mul_one,
    MultipartiteClassMasses.independentPairs_mass _ S.measurable_collapsedPartLabel] at hleZ
  have heq : (∑' j, MultipartiteClassMasses.classMass μ S.collapsedPartLabel j ^ 2) =
      ∑' j, (S.originalAtomMass j) ^ 2 := by
    apply tsum_congr
    intro j
    rw [MultipartiteClassMasses.classMass, S.collapsedPartLabel_fiber]
    rfl
  rw [heq] at hleZ
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  have hd' : (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 2 * d := by
    have hd' := hW.density_eq
    change (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at hd'
    linarith
  rw [hd'] at hle
  constructor <;> dsimp [originalAtomMass, P, I, C] at * <;> nlinarith

set_option maxHeartbeats 800000 in
/-- A whole original common peak outside the entire singleton source is
excluded by the actual original reserve and the same full reverse budget.
No original atom is identified with a surviving endpoint atom. -/
theorem no_cusp_outside_original_peak (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 6 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r}) (hpeak : S.IsCommonForwardPeak d c i)
    (hout : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∉ {x | S.ρ x = r.val} ∪ R.cuspSource) : False := by
  obtain ⟨hd, hslope, hell, _, hmargin⟩ :=
    hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  obtain ⟨hDelta, j, _, _, hj, _, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  let b := S.originalAtomMass r
  let A := S.originalAtomMass i
  let s := μ.real R.cuspSource
  let qS := ∫ p in R.cuspSource ×ˢ R.cuspSource,
    1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let QO := R.cuspWholeOutsideSquares r
  let H := 1 - 2 * density R.isFullReverseFlow.endpoint
  let x := (k : ℝ) * Real.sqrt H
  let t := (k : ℝ) * R.height
  let p := (k : ℝ) * b
  let Z := (k : ℝ) ^ 2 * QO
  let V := (k : ℝ) ^ 2 * (b ^ 2 + qS)
  have hk0 : (0 : ℝ) < k := by positivity
  have hk2 : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk0
  have hcancel : (k : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) = 1 := by field_simp
  have hmissing : 1 - 2 * d = 1 / (k : ℝ) ^ 2 := by rw [hdk]; ring
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hqS : qS = s ^ 2 - ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    dsimp [qS, s]
    rw [integral_sub (integrable_const 1) hG.integrableOn,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod]
    ring
  have hq0 : 0 ≤ qS := integral_nonneg (fun p => sub_nonneg.mpr (adjacency_moment_mem W p).2)
  have hheight : R.height = b + s := by
    simpa only [b, s, cuspSource, hr, originalAtomMass] using R.singleton_height_eq_mass_add_source r hr
  have hH := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  change H = R.height ^ 2 + QO at hH
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  rw [← hSource] at hg
  have hf : MissingFlow.sourceSlice R.cuspSource R.flow =ᵐ[μ.prod μ]
      MissingFlow.OneCenter.sourceDensity μ {x | S.ρ x = r.val} R.cuspSource := by
    filter_upwards [R.sourceSlice_singleton hW r hr] with p hp
    change MissingFlow.sourceSlice R.cuspSource R.flow p =
      MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} p.1 *
        R.cuspSource.indicator (fun _ => 1) p.2
    simpa only [hSource] using hp
  have hdrop : density R.cuspPartialModel - density R.isFullReverseFlow.endpoint =
      (∫ p in R.cuspSource ×ˢ R.cuspSource, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 := by
    have he := R.isFullReverseFlow.endpoint_density_eq_retained_sub (C := R.cuspSource) hg hf
    change density R.isFullReverseFlow.endpoint = density R.cuspPartialModel - _ at he
    linarith
  have hdrop' := R.cuspDensityDrop_nonnegative hW hd hgap
  obtain ⟨hblocks, hsquares⟩ := R.outside_missing_blocks r i hW hd hgap hr hout
  change b ^ 2 + 2 * b * s + qS + A ^ 2 ≤ 1 - 2 * d at hblocks
  change b ^ 2 + qS + A ^ 2 ≤ ∑' j, (S.originalAtomMass j) ^ 2 at hsquares
  have hpartial : 1 - 2 * density R.cuspPartialModel =
      b ^ 2 + 2 * b * s + qS + QO := by
    dsimp [H] at hH
    rw [hheight] at hH
    nlinarith only [hdrop, hH, hqS]
  have hQO : A ^ 2 ≤ QO := by
    change 0 ≤ d - density R.cuspPartialModel at hdrop'
    linarith only [hblocks, hpartial, hdrop']
  have hinventory : 1 / (k : ℝ) ^ 2 ≤ b ^ 2 + 2 * b * s + qS + QO := by
    change 0 ≤ d - density R.cuspPartialModel at hdrop'
    linarith only [hpartial, hmissing, hdrop']
  have hweighted := mul_le_mul_of_nonneg_left hsquares (show 0 ≤ -m by linarith [hell.1])
  have hQweighted := mul_le_mul_of_nonneg_left hQO (show 0 ≤ 2 + m by linarith [hell.2])
  have hrawReserve : (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 <
      (2 + m) * QO - (-m) * (b ^ 2 + qS) := by
    change 2 * (c - m * d) + m + (-m) * (∑' j, (S.originalAtomMass j) ^ 2) ≤ 2 * A ^ 2 at hreserve
    nlinarith only [hmargin, hreserve, hweighted, hQweighted]
  have hbudget := R.cusp_endpoint_source_budget_whole r k (by omega) hdk hW hgap hglobal hr
  have henergy := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have he : 0 < c - ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by
    have hid : 2 * (c - m * d) + m - (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 =
        2 * (c - ((k : ℝ) - 1) / (k : ℝ) ^ 3) := by
      rw [hdk]
      field_simp
      ring
    linarith only [hmargin, hid]
  have hrawVariance : (-m - 1) * QO <
      (2 - 2 / (k : ℝ) + m) * (R.height ^ 2 - 1 / (k : ℝ) ^ 2) := by
    dsimp [QO]
    linarith only [hbudget, henergy, he]
  obtain ⟨hx0, hx2, _, _, hgapSplit⟩ := R.cusp_endpoint_normalized_range k hk hdk hW hgap hglobal
  change 0 ≤ x at hx0
  change x < 2 at hx2
  change 0 < (k : ℝ) ^ 2 * Benchmark.splitValue (x / k) - (1 - 1 / (k : ℝ)) -
    (-m) * (x ^ 2 - 1) / 2 at hgapSplit
  let := R.isFullReverseFlow.endpoint_probability
  have hxH : x ^ 2 = t ^ 2 + Z := by
    have hH0 : 0 ≤ H := by dsimp [H]; linarith [(density_mem R.isFullReverseFlow.endpoint).2]
    dsimp [x, t, Z]
    rw [mul_pow, Real.sq_sqrt hH0, hH]
    ring
  have hpV : p ^ 2 ≤ V := by dsimp [p, V]; nlinarith [mul_nonneg hk2.le hq0]
  have hinv : 1 ≤ V + 2 * p * t - 2 * p ^ 2 + Z := by
    have hi := mul_le_mul_of_nonneg_left hinventory hk2.le
    rw [hcancel] at hi
    dsimp [V, p, t, Z]
    rw [hheight]
    nlinarith only [hi]
  have hres : 2 - 2 / (k : ℝ) - (-m) < (2 - (-m)) * Z - (-m) * V := by
    have hi := mul_lt_mul_of_pos_left hrawReserve hk2
    have hc : (k : ℝ) ^ 2 * ((2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2) =
        2 - 2 / (k : ℝ) + m := by field_simp
    rw [hc] at hi
    dsimp [V, Z]
    nlinarith only [hi]
  have hvar : (-m - 1) * Z < (2 - 2 / (k : ℝ) - (-m)) * (t ^ 2 - 1) := by
    have hi := mul_lt_mul_of_pos_left hrawVariance hk2
    have hc : (k : ℝ) ^ 2 * ((2 - 2 / (k : ℝ) + m) *
        (R.height ^ 2 - 1 / (k : ℝ) ^ 2)) =
        (2 - 2 / (k : ℝ) + m) * ((k : ℝ) ^ 2 * R.height ^ 2 - 1) := by
      field_simp
    rw [hc] at hi
    dsimp [Z, t]
    nlinarith only [hi]
  exact CuspOutsidePeakScalar.outside_contradiction hk ⟨hslope.1.le, hslope.2⟩
    hx0 hx2 hgapSplit hxH hpV hinv hres hvar

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
