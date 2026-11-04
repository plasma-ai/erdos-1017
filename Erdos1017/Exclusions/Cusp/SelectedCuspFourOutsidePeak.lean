module

public import Erdos1017.Exclusions.Cusp.CuspFourOutsidePeakScalar
public import Erdos1017.Exclusions.Cusp.SelectedCuspFourBounds
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.SelectedModel.SelectedHeadPeak

/-!
# No outside original peak at the fourth cusp

At the fourth reciprocal cusp, the original common peak cannot lie outside the
recovered head and the entire source, with both scalar sectors paid
(`no_cusp_four_outside_original_peak`).
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
private theorem four_outside_missing_blocks (R : S.ReverseRecovery) (r i : S.I)
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


private theorem four_avoiding_forward_split (i : S.I) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 < -m) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L) :
    2 * (c - m * d) + m ≤ 2 * Benchmark.splitValue (S.originalAtomMass i) -
      (-m) * (S.originalAtomMass i) ^ 2 := by
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hret := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  change S.forwardClassMass q i = S.originalAtomMass i at hret
  let := hq.endpoint_probability
  let : NullSingletonClass (missingFlowEndpointLaw μ q) := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmax (j : S.I) : S.forwardClassMass q j ≤ S.forwardClassMass q i := by
    by_cases hji : j = i
    · rw [hji]
    · have hsep := (hpeak q hq).2.2 j hji
      have hDelta := (S.exists_original_atomic_square_reserve hW hd hgap).1
      linarith
  have hcost := MultipartiteClassMasses.objective_le_split_add_tail hq.endpoint
    (hq.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [hq.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp) i (hpeak q hq).1 hmax
  change objective hq.endpoint ≤ Benchmark.splitValue (S.forwardClassMass q i) +
    (1 - 2 * density hq.endpoint - (S.forwardClassMass q i) ^ 2) / 2 at hcost
  have hp := hq.classMass_properties
  have hs : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith [(hp.1 j).1, (hp.1 j).2])
  have hsingle := hs.le_tsum i (fun _ _ => sq_nonneg _)
  rw [← hq.missing_density_eq_classMass_sq hW hd hgap] at hsingle
  have htail := mul_nonneg (show 0 ≤ -m - 1 by linarith) (sub_nonneg.mpr hsingle)
  have hbudget := hq.endpoint_budget hW
  have hE := hq.energy_nonnegative hW hd hgap
  rw [hret] at hcost htail
  nlinarith only [hcost, htail, hbudget, hE]


set_option maxHeartbeats 800000 in
/-- At the fourth reciprocal cusp, the actual original common peak cannot
lie outside the recovered head and entire source. The two scalar sectors
are paid by the actual reverse and distinct avoiding-forward endpoints. -/
theorem no_cusp_four_outside_original_peak (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 15 / 32) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r}) (hpeak : S.IsCommonForwardPeak d c i)
    (hout : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∉ {x | S.ρ x = r.val} ∪ R.cuspSource) : False := by
  have hdk' : d = (1 - 1 / (4 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨hd, hslope, _, _, hmargin⟩ :=
    hW.cusp_contact_parameters 4 (by norm_num) hdk' hgap hglobal
  norm_num only [Nat.cast_ofNat] at hslope hmargin
  have hell : -m ∈ Ioo (11 / 10 : ℝ) (3 / 2) := by norm_num at hslope; exact hslope
  obtain ⟨hDelta, j, hA, hside, hj, _, _, _⟩ :=
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
  let delta := 3 / 2 + m
  have hdelta : delta ∈ Ioo (0 : ℝ) (2 / 5) := by
    dsimp [delta]
    constructor <;> linarith only [hell.1, hell.2]
  have hH := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  change H = R.height ^ 2 + QO at hH
  obtain ⟨hHcap, hheight, _⟩ := R.cusp_four_endpoint_bounds hdk hW hgap hglobal
  change H < 5 / 32 at hHcap
  have hcost := R.cusp_four_endpoint_split hdk hW hgap hglobal
  have hc : 3 / 64 < c := by rw [hdk] at hmargin; norm_num at hmargin; linarith
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hreverse : 0 < Benchmark.splitValue (Real.sqrt H) - 3 / 64 -
      (3 / 2 - delta) * (H - 1 / 16) / 2 := by
    change objective R.isFullReverseFlow.endpoint ≤ Benchmark.splitValue (Real.sqrt H) at hcost
    rw [hdk] at hbudget
    dsimp [H, delta]
    nlinarith only [hc, hcost, hbudget, hE]
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
  have hheightEq : R.height = b + s := by
    simpa only [b, s, cuspSource, hr, originalAtomMass] using R.singleton_height_eq_mass_add_source r hr
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
  obtain ⟨hblocks, _⟩ := R.four_outside_missing_blocks r i hW hd hgap hr hout
  change b ^ 2 + 2 * b * s + qS + A ^ 2 ≤ 1 - 2 * d at hblocks
  have hpartial : 1 - 2 * density R.cuspPartialModel =
      b ^ 2 + 2 * b * s + qS + QO := by
    dsimp [H] at hH
    rw [hheightEq] at hH
    nlinarith only [hdrop, hH, hqS]
  have hAQ : A ^ 2 ≤ QO := by
    change 0 ≤ d - density R.cuspPartialModel at hdrop'
    linarith only [hblocks, hpartial, hdrop']
  have hvariance := R.cusp_endpoint_source_budget_whole r 4 (by norm_num)
    hdk' hW hgap hglobal hr
  norm_num only [Nat.cast_ofNat] at hvariance
  have hrawVariance : (1 / 2 - delta) * QO < delta * (R.height ^ 2 - 1 / 16) := by
    change c - 3 / 64 +
      kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) / 2 +
      (-m - 1) * QO / 2 ≤ (3 / 2 + m) * (R.height ^ 2 - 1 / 16) / 2 at hvariance
    dsimp [delta]
    linarith only [hvariance, hE, hc]
  have hproduct : delta / 16 < (1 / 2 + delta) * H - 2 * QO := by
    have hcostMax := R.isFullReverseFlow.objective_le_mass_bound_sq hW hd hgap R.height
      (R.classMass_le hW)
    rw [hdk] at hbudget hmargin
    dsimp [H, delta]
    dsimp [H] at hH
    nlinarith only [hmargin, hbudget, hcostMax, hH, hE]
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  have hforward := four_avoiding_forward_split i hW hd hgap
    (by linarith only [hell.1]) hpeak hnonlow
  have hrawForward : delta < 16 * (2 * Benchmark.splitValue ((4 * A) / 4) -
      (3 / 2 - delta) * ((4 * A) / 4) ^ 2) := by
    have hnorm : (4 * A) / 4 = A := by ring
    rw [hnorm]
    dsimp [delta]
    change 2 * (c - m * d) + m ≤ 2 * Benchmark.splitValue A - (-m) * A ^ 2 at hforward
    nlinarith only [hmargin, hforward]
  exact CuspFourOutsidePeakScalar.outside_contradiction hdelta (by positivity : 0 < 4 * A)
    hH hheight hHcap (by convert hAQ using 1; ring)
    hrawVariance hproduct hreverse hrawForward

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
