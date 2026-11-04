module

public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak
public import Erdos1017.Exclusions.Common.CliqueStarVariation
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit
public import Erdos1017.Exclusions.Common.SelectedRootRepricing
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedAtomDegree

/-!
# Peak geometry of the one-center smooth `W` recovery

A fixed common original peak in a one-center recovery with a positive entire
source has exactly the original private or saturated universal row pattern
(`exists_smoothW_one_center_peak_geometry`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.Benchmark

private theorem mixedValue_sigmaZero_gt_ninth : (1 / 9 : ℝ) < mixedValue sigmaZero := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  rw [mixedValue_sigmaZero, sqrt_two_epsilonStar,
    splitValue_index_two (by nlinarith : (1 / 3 : ℝ) ≤ (9 - Real.sqrt 21) / 10)
      (by nlinarith : (9 - Real.sqrt 21) / 10 < (1 / 2 : ℝ))]
  have hroot : (41 / 9 : ℝ) < Real.sqrt 21 := by nlinarith
  nlinarith

private theorem benchmark_gt_ninth_of_smoothW {d : ℝ}
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (he : 1 / 2 - d ∈ Ioo epsilonStar epsilonD)
    (hactive : twoHeadCurve (1 / 2 - d) < mixedCurve (1 / 2 - d)) :
    (1 / 9 : ℝ) < benchmark d := by
  have hi := mixedInverse_spec ⟨he.1.le, he.2.le⟩
  have hzero : sigmaZero ∈ Icc sigmaD sigmaZero := ⟨hi.1.1.trans hi.1.2, le_rfl⟩
  have hmin := mixedValue_strictAntiOn.antitoneOn hi.1 hzero hi.1.2
  have hvalue : benchmark d = mixedValue (mixedInverse (1 / 2 - d)) := by
    simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true,
      max_eq_left hactive.le]
    simp only [mixedCurve, not_le.mpr he.1, ite_false, he.2.le, ite_true]
  rw [hvalue]
  exact mixedValue_sigmaZero_gt_ninth.trans_le hmin

end Erdos1017.Benchmark

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

private theorem singleton_objective_le_height_sq
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) (hr : R.plateau = {r}) :
    c ≤ R.height ^ 2 := by
  let C := S.reverseCompulsorySource {r}
  have hA : 0 ≤ ∫ p in C ×ˢ C, adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    apply integral_nonneg_of_ae
    exact ae_restrict_of_ae (Filter.Eventually.of_forall (fun p => (adjacency_moment_mem W p).1))
  have hM : 0 ≤ ∫ p in C ×ˢ C, shiftedKernel W m p.1 p.2 ∂μ.prod μ := by
    apply integral_nonneg_of_ae
    exact ae_restrict_of_ae (hW.moment_mem.mono (fun _ hp => hp.1))
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hcredit := R.singleton_source_credit hW hd hgap r hr
  rw [← R.singleton_height_eq_mass_add_source r hr] at hcredit
  nlinarith [mul_nonneg (show 0 ≤ -m by linarith) hA]

private theorem singleton_height_gt_third
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (r : S.I) (hr : R.plateau = {r}) : 1 / 3 < R.height := by
  have hc : 1 / 9 < c :=
    (Benchmark.benchmark_gt_ninth_of_smoothW hd he hactive).trans hgap
  have hle := R.singleton_objective_le_height_sq hW hd hgap r hr
  have hnonneg : 0 ≤ R.height := by
    rw [R.singleton_height_eq_mass_add_source r hr]
    exact add_nonneg (measureReal_nonneg) (measureReal_nonneg)
  nlinarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem singleton_peak_ne_head
    (hW : FullStationaryClass d c W m) (r : S.I) (hr : R.plateau = {r})
    (hsource : 0 < μ (S.reverseCompulsorySource R.plateau))
    (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) : k ≠ r := by
  intro heq
  subst k
  have hmass := R.common_peak_head_mass r (by rw [hr]; simp) hW hpeak
  have hheight := R.singleton_height_eq_mass_add_source r hr
  rw [← hmass] at hheight
  have hs : 0 < μ.real (S.reverseCompulsorySource {r}) := by
    rw [hr] at hsource
    exact ENNReal.toReal_pos hsource.ne' (measure_ne_top μ _)
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem singleton_whole_row_le (r : S.I) (hm : m ≤ 1) :
    ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property] with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

private theorem singleton_stationary_row_le_neighborhood
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
  have hbound : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) ≤
      (∫ x in N, (1 - m : ℝ) ∂μ) :=
    integral_mono_ae hf.integrableOn (integrable_const (1 - m)).integrableOn
      (ae_restrict_of_ae (singleton_whole_row_le (S := S) r hm))
  rw [hNint, setIntegral_const, smul_eq_mul] at hbound
  simpa only [N, mul_comm] using hbound

private theorem singleton_neighborhood_mass_gt_third
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (r : S.I) :
    1 / 3 < μ.real (S.rootNeighborhood r) := by
  obtain ⟨_, _, hell, _, hgamma, _⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  have hrow := singleton_stationary_row_le_neighborhood (S := S) hW hd hgap r
  have hn : 0 ≤ μ.real (S.rootNeighborhood r) := measureReal_nonneg
  by_contra h
  have hnle : μ.real (S.rootNeighborhood r) ≤ 1 / 3 := le_of_not_gt h
  have hprod := mul_nonneg (show 0 ≤ 1 - m by linarith [hell.2])
    (show 0 ≤ 1 / 3 - μ.real (S.rootNeighborhood r) by linarith)
  nlinarith [hell.1]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem singleton_mass_partition
    (r : S.I) (hr : R.plateau = {r}) :
    μ.real (({x | S.ρ x = r.val} ∪ S.reverseCompulsorySource {r}) ∪
      S.rootNeighborhood r) = R.height + μ.real (S.rootNeighborhood r) := by
  let I : Set Ω := {x | S.ρ x = r.val}
  let C : Set Ω := S.reverseCompulsorySource {r}
  let N := S.rootNeighborhood r
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hC : MeasurableSet C := R.singleton_measurableSet_source r hr
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hIC : Disjoint I C := S.disjoint_singleton_fiber_source r
  have hIN : Disjoint I N := S.rootNeighborhood_disjoint r
  have hCN : Disjoint C N := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_le_of_gt hy.2) (S.mem_singleton_compulsorySource_missing r hx).2
  have hUC : Disjoint (I ∪ C) N := disjoint_union_left.mpr ⟨hIN, hCN⟩
  rw [measureReal_union hUC hN, measureReal_union hIC hC,
    R.singleton_height_eq_mass_add_source r hr]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem singleton_height_add_neighborhood_le_one
    (r : S.I) (hr : R.plateau = {r}) :
    R.height + μ.real (S.rootNeighborhood r) ≤ 1 := by
  rw [← R.singleton_mass_partition r hr]
  exact measureReal_le_one

private theorem singleton_outside_mass_lt_third
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (r : S.I) (hr : R.plateau = {r}) :
    μ.real ((({x | S.ρ x = r.val} ∪ S.reverseCompulsorySource {r}) ∪
      S.rootNeighborhood r)ᶜ) < 1 / 3 := by
  have hm := R.singleton_mass_partition r hr
  have ht := R.singleton_height_gt_third hW hd hgap he hactive r hr
  have hn := singleton_neighborhood_mass_gt_third (S := S) hW hd hgap he hactive hglobal r
  rw [measureReal_compl ((S.hfibers r.val r.property).1.union
    (R.singleton_measurableSet_source r hr) |>.union (S.measurableSet_rootNeighborhood r)),
    probReal_univ, hm]
  linarith

private theorem singleton_peak_source_or_neighborhood
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (r k : S.I) (hr : R.plateau = {r}) (hkr : k ≠ r)
    (hA : 1 / 3 < μ.real {x | S.ρ x = k.val}) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ S.reverseCompulsorySource {r}) ∨
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood r) := by
  by_cases hC : S.fiberCompulsoryPredicate k {r}
  · left
    exact (S.ae_compulsorySource_iff_fiberPredicate k {r} hW).mono
      (fun _ hx => hx.mpr hC)
  have hnotC : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∉ S.reverseCompulsorySource {r} :=
    (S.ae_compulsorySource_iff_fiberPredicate k {r} hW).mono
      (fun _ hx h => hC (hx.mp h))
  rcases S.ae_fiber_missing_or_not k r hW with hmissing | hjoined
  · have hK : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
        x ∈ ((({y | S.ρ y = r.val} ∪ S.reverseCompulsorySource {r}) ∪
          S.rootNeighborhood r)ᶜ) := by
      filter_upwards [hmissing, hnotC, ae_restrict_mem (S.hfibers k.val k.property).1]
        with x hm hc hk
      have hxr : S.ρ x ≠ r.val := fun heq => hkr (Subtype.ext (hk.symm.trans heq))
      have hnotN : x ∉ S.rootNeighborhood r := fun hN => not_le_of_gt hN.2 hm.2
      exact fun h => h.elim (fun h => h.elim (fun h => hxr h) hc) hnotN
    have hle : μ.real {x | S.ρ x = k.val} ≤
        μ.real ((({y | S.ρ y = r.val} ∪ S.reverseCompulsorySource {r}) ∪
          S.rootNeighborhood r)ᶜ) :=
      ENNReal.toReal_mono (measure_ne_top μ _)
        (measure_mono_ae ((ae_restrict_iff' (S.hfibers k.val k.property).1).mp hK))
    have hsmall := R.singleton_outside_mass_lt_third hW hd hgap he hactive hglobal r hr
    exact False.elim (not_le_of_gt hA (hle.trans_lt hsmall).le)
  · right
    filter_upwards [hjoined, ae_restrict_mem (S.hfibers k.val k.property).1] with x hx hk
    have hxr : S.ρ x ≠ r.val := fun heq => hkr (Subtype.ext (hk.symm.trans heq))
    exact ⟨hxr, lt_of_not_ge (fun h => hx ⟨hxr, h⟩)⟩

private theorem singleton_joined_unsaturated_mass
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (k r : S.I) (hkr : k ≠ r)
    (hjoined : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood r)
    (hnot : ¬S.IsSaturatedAtomPair k r) :
    2 * μ.real {x | S.ρ x = k.val} ≤ μ.real (S.rootNeighborhood r) := by
  let I : Set Ω := {x | S.ρ x = k.val}
  let P : Set Ω := {x | S.ρ x = r.val}
  let N := S.rootNeighborhood r
  let Z := N \ I
  have hI : MeasurableSet I := (S.hfibers k.val k.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hZ : MeasurableSet Z := hN.diff hI
  have hblock : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = if true = true then 1 else 0 := by
    have hjoined' := (ae_restrict_iff' hI).mp hjoined
    filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_original_root_adjacency r hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae hjoined', adjacencyKernel_symm W]
      with p hr hj hs hk _
    have h := hr (show S.ρ p.2 = r.val from ‹S.ρ p.2 = r.val›)
    change adjacencyKernel W p.2 p.1 = if p.1 ∈ N then 1 else 0 at h
    rw [ite_eq_left (hj hk)] at h
    exact hs.trans h
  have hmem : ∀ᵐ x ∂μ.restrict P, x ∈ S.rootNeighborhood k := by
    have h := S.ae_rootNeighborhood_on_constant_block k r hW hd hgap true hblock
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem (S.hfibers r.val r.property).1]
      with x hx hρ
    exact (hx hρ).mpr rfl
  have hslack := S.ae_rootChargeRow_lt_one_of_not_saturated k r hkr hW hd hgap hnot
  have hcover : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ S.rootNeighborhood k →
      p.2 ∉ Z → adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [S.ae_original_root_adjacency r hW hd hgap] with p hp hP hNk hnotZ
    by_cases hAdj : adjacencyKernel W p.1 p.2 = 0
    · exact hAdj
    have hNr : p.2 ∈ N := by
      have he := hp hP
      by_cases hz : p.2 ∈ N
      · exact hz
      · change adjacencyKernel W p.1 p.2 = if p.2 ∈ N then 1 else 0 at he
        rw [ite_eq_right hz] at he
        exact False.elim (hAdj he)
    have hI' : p.2 ∈ I := by
      by_contra h
      exact hnotZ ⟨hNr, h⟩
    exact False.elim (hNk.1 hI')
  have hcap := S.root_mass_le_cover_of_unsaturated_head k hW hd hgap
    P Z (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.1 hZ
    hmem hslack hcover
  have hsub := (ae_restrict_iff' hI).mp hjoined
  have hinter : μ.real (N ∩ I) = μ.real I := by
    apply measureReal_congr
    filter_upwards [hsub] with x hx
    exact propext ⟨And.right, fun hi => ⟨hx hi, hi⟩⟩
  have hsplit := measureReal_sdiff_add_inter (μ := μ) (s := N) hI
  rw [hinter] at hsplit
  change μ.real Z + μ.real I = μ.real N at hsplit
  linarith

private theorem singleton_source_fiber_private_row (k p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {p})
    (hsource : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val},
      x ∈ S.reverseCompulsorySource {p}) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1 := by
  have hsrc := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hsource
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsrc,
    singleton_zero_II (S := S) k,
    hswap.ae (singleton_zero_IC (S := S) p hW hd hgap),
    adjacencyKernel_symm W, hW.moment_mem, hW.complementary, S.hcoverage, S.hrelation,
    hswap.ae (R.ae_reverse_pair_to_singleton_source p hW hp),
    actualZeroRelation_symm W m S.ρ] with z hC hself hhead hsym hm hc hcover hrel hraw hZsym hk
  have hxC := hC hk
  by_cases hy : S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val
  · rw [ite_eq_left hy]
    rcases hy with hy | hy
    · exact hself hk hy
    · exact hsym.trans (hhead hy hxC)
  · rw [ite_eq_right hy]
    have hpos : 0 < shiftedKernel W m z.1 z.2 := by
      apply lt_of_le_of_ne hm.1
      intro he
      rcases hcover he.symm with ⟨q, _, hxq, hyq⟩ | hZ
      · exact hy (Or.inl (hyq.trans (hxq.symm.trans hk)))
      · rcases hrel hZ with h | h
        · have hR : (z.2, z.1) ∈ S.reverseAssignmentRelation := ⟨hZsym.mp hZ, h.2.2⟩
          exact hy (Or.inr (hraw hxC hR))
        · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hxC.1 h.2.1
    have hz := (mul_eq_zero.mp hc).resolve_right (ne_of_gt hpos)
    change 1 - adjacencyKernel W z.1 z.2 = 0 at hz
    linarith only [hz]

/-- A fixed common original peak in a genuine one-center recovery with a
positive entire source has exactly the original private or saturated
universal row pattern. The head, mass bounds and saturation are derived. -/
theorem exists_smoothW_one_center_peak_geometry
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 1)
    (hsource : 0 < μ (S.reverseCompulsorySource R.plateau))
    (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) :
    ∃ p : S.I, R.plateau = {p} ∧ k ≠ p ∧
      ((∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
          adjacencyKernel W z.1 z.2 =
            if S.ρ z.2 = k.val ∨ S.ρ z.2 = p.val then 0 else 1) ∨
        (S.IsSaturatedAtomPair k p ∧
          ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
            adjacencyKernel W z.1 z.2 = if S.ρ z.2 = k.val then 0 else 1)) := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨hΔ, i, hA, _, _, hi, _, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  have heq : i = k := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  change 357 / 1000 < μ.real {x | S.ρ x = k.val} at hA
  have hkr := R.singleton_peak_ne_head hW p hp hsource k hpeak
  have hloc := R.singleton_peak_source_or_neighborhood hW hd hgap he hactive hglobal
    p k hp hkr (by linarith : 1 / 3 < μ.real {x | S.ρ x = k.val})
  refine ⟨p, hp, hkr, ?_⟩
  rcases hloc with hsrc | hjoin
  · exact Or.inl (R.singleton_source_fiber_private_row k p hW hd hgap hp hsrc)
  · right
    have hpair : S.IsSaturatedAtomPair k p := by
      by_contra hnot
      have hmass := singleton_joined_unsaturated_mass (S := S) hW hd hgap k p hkr hjoin hnot
      have ht := R.singleton_height_gt_third hW hd hgap he hactive p hp
      have hpartition := R.singleton_height_add_neighborhood_le_one p hp
      linarith
    obtain ⟨hΔ', j, _, hside, hj, _, _, _⟩ :=
      S.exists_original_atomic_square_reserve hW hd hgap
    have heq' : j = k := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ'
    subst j
    have hell := (hW.smoothW_contact_parameters hd hgap he hactive hglobal).2.2.1.2
    have hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.N := by
      rcases hside with hH | hN
      · have hz := hpair.high_head_null hW hd hgap (hell.trans (by norm_num))
        have hraw := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hH
        have heq : μ ({x | S.ρ x = k.val} ∩ S.H) = μ {x | S.ρ x = k.val} := by
          apply measure_congr
          filter_upwards [hraw] with x hx
          exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
        rw [heq] at hz
        exact False.elim ((S.hfibers k.val k.property).2.1.ne' hz)
      · exact hN
    exact ⟨hpair, S.neutral_atom_adjacency k hW hd hgap hN⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
