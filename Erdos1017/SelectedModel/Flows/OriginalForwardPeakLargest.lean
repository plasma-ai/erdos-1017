module

public import Erdos1017.Exclusions.Common.ControlledDiffuseAtomization
public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass

/-!
# The forward peak is the largest original atom

A low atom at least as large as a controlled forward peak would force a positive
diffuse high recipient set, which the two independent squares and the strict
benchmark gap exclude, so the common forward peak is the unique largest original
independent atom (`exists_unique_largest_original_forward_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- A whole independent atom contributes its entire original mass to the
outside missing section at almost every point of its actual missing region. -/
theorem ae_atomMass_le_outsideSectionMass_on_missing (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (j : S.I) :
    ∀ᵐ x ∂μ, x ∈ KernelOperator.wholeFiberMissingSet S.ρ j →
      S.originalAtomMass j ≤ S.outsideSectionMass x := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    ((S.ae_kernel_eq_fiber_row j j.property).and hW.moment_mem)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxN
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hx] with y hy hyj
  have he : shiftedKernel W m y x = (j : Lp ℝ 2 μ) x := hy.1 hyj
  refine ⟨le_antisymm (he.trans_le hxN.2) hy.2.1, ?_⟩
  exact fun h => hxN.1 (h.symm.trans hyj)

/-- Actual flow from one original atom can only reach points whose
outside missing section contains that atom's entire original mass. -/
theorem IsFullForwardFlow.ae_atom_source_mass_le_recipient_missing
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m) (j : S.I) :
    ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.2 = j →
      S.originalAtomMass j ≤ S.outsideSectionMass p.1 := by
  have hrows := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_kernel_eq_fiber_row j j.property)
  have hb := S.ae_atomMass_le_outsideSectionMass_on_missing hW j
  filter_upwards [hq.support, hrows, shiftedMoment_symm W m,
    Measure.quasiMeasurePreserving_fst.ae hb] with p hs hr hsym hb hq0 hyj
  apply hb
  have hz := (hs hq0).1
  refine ⟨fun he => hz.2 (he.trans hyj.symm), ?_⟩
  have he : shiftedKernel W m p.2 p.1 = (j : Lp ℝ 2 μ) p.1 := hr hyj
  have hzero : shiftedKernel W m p.2 p.1 = 0 := hsym.trans hz.1
  rw [← he, hzero]

/-- If one source atom is at least as large as the peak, an actual flow
avoiding that peak has no atomic HIGH recipients from that source. -/
theorem IsFullForwardFlow.ae_large_atom_recipients_diffuse
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (i j : S.I) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlarge : S.originalAtomMass i ≤ S.originalAtomMass j)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hhigh : ∀ k : S.I, k ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
      S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
        S.originalAtomMass i - Δ) :
    ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.2 = j →
      p.1 ∈ S.D ∧ p.1 ∈ S.H ∧ S.originalAtomMass j ≤ S.outsideSectionMass p.1 := by
  let : Countable S.I := S.hI.to_subtype
  have hnot : ∀ᵐ p ∂μ.prod μ, ∀ k : S.I,
      q p ≠ 0 → S.ρ p.2 = j → S.ρ p.1 ≠ k := by
    rw [ae_all_iff]
    intro k
    by_cases hki : k = i
    · subst k
      exact havoid.mono (fun _ hp hq0 _ => hp hq0)
    rcases S.hfiberClass k k.property with hH | hL | hN
    · have hb := (ae_restrict_iff'
        (KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ k)).mp
        (S.ae_ownIndependentMass_le_missingRegion hW k k.property)
      have hsource := S.atom_receipt_sources k k.property q
        (hq.support.mono (fun _ hp hq0 => (hp hq0).1))
      filter_upwards [hsource, Measure.quasiMeasurePreserving_snd.ae hb]
        with p hp hb hq0 hyj hxk
      have hbound := hb (hp hxk hq0)
      rw [S.ownIndependentMass_eq_fiber j j.property p.2 hyj] at hbound
      have hcap := hhigh k hki hH
      have hnonneg := S.originalAtomMass_summable.1 k
      change S.originalAtomMass j ≤ _ at hbound
      linarith
    · have hL' := (ae_restrict_iff' (S.hfibers k k.property).1).mp hL
      filter_upwards [hq.support, Measure.quasiMeasurePreserving_fst.ae hL']
        with p hp hl hq0 _ hxk
      exact Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hp hq0).2.1 (hl hxk)
    · have hN' := (ae_restrict_iff' (S.hfibers k k.property).1).mp hN
      filter_upwards [hq.support, Measure.quasiMeasurePreserving_fst.ae hN']
        with p hp hn hq0 _ hxk
      exact Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 (hp hq0).2.1 (hn hxk)
  filter_upwards [hnot, hq.support, hq.ae_atom_source_mass_le_recipient_missing hW j]
    with p hn hs hm hq0 hyj
  refine ⟨?_, (hs hq0).2.1, hm hq0 hyj⟩
  rw [S.hDeq]
  intro hmem
  obtain ⟨r, hr⟩ := mem_iUnion.mp hmem
  obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
  exact hn ⟨r, hrI⟩ hq0 hyj hxr

/-- Full supply on a positive LOW atom forces a positive diffuse HIGH
recipient set if that atom is at least as large as an avoided peak. -/
theorem IsFullForwardFlow.positive_diffuse_high_of_large_low_atom
    {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}
    (hq : S.IsFullForwardFlow q) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (i j : S.I) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlarge : S.originalAtomMass i ≤ S.originalAtomMass j)
    (hjL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j}, x ∈ S.L)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hhigh : ∀ k : S.I, k ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
      S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
        S.originalAtomMass i - Δ) :
    0 < μ (S.D ∩ S.H ∩ {x | S.originalAtomMass i ≤ S.outsideSectionMass x}) := by
  let C := S.D ∩ S.H ∩ {x | S.originalAtomMass i ≤ S.outsideSectionMass x}
  by_contra hpos
  have hnull : μ C = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
  have hnot : ∀ᵐ x ∂μ, x ∉ C := by
    rw [ae_iff]
    have he : {x | ¬x ∉ C} = C := by
      ext x
      simp only [mem_ofPred_eq, not_not]
    rw [he]
    exact hnull
  have hp := hq.ae_large_atom_recipients_diffuse hW i j Δ hΔ hlarge havoid hhigh
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hp
  have hnested := Measure.ae_ae_of_ae_prod hswap
  have hsupply := ae_restrict_of_ae (s := {x | S.ρ x = j}) hq.supply
  obtain ⟨y, hyj, hyL, hys, hyp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers j j.property).2.1.ne'
    (hjL.and (hsupply.and (ae_restrict_of_ae hnested)))
  have hz : MissingFlow.supply μ q y = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hyp, hnot] with x hx hxnot
    by_contra hne
    have hg := hx hne hyj
    exact hxnot ⟨⟨hg.1, hg.2.1⟩, hlarge.trans hg.2.2⟩
  rw [indicator_of_mem hyL] at hys
  linarith

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The controlled diffuse comparison extends to the peak mass by
continuity whenever positive diffuse HIGH mass has at least that missing mass. -/
theorem controlled_diffuse_boundary (S : SelectedHighLowStructure W m)
    {d c A : ℝ} (hA : 0 < A)
    (hcontrolled : ∀ b ∈ Ioc (0 : ℝ) A,
      0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}) →
        2 * (c - m * d) + m ≤ (2 + m) * A ^ 2 + m * b ^ 2)
    (hpositive : 0 < μ (S.D ∩ S.H ∩ {x | A ≤ S.outsideSectionMass x})) :
    2 * (c - m * d) + m ≤ 2 * (1 + m) * A ^ 2 := by
  have hclosed : IsClosed {b : ℝ |
      2 * (c - m * d) + m ≤ (2 + m) * A ^ 2 + m * b ^ 2} :=
    isClosed_le continuous_const (by fun_prop)
  have hsub : Ioo (0 : ℝ) A ⊆ {b : ℝ |
      2 * (c - m * d) + m ≤ (2 + m) * A ^ 2 + m * b ^ 2} := by
    intro b hb
    apply hcontrolled b ⟨hb.1, hb.2.le⟩
    apply hpositive.trans_le (measure_mono _)
    intro x hx
    exact ⟨hx.1, hb.2.trans_le hx.2⟩
  have hmem : A ∈ closure (Ioo (0 : ℝ) A) := by
    rw [closure_Ioo hA.ne]
    exact ⟨hA.le, le_rfl⟩
  have h := closure_minimal hsub hclosed hmem
  change 2 * (c - m * d) + m ≤ (2 + m) * A ^ 2 + m * A ^ 2 at h
  nlinarith

/-- The two original independent squares and strict original benchmark
gap exclude a LOW atom as large as a controlled forward peak. -/
theorem low_atom_mass_lt_controlled_peak (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (hA : 0 < S.originalAtomMass i)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hhigh : ∀ k : S.I, k ≠ i →
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
      S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
        S.originalAtomMass i - Δ)
    (hcontrolled : ∀ b ∈ Ioc (0 : ℝ) (S.originalAtomMass i),
      0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}) →
        2 * (c - m * d) + m ≤ (2 + m) * (S.originalAtomMass i) ^ 2 + m * b ^ 2)
    (j : S.I) (hji : j ≠ i)
    (hjL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j}, x ∈ S.L) :
    S.originalAtomMass j < S.originalAtomMass i := by
  by_contra hlt
  have hlarge : S.originalAtomMass i ≤ S.originalAtomMass j := le_of_not_gt hlt
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hpositive := hq.positive_diffuse_high_of_large_low_atom hW i j Δ hΔ hlarge
    hjL havoid hhigh
  have hboundary := S.controlled_diffuse_boundary hA hcontrolled hpositive
  have hs := hW.strict_gap_structure hd hgap
  have hbase := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
  have hdelta : 0 < 2 * c - (1 - 2 * d) := by linarith
  by_cases hm : 1 + m ≤ 0
  · have hnonpos := mul_nonpos_of_nonpos_of_nonneg hm (sq_nonneg (S.originalAtomMass i))
    linarith [hs.gamma_pos]
  · have hmpos : 0 < 1 + m := lt_of_not_ge hm
    have hpairs := S.two_originalAtomMass_sq_le_missing_density i j hji.symm
    rw [hW.density_eq] at hpairs
    have hsq : 2 * (S.originalAtomMass i) ^ 2 ≤ 1 - 2 * d := by
      nlinarith [S.originalAtomMass_summable.1 j]
    have hmul := mul_le_mul_of_nonneg_left hsq hmpos.le
    nlinarith

/-- A positive unique maximum in a summable real family is separated by
one positive gap from every other member, even for an infinite family. -/
private theorem positive_gap_of_summable_unique_max {ι : Type*}
    (a : ι → ℝ) (hsum : Summable a) (i : ι) (hi : 0 < a i)
    (hlt : ∀ j, j ≠ i → a j < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j, j ≠ i → a j ≤ a i - ε := by
  let f : {j : ι // j ≠ i} → ℝ := fun j => a j.val
  have hs : Summable f := hsum.subtype (fun j => j ≠ i)
  by_cases hpos : ∃ j, 0 < f j
  · obtain ⟨j, _, hmax⟩ := ForwardPeak.exists_positive_max_of_summable f hs hpos
    refine ⟨a i - a j.val, sub_pos.mpr (hlt j.val j.property), ?_⟩
    intro k hki
    have h := hmax ⟨k, hki⟩
    change a k ≤ a j.val at h
    linarith
  · refine ⟨a i, hi, ?_⟩
    intro j hji
    have h : a j ≤ 0 := le_of_not_gt (fun hj => hpos ⟨⟨j, hji⟩, hj⟩)
    linarith

/-- The actual common forward peak is the unique largest original
independent atom. Its positive original mass gap and controlled diffuse
comparison are retained on the same original labels and multiplier. -/
theorem exists_unique_largest_original_forward_peak (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (u : Ω × Ω → ℝ), S.IsFullForwardFlow u →
        0 < S.forwardClassMass u i ∧
        ForwardPeak.massPeak (S.forwardClassMass u) = S.forwardClassMass u i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass u) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i →
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
        S.originalAtomMass k + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
          S.originalAtomMass i - forwardPeakGap d c m) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ k : S.I, k ≠ i →
        S.originalAtomMass k ≤ S.originalAtomMass i - ε) ∧
      ∀ b ∈ Ioc (0 : ℝ) (S.originalAtomMass i),
        0 < μ (S.D ∩ S.H ∩ {x | b < S.outsideSectionMass x}) →
          2 * (c - m * d) + m ≤
            (2 + m) * (S.originalAtomMass i) ^ 2 + m * b ^ 2 := by
  obtain ⟨hΔ, i, hA, hside, hpeak, hhigh, hneutral, hcontrolled⟩ :=
    S.exists_controlled_diffuse_peak_atom hW hd hgap
  have hlt : ∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i := by
    intro k hki
    rcases S.hfiberClass k k.property with hH | hL | hN
    · have hb := hhigh k hki hH
      have hn : 0 ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) := measureReal_nonneg
      change S.originalAtomMass k + _ ≤ S.originalAtomMass i - _ at hb
      linarith
    · exact S.low_atom_mass_lt_controlled_peak hW hd hgap i hA
        (forwardPeakGap d c m) hΔ hhigh hcontrolled k hki hL
    · have hb := hneutral k hki hN
      change S.originalAtomMass k ≤ S.originalAtomMass i - _ at hb
      linarith
  exact ⟨hΔ, i, hA, hside, hpeak, hhigh, hlt,
    positive_gap_of_summable_unique_max S.originalAtomMass S.originalAtomMass_summable.2 i hA hlt,
    hcontrolled⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
