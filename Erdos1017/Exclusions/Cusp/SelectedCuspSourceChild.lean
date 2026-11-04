module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit
public import Erdos1017.Exclusions.Cusp.WholeSourceChild
public import Erdos1017.SelectedModel.Flows.FullForwardPeakAtom
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence

/-!
# The whole-source child of the cusp recovery

Definitions of the compulsory source, its peak and its remainder (`cuspSource`,
`cuspSourcePeak`, `cuspSourceRemainder`) and of the partial law, whose height is
the sum of the current P, I and J masses and whose missing density is exact. The
one-center source case supplies a fully feasible whole-source child with its
same-profile cost (`exists_cusp_source_child`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The entire compulsory source of this actual recovered plateau. -/
def cuspSource (R : S.ReverseRecovery) : Set Ω := S.reverseCompulsorySource R.plateau

/-- Cutting only null exceptions makes the source decomposition literal.
The actual original whole-atom restriction is recovered below. -/
def cuspSourcePeak (R : S.ReverseRecovery) (i : S.I) : Set Ω :=
  R.cuspSource ∩ {x | S.ρ x = i.val}

/-- The entire remaining source is retained, including its genuine dust. -/
def cuspSourceRemainder (R : S.ReverseRecovery) (i : S.I) : Set Ω :=
  R.cuspSource \ {x | S.ρ x = i.val}

/-- Only sources outside the actual entire compulsory source are moved. -/
def cuspPartialFlow (R : S.ReverseRecovery) : Ω × Ω → ℝ :=
  MissingFlow.sourceSlice R.cuspSourceᶜ R.flow

/-- The current partial-endpoint probability law is explicit. -/
def cuspPartialLaw (R : S.ReverseRecovery) : Measure Ω :=
  missingFlowEndpointLaw μ R.cuspPartialFlow

/-- The original decorated kernel under that actual complementary-source law. -/
def cuspPartialModel (R : S.ReverseRecovery) : Model Ω R.cuspPartialLaw :=
  R.isFullReverseFlow.retainedEndpoint R.measurableSet_source

/-- The density drop is defined by actual graph densities. -/
def cuspDensityDrop (R : S.ReverseRecovery) (d : ℝ) : ℝ := d - density R.cuspPartialModel

theorem measurableSet_cuspSource (R : S.ReverseRecovery) : MeasurableSet R.cuspSource :=
  R.measurableSet_source

theorem measurableSet_cuspSourcePeak (R : S.ReverseRecovery) (i : S.I) :
    MeasurableSet (R.cuspSourcePeak i) :=
  R.measurableSet_source.inter (S.hfibers i.val i.property).1

theorem measurableSet_cuspSourceRemainder (R : S.ReverseRecovery) (i : S.I) :
    MeasurableSet (R.cuspSourceRemainder i) :=
  R.measurableSet_source.diff (S.hfibers i.val i.property).1

theorem cuspPartialLaw_probability (R : S.ReverseRecovery) : IsProbabilityMeasure R.cuspPartialLaw :=
  R.isFullReverseFlow.retainedEndpoint_probability R.measurableSet_source

theorem cuspPartialLaw_ac (R : S.ReverseRecovery) : R.cuspPartialLaw ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem cuspPartialModel_fullFeasible (R : S.ReverseRecovery) (hW : FullFeasible W) :
    FullFeasible R.cuspPartialModel :=
  R.isFullReverseFlow.retainedEndpoint_fullFeasible R.measurableSet_source hW

theorem cuspPartialModel_moment (R : S.ReverseRecovery) (f : CappedColor → ℝ) (p : Ω × Ω) :
    R.cuspPartialModel.moment f p = W.moment f p := rfl

private theorem cuspPartialLaw_restrict_of_weight_one (R : S.ReverseRecovery)
    (C : Set Ω) (hC : MeasurableSet C)
    (hw : ∀ᵐ x ∂μ, x ∈ C → R.retainedWeight x = 1) :
    R.cuspPartialLaw.restrict C = μ.restrict C := by
  change (μ.withDensity (fun x => ENNReal.ofReal (R.retainedWeight x))).restrict C = _
  rw [restrict_withDensity hC]
  calc
    _ = (μ.restrict C).withDensity (fun _ => 1) := by
      apply withDensity_congr_ae
      apply (ae_restrict_iff' hC).mpr
      filter_upwards [hw] with x hx hmem
      rw [hx hmem]
      norm_num
    _ = _ := withDensity_one

/-- The current law agrees with the original law on the entire source. -/
theorem cuspPartialLaw_restrict_source (R : S.ReverseRecovery) :
    R.cuspPartialLaw.restrict R.cuspSource = μ.restrict R.cuspSource :=
  R.cuspPartialLaw_restrict_of_weight_one _ R.measurableSet_source R.retainedWeight_on_source

theorem cuspPartialLaw_restrict_peak (R : S.ReverseRecovery) (i : S.I) :
    R.cuspPartialLaw.restrict (R.cuspSourcePeak i) = μ.restrict (R.cuspSourcePeak i) := by
  have hs : R.cuspSourcePeak i ⊆ R.cuspSource := inter_subset_left
  calc
    _ = (R.cuspPartialLaw.restrict R.cuspSource).restrict (R.cuspSourcePeak i) :=
      (Measure.restrict_restrict_of_subset hs).symm
    _ = (μ.restrict R.cuspSource).restrict (R.cuspSourcePeak i) := by
      rw [R.cuspPartialLaw_restrict_source]
    _ = _ := Measure.restrict_restrict_of_subset hs

theorem cuspPartialLaw_restrict_remainder (R : S.ReverseRecovery) (i : S.I) :
    R.cuspPartialLaw.restrict (R.cuspSourceRemainder i) = μ.restrict (R.cuspSourceRemainder i) := by
  have hs : R.cuspSourceRemainder i ⊆ R.cuspSource := sdiff_subset
  calc
    _ = (R.cuspPartialLaw.restrict R.cuspSource).restrict (R.cuspSourceRemainder i) :=
      (Measure.restrict_restrict_of_subset hs).symm
    _ = (μ.restrict R.cuspSource).restrict (R.cuspSourceRemainder i) := by
      rw [R.cuspPartialLaw_restrict_source]
    _ = _ := Measure.restrict_restrict_of_subset hs

/-- The source cut changes only null exceptions of the original whole atom. -/
theorem cuspSourcePeak_restrict_eq_original (R : S.ReverseRecovery) (i : S.I)
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    μ.restrict (R.cuspSourcePeak i) = μ.restrict {x | S.ρ x = i.val} := by
  apply Measure.restrict_congr_set
  have hi := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hinside
  filter_upwards [hi] with x hx
  apply propext
  change (x ∈ R.cuspSource ∧ S.ρ x = i.val) ↔ S.ρ x = i.val
  exact ⟨fun h => h.2, fun h => ⟨hx h, h⟩⟩

/-- Both the current reweighting and the source cut retain the original
whole-atom measure, so later row integrals may use either representative. -/
theorem cuspPartialLaw_restrict_original_peak (R : S.ReverseRecovery) (i : S.I)
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    R.cuspPartialLaw.restrict (R.cuspSourcePeak i) = μ.restrict {x | S.ρ x = i.val} := by
  rw [R.cuspPartialLaw_restrict_peak i, R.cuspSourcePeak_restrict_eq_original i hinside]

theorem cuspPartialLaw_mass_source (R : S.ReverseRecovery) :
    R.cuspPartialLaw.real R.cuspSource = μ.real R.cuspSource := by
  simpa only [measureReal_restrict_apply_univ] using
    congrArg (fun ν : Measure Ω => ν.real univ) R.cuspPartialLaw_restrict_source

theorem cuspPartialLaw_mass_remainder (R : S.ReverseRecovery) (i : S.I) :
    R.cuspPartialLaw.real (R.cuspSourceRemainder i) = μ.real (R.cuspSourceRemainder i) := by
  simpa only [measureReal_restrict_apply_univ] using
    congrArg (fun ν : Measure Ω => ν.real univ) (R.cuspPartialLaw_restrict_remainder i)

theorem cuspSourcePeak_mass_original (R : S.ReverseRecovery) (i : S.I)
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    μ.real (R.cuspSourcePeak i) = S.originalAtomMass i := by
  simpa only [measureReal_restrict_apply_univ, originalAtomMass] using
    congrArg (fun ν : Measure Ω => ν.real univ) (R.cuspSourcePeak_restrict_eq_original i hinside)

theorem cuspPartialLaw_mass_peak (R : S.ReverseRecovery) (i : S.I)
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    R.cuspPartialLaw.real (R.cuspSourcePeak i) = S.originalAtomMass i := by
  simpa only [measureReal_restrict_apply_univ, originalAtomMass] using
    congrArg (fun ν : Measure Ω => ν.real univ) (R.cuspPartialLaw_restrict_original_peak i hinside)

theorem cuspSource_mass_decomposition (R : S.ReverseRecovery) (i : S.I) :
    μ.real (R.cuspSourcePeak i) + μ.real (R.cuspSourceRemainder i) = μ.real R.cuspSource :=
  measureReal_inter_add_sdiff (S.hfibers i.val i.property).1

theorem cuspSource_disjoint_peak_remainder (R : S.ReverseRecovery) (i : S.I) :
    Disjoint (R.cuspSourcePeak i) (R.cuspSourceRemainder i) :=
  disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)

/-- A positive actual source edge integral forces a positive entire
remainder after removing the independent whole peak. -/
theorem cuspSourceRemainder_mass_pos (R : S.ReverseRecovery) (i : S.I)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) :
    0 < μ.real (R.cuspSourceRemainder i) := by
  by_contra hpos
  have hz : μ (R.cuspSourceRemainder i) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    exact le_antisymm (le_of_not_gt hpos) ENNReal.toReal_nonneg
  have hs : ∀ᵐ x ∂μ, x ∈ R.cuspSource → S.ρ x = i.val := by
    rw [ae_iff]
    have he : {x | ¬(x ∈ R.cuspSource → S.ρ x = i.val)} = R.cuspSourceRemainder i := by
      ext x
      simp only [cuspSourceRemainder, Set.mem_sdiff, mem_ofPred_eq]
      tauto
    rw [he]
    exact hz
  have hi := singleton_zero_II (S := S) i
  have hzero : (∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 0 := by
    apply integral_eq_zero_of_ae
    apply (ae_restrict_iff' (R.measurableSet_source.prod R.measurableSet_source)).mpr
    filter_upwards [hi, Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae hs] with p hp hx hy hmem
    exact hp (hx hmem.1) (hy hmem.2)
  linarith

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The complementary-source endpoint retains the original head law. -/
theorem cuspPartialLaw_restrict_head (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) :
    R.cuspPartialLaw.restrict {x | S.ρ x = r.val} = μ.restrict {x | S.ρ x = r.val} :=
  R.cuspPartialLaw_restrict_of_weight_one _ (S.hfibers r.val r.property).1
    (R.retainedWeight_on_singleton_atom r hW hr)

theorem cuspPartialLaw_mass_head (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r}) :
    R.cuspPartialLaw.real {x | S.ρ x = r.val} = S.originalAtomMass r := by
  simpa only [measureReal_restrict_apply_univ, originalAtomMass] using
    congrArg (fun ν : Measure Ω => ν.real univ) (R.cuspPartialLaw_restrict_head r hW hr)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

theorem cuspDensityDrop_nonnegative (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) : 0 ≤ R.cuspDensityDrop d :=
  sub_nonneg.mpr (R.isFullReverseFlow.retainedEndpoint_density_le hW hd hgap R.measurableSet_source)

/-- The current-law source remainder missing integral, written with the
original law whose restriction on J is proved unchanged. -/
def cuspRemainderMissing (R : S.ReverseRecovery) (i : S.I) : ℝ :=
  ∫ p in (R.cuspSourceRemainder i) ×ˢ (R.cuspSourceRemainder i),
    1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ

/-- The outside profile uses its current masses, after the actual partial flow. -/
def cuspOutsideSquares (R : S.ReverseRecovery) (r i : S.I) : ℝ :=
  WholeSourceChild.outsideSquares R.cuspPartialLaw S.collapsedPartLabel
    {x | S.ρ x = r.val} (R.cuspSourcePeak i) (R.cuspSourceRemainder i)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The endpoint is supported on the literal retained head/source/outside
partition; removed HIGH points are null under this actual law. -/
theorem cuspPartialLaw_ae_partition (R : S.ReverseRecovery) (r : S.I)
    (hr : R.plateau = {r}) :
    ∀ᵐ x ∂R.cuspPartialLaw, x ∈ {x | S.ρ x = r.val} ∪ R.cuspSource ∪
      singletonOther (S := S) r := by
  have hzero : ∀ᵐ x ∂μ, x ∉ {x | S.ρ x = r.val} ∪ R.cuspSource ∪
      singletonOther (S := S) r → R.retainedWeight x = 0 := by
    simpa only [cuspSource, hr] using R.retainedWeight_zero_off_singleton r hr
  have hmeas := ((S.hfibers r.val r.property).1.union R.measurableSet_source).union
    (S.hpartition.1.compl.diff (S.hfibers r.val r.property).1)
  have hac : R.cuspPartialLaw ≪ μ.restrict
      ({x | S.ρ x = r.val} ∪ R.cuspSource ∪ singletonOther (S := S) r) :=
    weightedMeasure_ac_restrict_of_ae_zero R.retainedWeight _ hmeas hzero
  exact hac.ae_le (ae_restrict_mem hmeas)

private theorem original_half_support (_R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (b : Bool) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.half b → p.2 ∈ S.half b →
      adjacencyKernel W p.1 p.2 =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 := by
  have hs := S.ae_collapsed_half_support hW hd hgap b
  rw [Measure.prod_restrict] at hs
  exact ((ae_restrict_iff' ((S.measurableSet_half b).prod (S.measurableSet_half b))).mp hs).mono
    (fun _ hp hx hy => hp ⟨hx, hy⟩)

/-- The actual source and actual outside each retain their own original
multipartite atoms and genuine dust under the current law. -/
theorem cuspPartialLaw_source_outside_support (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    ∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      (p.1 ∈ R.cuspSource ∧ p.2 ∈ R.cuspSource ∨
        p.1 ∈ singletonOther (S := S) r ∧ p.2 ∈ singletonOther (S := S) r) →
      adjacencyKernel W p.1 p.2 =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  filter_upwards [hac.ae_le (R.original_half_support hW hd hgap true),
    hac.ae_le (R.original_half_support hW hd hgap false)] with p hh hl hp
  rcases hp with hp | hp
  · exact hh (Or.inl hp.1.1) (Or.inl hp.2.1)
  · have hnotH (x : Ω) (hx : x ∉ S.H) : x ∈ S.L ∪ S.N := by
      have hu : x ∈ S.H ∪ S.L ∪ S.N := by rw [S.hpartition.2.2.2.1]; exact mem_univ x
      rcases hu with (hH | hL) | hN
      · exact False.elim (hx hH)
      · exact Or.inl hL
      · exact Or.inr hN
    exact hl (hnotH p.1 hp.1.1) (hnotH p.2 hp.2.1)

set_option maxHeartbeats 1000000 in
/-- The current graph supplies the genuine external join, unchanged
outside multipartite blocks and old head nonedges needed by the child. -/
theorem cuspPartialLaw_child_graph (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    (∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      R.cuspPartialModel.moment CappedColor.adjacency p =
        if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) ∧
    (∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      p.1 ∈ R.cuspSourceRemainder i → p.2 ∉ R.cuspSourceRemainder i → S.ρ p.2 ≠ r.val →
        PhysicalRepresentative.adjacency W m p.1 p.2 = true ∧
          PhysicalRepresentative.adjacency W m p.2 p.1 = true) ∧
    (∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
        (p.1 ∉ R.cuspSourceRemainder i ∨ p.2 ∉ R.cuspSourceRemainder i) →
        PhysicalRepresentative.adjacency W m p.1 p.2 =
          WholeSourceChild.outsideAdjacency S.collapsedPartLabel (R.cuspSourcePeak i)
            (R.cuspSourceRemainder i) p.1 p.2) ∧
    (∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      (S.ρ p.1 = r.val → S.ρ p.2 = r.val → PhysicalRepresentative.adjacency W m p.1 p.2 = false) ∧
      (S.ρ p.1 = r.val → p.2 ∈ R.cuspSourcePeak i ∪ R.cuspSourceRemainder i →
        PhysicalRepresentative.adjacency W m p.1 p.2 = false)) := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hSource] at hg
  have hrep := hac.ae_le (PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support)
  have hbinary : ∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      R.cuspPartialModel.moment CappedColor.adjacency p =
        if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0 := by
    filter_upwards [hrep] with p hp
    rw [R.cuspPartialModel_moment]
    exact hp
  have hsoReverse : ∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      p.1 ∈ singletonOther (S := S) r → p.2 ∈ R.cuspSource →
        adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [hac.ae_le (adjacencyKernel_symm W),
      hac.ae_le (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.joined_CO)]
      with p hs hp hx hy
    exact hs.trans (hp hy hx)
  refine ⟨hbinary, ?_, ?_, ?_⟩
  all_goals
    filter_upwards [hsoReverse, hbinary, hac.ae_le hg.zero_II, hac.ae_le hg.zero_IC,
      hac.ae_le hg.joined_CO, R.cuspPartialLaw_source_outside_support r hW hd hgap,
      Measure.quasiMeasurePreserving_fst.ae (R.cuspPartialLaw_ae_partition r hr),
      Measure.quasiMeasurePreserving_snd.ae (R.cuspPartialLaw_ae_partition r hr)]
      with p hsoRev hbin hpp hps hso hhalf hxpart hypart
    have htrue (hv : adjacencyKernel W p.1 p.2 = 1) :
        PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
      by_contra hn
      rw [ite_eq_right hn] at hbin
      change adjacencyKernel W p.1 p.2 = 0 at hbin
      linarith
    have hfalse (hv : adjacencyKernel W p.1 p.2 = 0) :
        PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
      cases he : PhysicalRepresentative.adjacency W m p.1 p.2
      · rfl
      · rw [he] at hbin
        simp only [ite_true] at hbin
        change adjacencyKernel W p.1 p.2 = 1 at hbin
        linarith
    have hIlabel (x : Ω) (hx : x ∈ R.cuspSourcePeak i) : S.collapsedPartLabel x = some i := by
      have hf : x ∈ S.collapsedPartLabel ⁻¹' {some i} := by
        rw [S.collapsedPartLabel_fiber]
        exact hx.2
      exact hf
    have hJlabel (x : Ω) (hx : x ∈ R.cuspSourceRemainder i) : S.collapsedPartLabel x ≠ some i := by
      intro he
      apply hx.2
      have hf : x ∈ S.collapsedPartLabel ⁻¹' {some i} := he
      rwa [S.collapsedPartLabel_fiber] at hf
    have hIJ (hx : p.1 ∈ R.cuspSourcePeak i) (hy : p.2 ∈ R.cuspSourceRemainder i) :
        adjacencyKernel W p.1 p.2 = 1 := by
      have hh := hhalf (Or.inl ⟨hx.1, hy.1⟩)
      have hn : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 := by
        rw [hIlabel p.1 hx]
        exact Ne.symm (hJlabel p.2 hy)
      split_ifs at hh with h
      · exact hh
      · exact False.elim (h (Or.inl hn))
    have hJI (hx : p.1 ∈ R.cuspSourceRemainder i) (hy : p.2 ∈ R.cuspSourcePeak i) :
        adjacencyKernel W p.1 p.2 = 1 := by
      have hh := hhalf (Or.inl ⟨hx.1, hy.1⟩)
      have hn : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 := by
        rw [hIlabel p.2 hy]
        exact hJlabel p.1 hx
      split_ifs at hh with h
      · exact hh
      · exact False.elim (h (Or.inl hn))
    have hII (hx : p.1 ∈ R.cuspSourcePeak i) (hy : p.2 ∈ R.cuspSourcePeak i) :
        adjacencyKernel W p.1 p.2 = 0 := by
      have hh := hhalf (Or.inl ⟨hx.1, hy.1⟩)
      simpa only [hIlabel p.1 hx, hIlabel p.2 hy, ne_eq, not_true_eq_false,
        reduceCtorEq, false_or, ↓reduceIte] using hh
    have hsplit (x : Ω) (hx : x ∈ R.cuspSource) :
        x ∈ R.cuspSourcePeak i ∨ x ∈ R.cuspSourceRemainder i := by
      by_cases hi : S.ρ x = i.val
      · exact Or.inl ⟨hx, hi⟩
      · exact Or.inr ⟨hx, hi⟩
    have hout (x : Ω)
        (hpart : x ∈ {x | S.ρ x = r.val} ∪ R.cuspSource ∪ singletonOther (S := S) r)
        (hnP : S.ρ x ≠ r.val) (hnI : x ∉ R.cuspSourcePeak i)
        (hnJ : x ∉ R.cuspSourceRemainder i) : x ∈ singletonOther (S := S) r := by
      rcases hpart with (hp | hs) | ho
      · exact False.elim (hnP hp)
      · exact False.elim ((hsplit x hs).elim hnI hnJ)
      · exact ho
  · intro hx hy hnP
    have hv : adjacencyKernel W p.1 p.2 = 1 := by
      by_cases hI : p.2 ∈ R.cuspSourcePeak i
      · exact hJI hx hI
      · exact hso hx.1 (hout p.2 hypart hnP hI hy)
    exact ⟨htrue hv, (PhysicalRepresentative.adjacency_symm W m p.2 p.1).trans (htrue hv)⟩
  · intro hxP hyP hnotJJ
    unfold WholeSourceChild.outsideAdjacency
    by_cases hxI : p.1 ∈ R.cuspSourcePeak i
    · by_cases hyI : p.2 ∈ R.cuspSourcePeak i
      · simp only [hxI, hyI, and_self, ↓reduceIte]
        exact hfalse (hII hxI hyI)
      · have hv : adjacencyKernel W p.1 p.2 = 1 := by
          by_cases hyJ : p.2 ∈ R.cuspSourceRemainder i
          · exact hIJ hxI hyJ
          · exact hso hxI.1 (hout p.2 hypart hyP hyI hyJ)
        simp only [hyI, and_false, ↓reduceIte, hxI, true_or]
        exact htrue hv
    · by_cases hyI : p.2 ∈ R.cuspSourcePeak i
      · have hv : adjacencyKernel W p.1 p.2 = 1 := by
          by_cases hxJ : p.1 ∈ R.cuspSourceRemainder i
          · exact hJI hxJ hyI
          · exact hsoRev (hout p.1 hxpart hxP hxI hxJ) hyI.1
        simp only [hxI, false_and, ↓reduceIte, hyI, true_or, false_or]
        exact htrue hv
      · by_cases hxJ : p.1 ∈ R.cuspSourceRemainder i
        · have hyJ : p.2 ∉ R.cuspSourceRemainder i := hnotJJ.elim
            (fun hx => False.elim (hx hxJ)) id
          have hv := hso hxJ.1 (hout p.2 hypart hyP hyI hyJ)
          simp only [hxI, hyI, false_and, ↓reduceIte, hxJ, true_or, false_or]
          exact htrue hv
        · by_cases hyJ : p.2 ∈ R.cuspSourceRemainder i
          · have hv := hsoRev (hout p.1 hxpart hxP hxI hxJ) hyJ.1
            simp only [hxI, hyI, hxJ, hyJ, false_and, ↓reduceIte, false_or]
            exact htrue hv
          · have hh := hhalf (Or.inr ⟨hout p.1 hxpart hxP hxI hxJ, hout p.2 hypart hyP hyI hyJ⟩)
            simp only [hxI, hyI, hxJ, hyJ, false_and, false_or, ↓reduceIte]
            have he := hbin.symm.trans hh
            cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
              by_cases hq : S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨
                S.collapsedPartLabel p.1 = none <;>
              simp [MultipartiteDustAtomization.adjacency, hA, hq] at he ⊢
  · constructor
    · intro hx hy
      exact hfalse (hpp hx hy)
    · intro hx hy
      exact hfalse (hps hx (hy.elim And.left And.left))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The recovered height is the literal sum of the current P/I/J masses. -/
theorem cuspPartialLaw_halfMass (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    WholeSourceChild.halfMass R.cuspPartialLaw {x | S.ρ x = r.val}
      (R.cuspSourcePeak i) (R.cuspSourceRemainder i) = R.height / 2 := by
  unfold WholeSourceChild.halfMass
  rw [R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_peak i hinside,
    R.cuspPartialLaw_mass_remainder i]
  have hsum := R.cuspSource_mass_decomposition i
  rw [R.cuspSourcePeak_mass_original i hinside] at hsum
  have hheight := R.singleton_height_eq_mass_add_source r hr
  change R.height = S.originalAtomMass r + μ.real (S.reverseCompulsorySource {r}) at hheight
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hSource] at hheight
  linarith

/-- The actual original one-center/source case supplies a full-feasible
whole-source child and its same-current-profile cost. -/
theorem exists_cusp_source_child (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) :
    ∃ child : Model Ω (WholeSourceChild.law R.cuspPartialLaw {x | S.ρ x = r.val}
        (R.cuspSourcePeak i) (R.cuspSourceRemainder i)),
      FullFeasible child ∧
      objective child ≤ max (R.height ^ 2 / 4) (R.cuspOutsideSquares r i) ∧
      objective child = KernelOperator.kernelEnergy (μ := R.cuspPartialLaw) (chargeKernel W)
        (WholeSourceChild.weight {x | S.ρ x = r.val} (R.cuspSourcePeak i) (R.cuspSourceRemainder i)
          (R.height / 2) (S.originalAtomMass i) (μ.real (R.cuspSourceRemainder i))) / 2 -
        (∫ p in (R.cuspSourceRemainder i) ×ˢ (R.cuspSourceRemainder i),
          chargeKernel W p.1 p.2 ∂(WholeSourceChild.law R.cuspPartialLaw {x | S.ρ x = r.val}
            (R.cuspSourcePeak i) (R.cuspSourceRemainder i)).prod
              (WholeSourceChild.law R.cuspPartialLaw {x | S.ρ x = r.val}
                (R.cuspSourcePeak i) (R.cuspSourceRemainder i))) / 2 := by
  let := R.cuspPartialLaw_probability
  let : NullSingletonClass R.cuspPartialLaw := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hg := R.cuspPartialLaw_child_graph r i hW hd hgap hr
  have hPS : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
    rw [cuspSource, hr]
    exact S.disjoint_singleton_fiber_source r
  have hPI : Disjoint {x | S.ρ x = r.val} (R.cuspSourcePeak i) := hPS.mono_right inter_subset_left
  have hPJ : Disjoint {x | S.ρ x = r.val} (R.cuspSourceRemainder i) := hPS.mono_right sdiff_subset
  have ha : 0 < R.cuspPartialLaw.real (R.cuspSourcePeak i) := by
    rw [R.cuspPartialLaw_mass_peak i hinside, originalAtomMass]
    exact ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top _ _)
  have hz : 0 < R.cuspPartialLaw.real (R.cuspSourceRemainder i) := by
    rw [R.cuspPartialLaw_mass_remainder i]
    exact R.cuspSourceRemainder_mass_pos i hsourceEdge
  obtain ⟨child, hchild, _, hvalue, hcost⟩ := WholeSourceChild.exists_child_with_cost
    R.cuspPartialModel (R.cuspPartialModel_fullFeasible hW.full)
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.measurable_adjacency W m)
    (PhysicalRepresentative.adjacency_symm W m) hg.1 S.collapsedPartLabel
    S.measurable_collapsedPartLabel {x | S.ρ x = r.val} (R.cuspSourcePeak i) (R.cuspSourceRemainder i)
    (S.hfibers r.val r.property).1 (R.measurableSet_cuspSourcePeak i)
    (R.measurableSet_cuspSourceRemainder i) hPI hPJ (R.cuspSource_disjoint_peak_remainder i)
    ha hz hg.2.1 hg.2.2.1
  rw [R.cuspPartialLaw_halfMass r i hW hr hinside] at hcost hvalue
  rw [R.cuspPartialLaw_mass_peak i hinside, R.cuspPartialLaw_mass_remainder i] at hvalue
  refine ⟨child, hchild, ?_, hvalue⟩
  have hpow : (R.height / 2) ^ 2 = R.height ^ 2 / 4 := by ring
  simpa only [hpow, cuspOutsideSquares] using hcost

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem energy_three {ν : Measure Ω} [IsProbabilityMeasure ν]
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (f g h : Ω → ℝ) (hf : Integrable f ν) (hg : Integrable g ν) (hh : Integrable h ν) :
    KernelOperator.kernelEnergy (μ := ν) K (fun x => f x + g x + h x) =
      KernelOperator.kernelEnergy (μ := ν) K f + KernelOperator.kernelEnergy (μ := ν) K g +
        KernelOperator.kernelEnergy (μ := ν) K h +
        2 * KernelOperator.kernelPairing (μ := ν) K f g +
        2 * KernelOperator.kernelPairing (μ := ν) K f h +
        2 * KernelOperator.kernelPairing (μ := ν) K g h := by
  have hadd (a b : Ω → ℝ) (ha : Integrable a ν) (hb : Integrable b ν) :=
    KernelOperator.kernelEnergy_sub_mul K hK hB hsym a b ha hb (-1)
  have hfg := hadd f g hf hg
  have hall := hadd (fun x => f x + g x) h (hf.add hg) hh
  simp only [neg_mul, one_mul, sub_neg_eq_add, neg_sq, one_pow] at hfg hall
  have hpair : KernelOperator.kernelPairing (μ := ν) K (fun x => f x + g x) h =
      KernelOperator.kernelPairing (μ := ν) K f h + KernelOperator.kernelPairing (μ := ν) K g h := by
    have he : (fun p : Ω × Ω => K p.1 p.2 * (f p.2 + g p.2) * h p.1) =
        fun p => K p.1 p.2 * f p.2 * h p.1 + K p.1 p.2 * g p.2 * h p.1 := by
      funext p
      ring
    rw [KernelOperator.kernelPairing, he,
      integral_add (KernelOperator.integrable_kernel_bilinear hK hB hf hh)
        (KernelOperator.integrable_kernel_bilinear hK hB hg hh)]
    rfl
  rw [hall, hfg, hpair]
  ring

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem restricted_missing_squares {ν : Measure Ω} [IsProbabilityMeasure ν]
    {κ : Type*} [Countable κ] (q : Ω → Option κ)
    (hq : @Measurable Ω (Option κ) _ ⊤ q) (C : Set Ω) (hC : MeasurableSet C)
    (G : Ω → Ω → ℝ)
    (hG : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → p.2 ∈ C → G p.1 p.2 =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0) :
    (∫ p in C ×ˢ C, 1 - G p.1 p.2 ∂ν.prod ν) =
      ∑' i, (ν.real ((q ⁻¹' {some i}) ∩ C)) ^ 2 := by
  let : MeasurableSpace (Option κ) := ⊤
  let Z := MultipartiteClassMasses.independentPairs q
  let D := (C ×ˢ C) ∩ Z
  have hZ := MultipartiteClassMasses.independentPairs_measurable q hq
  have hD : MeasurableSet D := (hC.prod hC).inter hZ
  have heq : (C ×ˢ C).indicator (fun p => 1 - G p.1 p.2) =ᵐ[ν.prod ν]
      D.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hG] with p hp
    by_cases hc : p ∈ C ×ˢ C
    · rw [indicator_of_mem hc, hp hc.1 hc.2]
      by_cases hz : p ∈ Z
      · have hn := (MultipartiteClassMasses.mem_independentPairs_iff q p).mp hz
        have hd : p ∈ D := ⟨hc, hz⟩
        simp only [hn, ↓reduceIte, sub_zero, indicator_of_mem hd]
      · have hn : q p.1 ≠ q p.2 ∨ q p.1 = none := by
          by_contra hn
          exact hz ((MultipartiteClassMasses.mem_independentPairs_iff q p).mpr hn)
        have hd : p ∉ D := fun h => hz h.2
        simp only [hn, ↓reduceIte, sub_self, indicator_of_notMem hd]
    · have hd : p ∉ D := fun h => hc h.1
      rw [indicator_of_notMem hc, indicator_of_notMem hd]
  have hDu : D = ⋃ i : κ, ((q ⁻¹' {some i}) ∩ C) ×ˢ ((q ⁻¹' {some i}) ∩ C) := by
    ext p
    simp only [D, Z, MultipartiteClassMasses.independentPairs, mem_inter_iff, mem_prod,
      mem_iUnion, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, i, hxi, hyi⟩
      exact ⟨i, ⟨hxi, hx⟩, ⟨hyi, hy⟩⟩
    · rintro ⟨i, ⟨hxi, hx⟩, ⟨hyi, hy⟩⟩
      exact ⟨⟨hx, hy⟩, i, hxi, hyi⟩
  rw [← integral_indicator (hC.prod hC), integral_congr_ae heq,
    integral_indicator hD, setIntegral_const, smul_eq_mul, mul_one]
  have hd : Pairwise (fun i j : κ => Disjoint
      (((q ⁻¹' {some i}) ∩ C) ×ˢ ((q ⁻¹' {some i}) ∩ C))
      (((q ⁻¹' {some j}) ∩ C) ×ˢ ((q ⁻¹' {some j}) ∩ C))) := by
    intro i j hij
    exact disjoint_left.mpr (fun p hp hq => hij (Option.some_injective _ (hp.1.1.symm.trans hq.1.1)))
  have hm (i : κ) : MeasurableSet (((q ⁻¹' {some i}) ∩ C) ×ˢ ((q ⁻¹' {some i}) ∩ C)) :=
    ((hq (measurableSet_singleton (some i))).inter hC).prod
      ((hq (measurableSet_singleton (some i))).inter hC)
  rw [measureReal_def, hDu, measure_iUnion hd hm, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  apply tsum_congr
  intro i
  rw [← measureReal_def, measureReal_prod_prod]
  ring

omit [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem missing_partition {ν : Measure Ω} [IsProbabilityMeasure ν]
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (P C O : Set Ω) (hP : MeasurableSet P) (hC : MeasurableSet C) (hO : MeasurableSet O)
    (hPC : Disjoint P C) (hPO : Disjoint P O) (hCO : Disjoint C O)
    (hcover : ∀ᵐ x ∂ν, x ∈ P ∪ C ∪ O)
    (hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 1)
    (hCP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → p.2 ∈ P → K p.1 p.2 = 1)
    (hOP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ O → p.2 ∈ P → K p.1 p.2 = 0)
    (hOC : ∀ᵐ p ∂ν.prod ν, p.1 ∈ O → p.2 ∈ C → K p.1 p.2 = 0) :
    KernelOperator.kernelEnergy (μ := ν) K (fun _ => 1) =
      (ν.real P) ^ 2 + 2 * ν.real P * ν.real C +
        KernelOperator.kernelEnergy (μ := ν) K (C.indicator (fun _ => 1)) +
        KernelOperator.kernelEnergy (μ := ν) K (O.indicator (fun _ => 1)) := by
  let p := P.indicator (fun _ => (1 : ℝ))
  let c := C.indicator (fun _ => (1 : ℝ))
  let o := O.indicator (fun _ => (1 : ℝ))
  have hp : Integrable p ν := (integrable_const 1).indicator hP
  have hc : Integrable c ν := (integrable_const 1).indicator hC
  have ho : Integrable o ν := (integrable_const 1).indicator hO
  have he : (fun _ : Ω => (1 : ℝ)) =ᵐ[ν] fun x => p x + c x + o x := by
    filter_upwards [hcover] with x hx
    by_cases hxP : x ∈ P
    · have hxC : x ∉ C := fun h => disjoint_left.mp hPC hxP h
      have hxO : x ∉ O := fun h => disjoint_left.mp hPO hxP h
      simp only [p, c, o, indicator_of_mem hxP, indicator_of_notMem hxC,
        indicator_of_notMem hxO, add_zero]
    · by_cases hxC : x ∈ C
      · have hxO : x ∉ O := fun h => disjoint_left.mp hCO hxC h
        simp only [p, c, o, indicator_of_notMem hxP, indicator_of_mem hxC,
          indicator_of_notMem hxO, zero_add, add_zero]
      · have hxO : x ∈ O := hx.elim (fun h => False.elim (h.elim hxP hxC)) id
        simp only [p, c, o, indicator_of_notMem hxP, indicator_of_notMem hxC,
          indicator_of_mem hxO, zero_add]
  have henergy : KernelOperator.kernelEnergy (μ := ν) K (fun _ => 1) =
      KernelOperator.kernelEnergy (μ := ν) K (fun x => p x + c x + o x) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with x hx hy
    rw [← hx, ← hy]
  have hsupp (A : Set Ω) : ∀ᵐ x ∂ν, x ∉ A → A.indicator (fun _ => (1 : ℝ)) x = 0 :=
    Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have hpp := MissingFlow.OneCenter.pairing_eq_const_of_supported K p p P P 1 (hsupp P) (hsupp P) hPP
  have hpc := MissingFlow.OneCenter.pairing_eq_const_of_supported K p c P C 1 (hsupp P) (hsupp C) hCP
  have hpo := MissingFlow.OneCenter.pairing_eq_const_of_supported K p o P O 0 (hsupp P) (hsupp O) hOP
  have hco := MissingFlow.OneCenter.pairing_eq_const_of_supported K c o C O 0 (hsupp C) (hsupp O) hOC
  have hi (A : Set Ω) (hA : MeasurableSet A) : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂ν) = ν.real A := by
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
  have hpint : (∫ x, p x ∂ν) = ν.real P := hi P hP
  have hcint : (∫ x, c x ∂ν) = ν.real C := hi C hC
  simp only [one_mul, zero_mul, hpint, hcint] at hpp hpc hpo hco
  change KernelOperator.kernelEnergy (μ := ν) K p = _ at hpp
  rw [henergy, energy_three K hK hB hsym p c o hp hc ho, hpp, hpc, hpo, hco]
  dsimp only [c, o]
  ring

/-- Exact current missing density. The source term is its literal missing
integral; only the actual outside multipartite classes are summed. -/
theorem cuspPartialLaw_missing_density (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    1 - 2 * density R.cuspPartialModel =
      (S.originalAtomMass r) ^ 2 + 2 * S.originalAtomMass r * μ.real R.cuspSource +
        (S.originalAtomMass i) ^ 2 + R.cuspRemainderMissing i + R.cuspOutsideSquares r i := by
  let ν := R.cuspPartialLaw
  let := R.cuspPartialLaw_probability
  let : Countable S.I := S.hI.to_subtype
  let P := {x | S.ρ x = r.val}
  let I := R.cuspSourcePeak i
  let J := R.cuspSourceRemainder i
  let C := R.cuspSource
  let O := singletonOther (S := S) r
  let K := fun x y => 1 - adjacencyKernel W x y
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hI : MeasurableSet I := R.measurableSet_cuspSourcePeak i
  have hJ : MeasurableSet J := R.measurableSet_cuspSourceRemainder i
  have hC : MeasurableSet C := R.measurableSet_source
  have hO : MeasurableSet O := S.hpartition.1.compl.diff hP
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hSource] at hg
  have hGsym : ∀ᵐ p ∂ν.prod ν, adjacencyKernel W p.1 p.2 = adjacencyKernel W p.2 p.1 :=
    hac.ae_le (adjacencyKernel_symm W)
  have hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν) :=
    aestronglyMeasurable_const.sub ((adjacencyKernel_measurable W).mono_ac hac)
  have hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ 1 := Eventually.of_forall (fun p => by
    have ha := adjacency_moment_mem W p
    change ‖1 - W.moment CappedColor.adjacency p‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha.2)]
    linarith [ha.1])
  have hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1 :=
    hGsym.mono (fun _ hp => by dsimp [K]; rw [hp])
  have hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 1 := by
    filter_upwards [hac.ae_le hg.zero_II] with p hp hx hy
    dsimp [K]
    rw [hp hx hy, sub_zero]
  have hCP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → p.2 ∈ P → K p.1 p.2 = 1 := by
    filter_upwards [hGsym,
      hac.ae_le (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC)]
      with p hs hp hx hy
    have hz : adjacencyKernel W p.2 p.1 = 0 := hp hy hx
    dsimp [K]
    rw [hs, hz, sub_zero]
  have hOP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ O → p.2 ∈ P → K p.1 p.2 = 0 := by
    filter_upwards [hGsym,
      hac.ae_le (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.joined_IO)]
      with p hs hp hx hy
    have hz : adjacencyKernel W p.2 p.1 = 1 := hp hy hx
    dsimp [K]
    rw [hs, hz, sub_self]
  have hOC : ∀ᵐ p ∂ν.prod ν, p.1 ∈ O → p.2 ∈ C → K p.1 p.2 = 0 := by
    filter_upwards [hGsym,
      hac.ae_le (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.joined_CO)]
      with p hs hp hx hy
    have hz : adjacencyKernel W p.2 p.1 = 1 := hp hy hx
    dsimp [K]
    rw [hs, hz, sub_self]
  have htotal := missing_partition K hK hB hsym P C O hP hC hO hg.disjoint_IC hg.disjoint_IO
    hg.disjoint_CO (R.cuspPartialLaw_ae_partition r hr) hPP hCP hOP hOC
  have hII : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 1 := by
    filter_upwards [hac.ae_le (singleton_zero_II (S := S) i)] with p hp hx hy
    dsimp [K]
    rw [hp hx.2 hy.2, sub_zero]
  have hgraph := R.cuspPartialLaw_child_graph r i hW hd hgap hr
  have hJI : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∈ I → K p.1 p.2 = 0 := by
    filter_upwards [hgraph.1, hgraph.2.1] with p hb hp hx hy
    have hnJ : p.2 ∉ J := fun hj => disjoint_left.mp (R.cuspSource_disjoint_peak_remainder i) hy hj
    have hnP : S.ρ p.2 ≠ r.val := fun h => disjoint_left.mp hg.disjoint_IC h hy.1
    have hA := (hp hx hnJ hnP).1
    rw [ite_eq_left hA] at hb
    change adjacencyKernel W p.1 p.2 = 1 at hb
    dsimp [K]
    rw [hb, sub_self]
  let fi := I.indicator (fun _ => (1 : ℝ))
  let fj := J.indicator (fun _ => (1 : ℝ))
  have hii := MissingFlow.OneCenter.pairing_eq_const_of_supported K fi fi I I 1
    (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _))
    (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)) hII
  have hij := MissingFlow.OneCenter.pairing_eq_const_of_supported K fi fj I J 0
    (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _))
    (Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)) hJI
  have hintI : (∫ x, fi x ∂ν) = ν.real I := by
    rw [show fi = I.indicator (fun _ => 1) from rfl, integral_indicator hI,
      setIntegral_const, smul_eq_mul, mul_one]
  simp only [one_mul, zero_mul, hintI] at hii hij
  change KernelOperator.kernelEnergy (μ := ν) K fi = _ at hii
  have hsum : C.indicator (fun _ => (1 : ℝ)) = fun x => fi x + fj x := by
    funext x
    by_cases hc : x ∈ R.cuspSource <;> by_cases hi : S.ρ x = i.val <;>
      simp [C, I, J, fi, fj, cuspSourcePeak, cuspSourceRemainder, hc, hi]
  have hEC : KernelOperator.kernelEnergy (μ := ν) K (C.indicator (fun _ => 1)) =
      (ν.real I) ^ 2 + R.cuspRemainderMissing i := by
    have he := KernelOperator.kernelEnergy_sub_mul K hK hB hsym fi fj
      ((integrable_const 1).indicator hI) ((integrable_const 1).indicator hJ) (-1)
    simp only [neg_mul, one_mul, sub_neg_eq_add, neg_sq, one_pow] at he
    rw [hsum, he, hii, hij, MissingFlow.OneCenter.energy_indicator K hJ]
    have hJJ : (∫ p in J ×ˢ J, K p.1 p.2 ∂ν.prod ν) = R.cuspRemainderMissing i := by
      rw [← Measure.prod_restrict, R.cuspPartialLaw_restrict_remainder i,
        Measure.prod_restrict]
      rfl
    rw [hJJ]
    ring
  have hEO : KernelOperator.kernelEnergy (μ := ν) K (O.indicator (fun _ => 1)) =
      R.cuspOutsideSquares r i := by
    rw [MissingFlow.OneCenter.energy_indicator K hO]
    have hs : ∀ᵐ p ∂ν.prod ν, p.1 ∈ O → p.2 ∈ O → adjacencyKernel W p.1 p.2 =
        if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
        then 1 else 0 :=
      (R.cuspPartialLaw_source_outside_support r hW hd hgap).mono (fun _ hp hx hy => hp (Or.inr ⟨hx, hy⟩))
    rw [restricted_missing_squares (ν := ν) S.collapsedPartLabel S.measurable_collapsedPartLabel O hO
      (adjacencyKernel W) (by
        filter_upwards [hs] with p hp hx hy
        have he := hp hx hy
        split_ifs at he ⊢ <;> exact he)]
    apply tsum_congr
    intro j
    congr 1
    apply measureReal_congr
    filter_upwards [R.cuspPartialLaw_ae_partition r hr] with x hx
    apply propext
    change (S.collapsedPartLabel x = some j ∧ x ∈ O) ↔
      (S.collapsedPartLabel x = some j ∧ x ∉ P ∪ I ∪ J)
    constructor
    · rintro ⟨hq, ho⟩
      refine ⟨hq, ?_⟩
      rintro ((hp | hi) | hj)
      · exact disjoint_left.mp hg.disjoint_IO hp ho
      · exact disjoint_left.mp hg.disjoint_CO hi.1 ho
      · exact disjoint_left.mp hg.disjoint_CO hj.1 ho
    · rintro ⟨hq, hn⟩
      refine ⟨hq, ?_⟩
      rcases hx with (hp | hc) | ho
      · exact False.elim (hn (Or.inl (Or.inl hp)))
      · by_cases hi : S.ρ x = i.val
        · exact False.elim (hn (Or.inl (Or.inr ⟨hc, hi⟩)))
        · exact False.elim (hn (Or.inr ⟨hc, hi⟩))
      · exact ho
  have hE : KernelOperator.kernelEnergy (μ := ν) K (fun _ => 1) = 1 - 2 * density R.cuspPartialModel := by
    unfold KernelOperator.kernelEnergy density
    simp only [mul_one]
    change (∫ p : Ω × Ω, 1 - adjacencyKernel W p.1 p.2 ∂ν.prod ν) = _
    have hiG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (ν.prod ν) := by
      simpa only [mul_one] using
        KernelOperator.integrable_kernel_bilinear ((adjacencyKernel_measurable W).mono_ac hac)
          (hac.ae_le (adjacencyKernel_bound W)) (integrable_const 1) (integrable_const 1)
    rw [integral_sub (integrable_const 1) hiG]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    change _ = 1 - 2 * ((∫ p, W.moment CappedColor.adjacency p ∂ν.prod ν) / 2)
    simp only [adjacencyKernel]
    ring
  rw [hE, hEC, hEO, R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_source,
    R.cuspPartialLaw_mass_peak i hinside] at htotal
  linarith

/-- The same actual density drop gives exactly the hole identity used by
the shared signed cusp child accounting. -/
theorem cusp_source_hole_identity (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    (-m) * R.cuspDensityDrop d - (-m) * ((S.originalAtomMass i) ^ 2 + R.cuspRemainderMissing i +
      (S.originalAtomMass r) ^ 2 + 2 * S.originalAtomMass r * μ.real R.cuspSource) / 2 =
      (-m) * (R.cuspOutsideSquares r i - (1 - 2 * d)) / 2 := by
  have h := R.cuspPartialLaw_missing_density r i hW hd hgap hr hinside
  unfold cuspDensityDrop
  linear_combination (-m / 2) * h

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
