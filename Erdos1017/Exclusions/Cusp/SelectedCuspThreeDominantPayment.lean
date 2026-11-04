module

public import Erdos1017.Exclusions.Cusp.DominantAtomMarkedEditVariation
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeGeometry
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedAtomDegree

/-!
# Marked payment for the dominant atom

The dominant atom `cuspThreeDominantAtom` and its marked body source are defined
and measurable; marking the entire original U pays its positive body rectangle
plus at most one copy of every mixed remainder charge, and a positive designated
missing atom has a nonnull marked body source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The original whole atom intersected with the literal missing region.
At a positive original incidence this retains the whole atom modulo null sets. -/
def cuspThreeDominantAtom (S : SelectedHighLowStructure W m) (i j : S.I) : Set Ω :=
  {x | S.ρ x = j.val} ∩ S.cuspThreeMissingRegion i

/-- The entire original body region missing the designated source atom. -/
def cuspThreeDominantSource (S : SelectedHighLowStructure W m) (i j : S.I) : Set Ω :=
  S.rootNeighborhood i \ S.rootNeighborhood j

theorem measurableSet_cuspThreeDominantAtom (S : SelectedHighLowStructure W m) (i j : S.I) :
    MeasurableSet (S.cuspThreeDominantAtom i j) :=
  (S.hfibers j.val j.property).1.inter (S.measurableSet_cuspThreeMissingRegion i)

theorem measurableSet_cuspThreeDominantSource (S : SelectedHighLowStructure W m) (i j : S.I) :
    MeasurableSet (S.cuspThreeDominantSource i j) :=
  (S.measurableSet_rootNeighborhood i).diff (S.measurableSet_rootNeighborhood j)

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Marking the entire original U pays its positive body rectangle plus
at most one copy of every mixed remainder charge. The original multiplier
is supplied by the actual exactly density-corrected competitor. -/
theorem cusp_three_dominant_atom_payment (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let P := S.cuspThreeDominantAtom i j
    let U := S.cuspThreeDominantSource i j
    let D := S.rootNeighborhood i
    let R := S.cuspThreeMissingRegion i \ P
    (-m * μ.real P - μ.real R) * μ.real U ≤
      ∫ p in U ×ˢ D, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = i.val}
  let J := S.cuspThreeMissingRegion i
  let P := S.cuspThreeDominantAtom i j
  let U := S.cuspThreeDominantSource i j
  let D := S.rootNeighborhood i
  let R := J \ P
  let E := DominantAtomMarkedEdit.exterior I P
  let T : Ω × Ω → ℝ := fun p => max (Y p.1 p.2) 0
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hP : MeasurableSet P := S.measurableSet_cuspThreeDominantAtom i j
  have hUmeas : MeasurableSet U := S.measurableSet_cuspThreeDominantSource i j
  have hD : MeasurableSet D := S.measurableSet_rootNeighborhood i
  have hR : MeasurableSet R := hJ.diff hP
  have hE : MeasurableSet E := (hI.union hP).compl
  have hID : Disjoint I D := S.rootNeighborhood_disjoint i
  have hPsub : P ⊆ J := fun _ hp => hp.2
  have hIP : Disjoint I P := disjoint_left.mpr (fun _ hi hp => hp.2.1 hi)
  have hUD : U ⊆ D := fun _ hu => hu.1
  have hUE : U ⊆ E := by
    intro x hx hn
    rcases hn with hi | hp
    · exact disjoint_left.mp hID hi hx.1
    · exact hp.2.2 hx.1
  have hIPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ P → A p.1 p.2 = false := by
    filter_upwards [S.ae_root_adjacency i hW hd hgap] with p hp hi hj
    exact Bool.eq_false_iff.mpr (fun ha => hj.2.2 ((hp hi).mp ha))
  have hUPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ U → p.2 ∈ P → A p.1 p.2 = false := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (S.ae_root_adjacency j hW hd hgap)] with p hp hu hj
    apply Bool.eq_false_iff.mpr
    intro ha
    exact hu.2 ((hp hj.1).mp ((PhysicalRepresentative.adjacency_symm W m _ _).trans ha))
  have hpay := dominant_marked_cost_payment W hW hd hgap I P U hI hP hUmeas hUE hIP hIPmiss hUPmiss
  have hY := PhysicalRepresentative.measurable_charge W m
  have hYint : Integrable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable 3
      (Eventually.of_forall (fun p => PhysicalRepresentative.charge_bound W m _ _))
  have hT : Measurable T := hY.max measurable_const
  have hT01 (p : Ω × Ω) : T p ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_right _ _, max_le (PhysicalRepresentative.charge_mem_Icc W m _ _).2 (by norm_num)⟩
  have hTint : Integrable T (μ.prod μ) := Integrable.of_bound hT.aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hT01 p).1]
      exact (hT01 p).2))
  have hlin : (∫ p : Ω × Ω, DominantAtomMarkedEdit.densityLinear A P U p.1 p.2 ∂μ.prod μ) =
      μ.real U * μ.real P := by
    have he : (fun p : Ω × Ω => DominantAtomMarkedEdit.densityLinear A P U p.1 p.2) =ᵐ[μ.prod μ]
        (U ×ˢ P).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hUPmiss] with p hp
      by_cases h : p ∈ U ×ˢ P
      · simp [DominantAtomMarkedEdit.densityLinear, Set.indicator, h, hp h.1 h.2]
      · simp [DominantAtomMarkedEdit.densityLinear, Set.indicator, h]
    rw [integral_congr_ae he, integral_indicator (hUmeas.prod hP), setIntegral_const,
      smul_eq_mul, mul_one, measureReal_prod_prod]
  have hzero : (∫ p in U ×ˢ P, Y p.1 p.2 ∂μ.prod μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hUPmiss, ae_restrict_mem (hUmeas.prod hP)] with p hp hm
    exact PhysicalRepresentative.charge_zero_of_nonedge W m _ _ (hp hm.1 hm.2)
  have hcost : (∫ p : Ω × Ω, DominantAtomMarkedEdit.costLinear Y I P U p.1 p.2 ∂μ.prod μ) =
      ∫ p in U ×ˢ E, T p ∂μ.prod μ := by
    have he := integral_add (hYint.indicator (hUmeas.prod hP)) (hTint.indicator (hUmeas.prod hE))
    rw [integral_indicator (hUmeas.prod hP), integral_indicator (hUmeas.prod hE), hzero, zero_add] at he
    exact he
  have hpartition : E = D ∪ R := by
    ext x
    have hnot : x ∈ D → x ∉ I := fun hd hi => disjoint_left.mp hID hi hd
    change (¬(x ∈ I ∨ x ∈ P)) ↔ (x ∈ D ∨ ((x ∉ I ∧ x ∉ D) ∧ x ∉ P))
    have hpnot : x ∈ P → x ∉ I ∧ x ∉ D := fun hp => hp.2
    tauto
  have hDR : Disjoint D R := disjoint_left.mpr (fun _ hd hr => hr.1.2 hd)
  have hsplit : (∫ p in U ×ˢ E, T p ∂μ.prod μ) =
      (∫ p in U ×ˢ D, T p ∂μ.prod μ) + ∫ p in U ×ˢ R, T p ∂μ.prod μ := by
    rw [hpartition, prod_union]
    exact setIntegral_union
      (disjoint_left.mpr (fun p hp hq => disjoint_left.mp hDR hp.2 hq.2)) (hUmeas.prod hR)
      hTint.integrableOn hTint.integrableOn
  have htax : (∫ p in U ×ˢ R, T p ∂μ.prod μ) ≤ μ.real U * μ.real R := by
    have hb := integral_mono_ae (μ := (μ.prod μ).restrict (U ×ˢ R))
      hTint.integrableOn (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun p => (hT01 p).2))
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
      measureReal_prod_prod] using hb
  rw [hlin, hcost, hsplit] at hpay
  change (-m * μ.real P - μ.real R) * μ.real U ≤ _
  nlinarith only [hpay, htax]

/-- A positive designated missing atom has a nonnull entire marked body
source: its original degree is strictly below the fixed common peak. -/
theorem cusp_three_dominant_source_pos (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1))
    (hPpos : 0 < μ.real (S.cuspThreeDominantAtom i j)) :
    0 < μ.real (S.cuspThreeDominantSource i j) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hdrop := (S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv).2.1
  have hdrop' := (ae_restrict_iff' (S.measurableSet_cuspThreeMissingRegion i)).mp hdrop
  have hdegree := ae_degree_eq_wholeRowDegree W m S.ρ S.hrow (hW.strict_gap_structure hd hgap).strict_support
  have hPne : μ (S.cuspThreeDominantAtom i j) ≠ 0 := by
    intro he
    have hz : μ.real (S.cuspThreeDominantAtom i j) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ _)).mpr he
    linarith only [hPpos, hz]
  obtain ⟨x, hx, hdeg, hdrop⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hPne
    (ae_restrict_of_ae (hdegree.and hdrop'))
  have hlt : wholeRowDegree j.val < wholeRowDegree i.val := by
    rw [hx.1] at hdeg
    exact hdeg ▸ (hdrop hx.2).2
  rw [S.wholeRowDegree_eq_neighborhood_mass j, S.wholeRowDegree_eq_neighborhood_mass i] at hlt
  have hmass := measureReal_inter_add_sdiff (μ := μ) (s := S.rootNeighborhood i)
    (S.measurableSet_rootNeighborhood j)
  have hle : μ.real (S.rootNeighborhood i ∩ S.rootNeighborhood j) ≤ μ.real (S.rootNeighborhood j) :=
    measureReal_mono inter_subset_right
  change 0 < μ.real (S.rootNeighborhood i \ S.rootNeighborhood j)
  linarith only [hmass, hle, hlt]

end Erdos1017.CappedModel.SelectedHighLowStructure
