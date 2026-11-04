module

public import Erdos1017.Exclusions.Common.SelectedReverseSourceColumns
public import Erdos1017.Exclusions.Common.SelectedReverseSingletonGeometry

/-!
# Private and shared source patterns of a two-center recovery

This module defines the private sources missing one head and the shared source
missing both, partitions the two-head source into these patterns, and identifies
each head's receipt from the constructed product flow: private mass flows
entirely to its sole head, and the shared receipt fractions sum to the shared
mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The entire original source that misses only the first displayed head. -/
def twoCenterPrivate (S : SelectedHighLowStructure W m) (r u : S.I) : Set Ω :=
  (S.reverseCompulsorySource {r, u} ∩ KernelOperator.wholeFiberMissingSet S.ρ r.val) \
    KernelOperator.wholeFiberMissingSet S.ρ u.val

/-- The entire original source that misses both displayed heads. -/
def twoCenterShared (S : SelectedHighLowStructure W m) (r u : S.I) : Set Ω :=
  S.reverseCompulsorySource {r, u} ∩ KernelOperator.wholeFiberMissingSet S.ρ r.val ∩
    KernelOperator.wholeFiberMissingSet S.ρ u.val

/-- The actual nonempty allowed-label clause exhausts the two-head source
by its three literal original missing-label patterns. -/
theorem twoCenter_source_partition (r u : S.I) :
    S.reverseCompulsorySource {r, u} =
      S.twoCenterPrivate r u ∪ S.twoCenterPrivate u r ∪ S.twoCenterShared r u := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hxv⟩ := hx.2.2.1
    have hp := hx.2.2.2 v hv hxv
    have hru : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val ∨
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val := by
      rcases (show v = r ∨ v = u from by simpa only [Finset.mem_insert, Finset.mem_singleton] using hp) with h | h
      · exact Or.inl (h ▸ hxv)
      · exact Or.inr (h ▸ hxv)
    by_cases hr : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val
    · by_cases hu : x ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val
      · exact Or.inr ⟨⟨hx, hr⟩, hu⟩
      · exact Or.inl (Or.inl ⟨⟨hx, hr⟩, hu⟩)
    · have hu := hru.resolve_left hr
      exact Or.inl (Or.inr ⟨⟨by simpa only [Finset.pair_comm] using hx, hu⟩, hr⟩)
  · rintro ((h | h) | h)
    · exact h.1.1
    · simpa only [Finset.pair_comm] using h.1.1
    · exact h.1.1

/-- The three patterns are genuinely disjoint, independently of null sets. -/
theorem twoCenter_patterns_disjoint (r u : S.I) :
    Disjoint (S.twoCenterPrivate r u) (S.twoCenterPrivate u r) ∧
      Disjoint (S.twoCenterPrivate r u) (S.twoCenterShared r u) ∧
      Disjoint (S.twoCenterPrivate u r) (S.twoCenterShared r u) := by
  exact ⟨disjoint_left.mpr (fun _ h₁ h₂ => h₁.2 h₂.1.2),
    disjoint_left.mpr (fun _ h₁ h₂ => h₁.2 h₂.2),
    disjoint_left.mpr (fun _ h₁ h₂ => h₁.2 h₂.1.2)⟩

/-- Shared incidence is independent of the order in which the heads are named. -/
theorem twoCenterShared_comm (r u : S.I) : S.twoCenterShared r u = S.twoCenterShared u r := by
  ext x
  simp only [twoCenterShared, Finset.pair_comm, mem_inter_iff]
  tauto

namespace ReverseRecovery

variable (R : S.ReverseRecovery)

/-- Original-law actual fraction of a recovered head. -/
def headFraction (r : S.I) : Ω → ℝ :=
  MissingFlow.RestrictedAtomicAssignment.liftFraction S.H R.fractions (R.data.code r)

/-- Shared-source receipt into the first original head, using its actual
physical column fraction rather than a freely chosen split parameter. -/
def sharedReceipt (r u : S.I) : ℝ := ∫ x in S.twoCenterShared r u, R.headFraction r x ∂μ

/-- All three literal source patterns are measurable. -/
theorem measurableSet_twoCenter_patterns [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) :
    MeasurableSet (S.twoCenterPrivate r u) ∧ MeasurableSet (S.twoCenterPrivate u r) ∧
      MeasurableSet (S.twoCenterShared r u) := by
  have hC : MeasurableSet (S.reverseCompulsorySource {r, u}) := by
    simpa only [hp] using R.measurableSet_source
  have hr := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ r.val
  have hu := KernelOperator.measurableSet_wholeFiberMissingSet S.ρ S.hρ u.val
  refine ⟨(hC.inter hr).diff hu, ?_, (hC.inter hr).inter hu⟩
  have hC' : MeasurableSet (S.reverseCompulsorySource {u, r}) := by
    simpa only [Finset.pair_comm] using hC
  exact (hC'.inter hu).diff hr

/-- The actual coded plateau has precisely the two original head codes. -/
theorem codePlateau_eq_pair (r u : S.I) (hp : R.plateau = {r, u}) :
    R.codePlateau = {R.data.code r, R.data.code u} := by
  have h := R.data.plateauLabels_code_image R.codePlateau R.active_codePlateau
  change R.plateau.image R.data.code = R.codePlateau at h
  simp only [hp, Finset.image_insert, Finset.image_singleton] at h
  exact h.symm

/-- The two actual head fractions sum to the entire source indicator. -/
theorem headFraction_add_eq_source (r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u}) :
    R.headFraction r + R.headFraction u =ᵐ[μ]
      (S.reverseCompulsorySource {r, u}).indicator (fun _ => 1) := by
  have h := R.original_entire_source_fractions
  have hcode : R.data.code r ≠ R.data.code u := R.data.code.injective.ne hru
  filter_upwards [h] with x hx
  simpa only [R.codePlateau_eq_pair r u hp, Finset.sum_pair hcode, hp,
    headFraction, Pi.add_apply] using hx

/-- Actual lifted fractions are nonnegative and integrable on the original
law, with their original restricted-source integral unchanged. -/
theorem headFraction_properties (r : S.I) :
    Integrable (R.headFraction r) μ ∧ (∀ᵐ x ∂μ, 0 ≤ R.headFraction r x) ∧
      (∫ x, R.headFraction r x ∂μ) = ∫ x, R.fractions (R.data.code r) x ∂μ.restrict S.H := by
  have hi : Integrable (R.headFraction r) μ := by
    apply (integrable_indicator_iff S.hpartition.1).mpr
    exact (Lp.memLp (R.fractions (R.data.code r))).integrable (by norm_num)
  refine ⟨hi, ?_, integral_indicator S.hpartition.1⟩
  have hn := (ae_restrict_iff' S.hpartition.1).mp
    ((R.feasible.box (R.data.code r)).mono (fun _ hx => hx.1))
  filter_upwards [hn] with x hx
  by_cases hH : x ∈ S.H
  · simpa only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
      indicator_of_mem hH] using hx hH
  · simp only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
      indicator_of_notMem hH, le_refl]

/-- An actual eligible head receives nothing from outside its original
whole-row missing set. -/
theorem headFraction_zero_off_missing (r : S.I) (hr : r ∈ R.plateau) :
    ∀ᵐ x ∂μ, x ∉ KernelOperator.wholeFiberMissingSet S.ρ r.val → R.headFraction r x = 0 := by
  have hel := R.plateau_eligible r hr
  have ha : R.data.allowed (R.data.code r) = KernelOperator.wholeFiberMissingSet S.ρ r.val := by
    rw [R.data.hallowed]
    simp only [reverseAllowed, R.data.label_at_code r hel]
  have hs := (ae_restrict_iff' S.hpartition.1).mp (R.feasible.support (R.data.code r))
  filter_upwards [hs] with x hx hn
  by_cases hH : x ∈ S.H
  · change S.H.indicator (fun x => R.fractions (R.data.code r) x) x = 0
    rw [indicator_of_mem hH]
    exact hx hH (by simpa only [ha] using hn)
  · simp only [headFraction, MissingFlow.RestrictedAtomicAssignment.liftFraction,
      indicator_of_notMem hH]

/-- Every actual head receipt is either its compulsory private unit supply
or its actual shared fraction. All other sources contribute zero. -/
theorem headFraction_pattern_decomposition (r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u}) :
    R.headFraction r =ᵐ[μ] fun x =>
      (S.twoCenterPrivate r u).indicator (fun _ => 1) x +
        (S.twoCenterShared r u).indicator (R.headFraction r) x := by
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hu : u ∈ R.plateau := by rw [hp]; simp
  filter_upwards [R.headFraction_add_eq_source r u hru hp,
    (R.headFraction_properties r).2.1, (R.headFraction_properties u).2.1,
    R.headFraction_zero_off_missing r hr, R.headFraction_zero_off_missing u hu]
    with x hs hn hm hz hw
  change R.headFraction r x + R.headFraction u x = _ at hs
  by_cases hc : x ∈ S.reverseCompulsorySource {r, u}
  · rw [indicator_of_mem hc] at hs
    by_cases hi : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val
    · by_cases hj : x ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val
      · have hpv : x ∉ S.twoCenterPrivate r u := fun h => h.2 hj
        have hsh : x ∈ S.twoCenterShared r u := ⟨⟨hc, hi⟩, hj⟩
        rw [indicator_of_notMem hpv, indicator_of_mem hsh, zero_add]
      · have hpv : x ∈ S.twoCenterPrivate r u := ⟨⟨hc, hi⟩, hj⟩
        have hsh : x ∉ S.twoCenterShared r u := fun h => hj h.2
        rw [indicator_of_mem hpv, indicator_of_notMem hsh, add_zero]
        linarith [hw hj]
    · have hpv : x ∉ S.twoCenterPrivate r u := fun h => hi h.1.2
      have hsh : x ∉ S.twoCenterShared r u := fun h => hi h.1.2
      rw [indicator_of_notMem hpv, indicator_of_notMem hsh, add_zero]
      exact hz hi
  · rw [indicator_of_notMem hc] at hs
    have hpv : x ∉ S.twoCenterPrivate r u := fun h => hc h.1.1
    have hsh : x ∉ S.twoCenterShared r u := fun h => hc h.1.1
    rw [indicator_of_notMem hpv, indicator_of_notMem hsh, add_zero]
    linarith

/-- The shared receipt split is nonnegative because it is actual flow. -/
theorem sharedReceipt_nonnegative (r u : S.I) : 0 ≤ R.sharedReceipt r u :=
  integral_nonneg_of_ae (ae_restrict_of_ae (R.headFraction_properties r).2.1)

/-- The shared source's two actual receipt fractions sum to its original mass. -/
theorem sharedReceipt_add [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    R.sharedReceipt r u + R.sharedReceipt u r = μ.real (S.twoCenterShared r u) := by
  have hC := (R.measurableSet_twoCenter_patterns r u hp).2.2
  rw [sharedReceipt, sharedReceipt, ← S.twoCenterShared_comm r u,
    ← integral_add (R.headFraction_properties r).1.integrableOn
      (R.headFraction_properties u).1.integrableOn]
  have he : (fun x => R.headFraction r x + R.headFraction u x) =ᵐ[μ.restrict (S.twoCenterShared r u)]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (R.headFraction_add_eq_source r u hru hp),
      ae_restrict_mem hC] with x hx hc
    change R.headFraction r x + R.headFraction u x = _ at hx
    exact hx.trans (indicator_of_mem hc.1.1 _)
  rw [integral_congr_ae he, setIntegral_const, smul_eq_mul, mul_one]

/-- Each head's actual endpoint cap is its original mass plus all its private
source and its actual shared receipt. -/
theorem twoCenter_head_balance [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    μ.real {x | S.ρ x = r.val} + μ.real (S.twoCenterPrivate r u) +
      R.sharedReceipt r u = R.height := by
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hcode := (R.data.code_mem_iff_plateauLabels R.codePlateau R.active_codePlateau r).mpr hr
  have hm := (R.mass_eq_iff (R.data.code r)).mpr hcode
  have hbase : R.data.a (R.data.code r) = μ.real {x | S.ρ x = r.val} := by
    rw [R.data.ha]
    simp only [reverseAtomMass, R.data.label_at_code r (R.plateau_eligible r hr)]
  rw [ReverseAssignment.mass, hbase, ← (R.headFraction_properties r).2.2,
    integral_congr_ae (R.headFraction_pattern_decomposition r u hru hp)] at hm
  have hmeas := R.measurableSet_twoCenter_patterns r u hp
  rw [integral_add ((integrable_const (1 : ℝ)).indicator hmeas.1)
    ((R.headFraction_properties r).1.indicator hmeas.2.2), integral_indicator hmeas.1,
    integral_indicator hmeas.2.2, setIntegral_const, smul_eq_mul, mul_one] at hm
  exact (add_assoc _ _ _).trans hm

/-- The head fraction is the actual physical original-fiber column of the
constructed product flow. -/
theorem column_on_head_eq_fraction [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    {d c : ℝ} (hW : FullStationaryClass d c W m) (r : S.I) :
    (fun x => ∫ y in {y | S.ρ y = r.val}, R.flow (y, x) ∂μ) =ᵐ[μ] R.headFraction r := by
  have hcol := MissingFlow.CompletedAtomicRelation.setIntegral_column_on_atom
    S.hpartition.1 (S.measurableSet_reverseAllAtomFiber R.data.code)
    (R.data.raw_feasible hW R.fractions R.feasible)
    (S.reverseAllAtomFiber_pairwise R.data.code) (R.data.code r)
  simpa only [S.reverseAllAtomFiber_code, headFraction,
    MissingFlow.RestrictedAtomicAssignment.liftFraction, flow,
    ReverseAssignmentData.completedFlow, reverseAssignmentRelation] using hcol

/-- The split parameter is the actual shared-source flow mass received by
that original head; no physical receipt identification is assumed. -/
theorem sharedReceipt_eq_physical [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    {d c : ℝ} (hW : FullStationaryClass d c W m) (r u : S.I) :
    R.sharedReceipt r u = ∫ x in S.twoCenterShared r u,
      (∫ y in {y | S.ρ y = r.val}, R.flow (y, x) ∂μ) ∂μ := by
  rw [sharedReceipt]
  apply integral_congr_ae
  exact ae_restrict_of_ae (R.column_on_head_eq_fraction hW r).symm

/-- Each private source point supplies one actual unit to its sole head. -/
theorem headFraction_one_on_private (r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u}) :
    ∀ᵐ x ∂μ, x ∈ S.twoCenterPrivate r u → R.headFraction r x = 1 := by
  filter_upwards [R.headFraction_pattern_decomposition r u hru hp] with x hx hi
  have hs : x ∉ S.twoCenterShared r u := fun h =>
    disjoint_left.mp (S.twoCenter_patterns_disjoint r u).2.1 hi h
  simpa only [indicator_of_mem hi, indicator_of_notMem hs, add_zero] using hx

/-- Private source mass is its actual physical receipt into the sole head. -/
theorem private_receipt_eq_mass [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    (∫ x in S.twoCenterPrivate r u,
      (∫ y in {y | S.ρ y = r.val}, R.flow (y, x) ∂μ) ∂μ) =
        μ.real (S.twoCenterPrivate r u) := by
  have hP := (R.measurableSet_twoCenter_patterns r u hp).1
  have he : (fun x => ∫ y in {y | S.ρ y = r.val}, R.flow (y, x) ∂μ) =ᵐ[μ.restrict (S.twoCenterPrivate r u)]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (R.column_on_head_eq_fraction hW r),
      ae_restrict_of_ae (R.headFraction_one_on_private r u hru hp), ae_restrict_mem hP]
      with x hx hy hi
    exact hx.trans (hy hi)
  rw [integral_congr_ae he, setIntegral_const, smul_eq_mul, mul_one]

/-- The actual two-head recovery has its exact private and shared receipt
balances on the original masses, allowing every pattern to be null. -/
theorem twoCenter_receipt_balances [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    0 ≤ R.sharedReceipt r u ∧ 0 ≤ R.sharedReceipt u r ∧
      R.sharedReceipt r u + R.sharedReceipt u r = μ.real (S.twoCenterShared r u) ∧
      μ.real {x | S.ρ x = r.val} + μ.real (S.twoCenterPrivate r u) + R.sharedReceipt r u = R.height ∧
      μ.real {x | S.ρ x = u.val} + μ.real (S.twoCenterPrivate u r) + R.sharedReceipt u r = R.height := by
  exact ⟨R.sharedReceipt_nonnegative r u, R.sharedReceipt_nonnegative u r,
    R.sharedReceipt_add r u hru hp, R.twoCenter_head_balance r u hru hp,
    R.twoCenter_head_balance u r hru.symm (by simpa only [Finset.pair_comm] using hp)⟩

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure
