module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurData

/-!
# Source direction of a two-center recovery in `L²`

This module defines the head receipts and the private and shared source means as
original `L²` vectors, shows this source partition is an identity of these
means, and represents the physical source-slice direction as an `L²` vector
whose Gram value is its energy, which the full reverse energy dominates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The actual private plus shared original receipt into the first head. -/
def headReceipt (r u : S.I) : ℝ := μ.real (S.twoCenterPrivate r u) + R.sharedReceipt r u

/-- Actual recovered head fractions vanish outside the entire source. -/
theorem headFraction_zero_off_source (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    ∀ᵐ x ∂μ, x ∉ S.reverseCompulsorySource {r, u} → R.headFraction r x = 0 := by
  filter_upwards [R.headFraction_pattern_decomposition r u hru hp] with x hx hn
  have hP : x ∉ S.twoCenterPrivate r u := fun h => hn h.1.1
  have hS : x ∉ S.twoCenterShared r u := fun h => hn h.1.1
  simpa only [indicator_of_notMem hP, indicator_of_notMem hS, add_zero] using hx

/-- The actual original-law fraction integral is its private plus shared
physical receipt, as derived from the recovered original mass identities. -/
theorem integral_headFraction [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) (hp : R.plateau = {r, u}) :
    (∫ x, R.headFraction r x ∂μ) = R.headReceipt r u := by
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hc := (R.data.code_mem_iff_plateauLabels R.codePlateau R.active_codePlateau r).mpr hr
  have hm := (R.mass_eq_iff (R.data.code r)).mpr hc
  have hbase : R.data.a (R.data.code r) = μ.real {x | S.ρ x = r.val} := by
    rw [R.data.ha]
    simp only [reverseAtomMass, R.data.label_at_code r (R.plateau_eligible r hr)]
  rw [ReverseAssignment.mass, hbase, ← (R.headFraction_properties r).2.2] at hm
  have hb := R.twoCenter_head_balance r u hru hp
  dsimp only [headReceipt]
  linarith only [hm, hb]

/-- The actual two-head source slice is its literal original-product
uniform-recipient density, with the actual completed source fractions. -/
theorem sourceSlice_twoCenter_density [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    MissingFlow.sourceSlice (S.reverseCompulsorySource {r, u}) R.flow =ᵐ[μ.prod μ]
      (fun p => MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} p.1 * R.headFraction r p.2 +
        MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = u.val} p.1 * R.headFraction u p.2) := by
  have hpr := R.headFraction_zero_off_source r u hru hp
  have hpu := R.headFraction_zero_off_source u r hru.symm (by simpa only [Finset.pair_comm] using hp)
  filter_upwards [R.ae_plateau_source_iff hW,
    Measure.quasiMeasurePreserving_snd.ae hpr, Measure.quasiMeasurePreserving_snd.ae hpu]
    with p hs hr hu
  by_cases hc : p.2 ∈ S.reverseCompulsorySource {r, u}
  · simp only [MissingFlow.sourceSlice, ite_eq_left hc]
    by_cases hi : S.ρ p.1 = r.val
    · have hir : p.1 ∈ {x | S.ρ x = r.val} := hi
      have hiu : p.1 ∉ {x | S.ρ x = u.val} := fun h => hru (Subtype.ext (hi.symm.trans h))
      change R.flow (p.1, p.2) = _
      rw [R.flow_on_original_atom r p.2 p.1 hi]
      simp only [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_mem hir,
        indicator_of_notMem hiu, zero_mul, add_zero, headFraction]
    · by_cases hj : S.ρ p.1 = u.val
      · have hir : p.1 ∉ {x | S.ρ x = r.val} := hi
        have hiu : p.1 ∈ {x | S.ρ x = u.val} := hj
        change R.flow (p.1, p.2) = _
        rw [R.flow_on_original_atom u p.2 p.1 hj]
        simp only [MissingFlow.AtomicAssignment.recipientDensity, indicator_of_notMem hir,
          indicator_of_mem hiu, zero_mul, zero_add, headFraction]
      · have hz : R.flow p = 0 := by
          by_contra hne
          have hm := (hs hne).mpr (by simpa only [hp] using hc)
          rw [R.plateauRegion_eq_pair r u hp] at hm
          exact hm.elim hi hj
        have hir : p.1 ∉ {x | S.ρ x = r.val} := hi
        have hiu : p.1 ∉ {x | S.ρ x = u.val} := hj
        simp only [hz, MissingFlow.AtomicAssignment.recipientDensity,
          indicator_of_notMem hir, indicator_of_notMem hiu, zero_mul, add_zero]
  · have hzero_r := hr hc
    have hzero_u := hu (by simpa only [Finset.pair_comm] using hc)
    simp only [MissingFlow.sourceSlice, ite_eq_right hc, hzero_r, hzero_u, mul_zero, add_zero]

/-- The literal source slice has its two actual original head receipts. -/
theorem receipt_sourceSlice_twoCenter [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    MissingFlow.receipt μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r, u}) R.flow) =ᵐ[μ]
      fun x => R.headReceipt r u * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} x +
        R.headReceipt u r * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = u.val} x := by
  filter_upwards [Measure.ae_ae_of_ae_prod (R.sourceSlice_twoCenter_density r u hru hW hp)]
    with x hx
  change (∫ y, MissingFlow.sourceSlice (S.reverseCompulsorySource {r, u}) R.flow (x, y) ∂μ) = _
  rw [integral_congr_ae hx,
    integral_add ((R.headFraction_properties r).1.const_mul _) ((R.headFraction_properties u).1.const_mul _),
    integral_const_mul, integral_const_mul, R.integral_headFraction r u hru hp,
    R.integral_headFraction u r hru.symm (by simpa only [Finset.pair_comm] using hp)]
  ring

/-- The physical source direction is the two actual receipt coefficients
minus the entire original source indicator. -/
theorem direction_sourceSlice_twoCenter [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource {r, u}) R.flow) =ᵐ[μ]
      fun x => R.headReceipt r u * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} x +
        R.headReceipt u r * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = u.val} x -
          (S.reverseCompulsorySource {r, u}).indicator (fun _ => 1) x := by
  filter_upwards [R.receipt_sourceSlice_twoCenter r u hru hW hp,
    R.isFullReverseFlow.sourceSlice_supply (show S.reverseCompulsorySource {r, u} ⊆ S.H from fun _ h => h.1)]
    with x hr hs
  change MissingFlow.receipt μ _ x - MissingFlow.supply μ _ x = _
  rw [hr, hs]

/-- The original entire-source mean is an actual original L² indicator. -/
def entireSourceMean : Lp ℝ 2 μ :=
  indicatorVector (S.reverseCompulsorySource R.plateau) R.measurableSet_source

/-- The entire original source mean has its literal original indicator. -/
theorem entireSourceMean_coe : (R.entireSourceMean : Ω → ℝ) =ᵐ[μ]
    (S.reverseCompulsorySource R.plateau).indicator (fun _ => 1) := by
  change (indicatorConstLp 2 R.measurableSet_source
    (measure_ne_top μ (S.reverseCompulsorySource R.plateau)) (1 : ℝ) : Ω → ℝ) =ᵐ[μ] _
  exact indicatorConstLp_coeFn

/-- The actual private source mean retains its literal original pattern. -/
def privateMean [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) : Lp ℝ 2 μ :=
  indicatorVector (S.twoCenterPrivate r u) (R.measurableSet_twoCenter_patterns r u hp).1

/-- The actual shared source mean retains its literal original pattern. -/
def sharedMean [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) : Lp ℝ 2 μ :=
  indicatorVector (S.twoCenterShared r u) (R.measurableSet_twoCenter_patterns r u hp).2.2

/-- The actual private mean has its literal original indicator. -/
theorem privateMean_coe [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) :
    (R.privateMean r u hp : Ω → ℝ) =ᵐ[μ] (S.twoCenterPrivate r u).indicator (fun _ => 1) := by
  change (indicatorConstLp 2 (R.measurableSet_twoCenter_patterns r u hp).1
    (measure_ne_top μ (S.twoCenterPrivate r u)) (1 : ℝ) : Ω → ℝ) =ᵐ[μ] _
  exact indicatorConstLp_coeFn

/-- The actual shared mean has its literal original indicator. -/
theorem sharedMean_coe [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) :
    (R.sharedMean r u hp : Ω → ℝ) =ᵐ[μ] (S.twoCenterShared r u).indicator (fun _ => 1) := by
  change (indicatorConstLp 2 (R.measurableSet_twoCenter_patterns r u hp).2.2
    (measure_ne_top μ (S.twoCenterShared r u)) (1 : ℝ) : Ω → ℝ) =ᵐ[μ] _
  exact indicatorConstLp_coeFn

/-- Reversing head names leaves the same actual shared-source mean. -/
theorem sharedMean_comm [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) :
    R.sharedMean u r (by simpa only [Finset.pair_comm] using hp) = R.sharedMean r u hp := by
  apply Lp.ext
  filter_upwards [R.sharedMean_coe u r (by simpa only [Finset.pair_comm] using hp),
    R.sharedMean_coe r u hp] with x hx hy
  rw [S.twoCenterShared_comm u r] at hx
  exact hx.trans hy.symm

/-- The exact source partition is an identity of the actual original
L² means, even for empty source patterns. -/
theorem sourceMeans_add [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hp : R.plateau = {r, u}) :
    R.privateMean r u hp + R.privateMean u r (by simpa only [Finset.pair_comm] using hp) +
      R.sharedMean r u hp = R.entireSourceMean := by
  let c₁ := R.privateMean r u hp
  let c₂ := R.privateMean u r (by simpa only [Finset.pair_comm] using hp)
  let c₁₂ := R.sharedMean r u hp
  have hd := S.twoCenter_patterns_disjoint r u
  have hds : Disjoint (S.twoCenterPrivate r u ∪ S.twoCenterPrivate u r) (S.twoCenterShared r u) :=
    disjoint_union_left.mpr ⟨hd.2.1, hd.2.2⟩
  have hi : (S.reverseCompulsorySource R.plateau).indicator (fun _ => (1 : ℝ)) =
      (S.twoCenterPrivate r u).indicator (fun _ => 1) +
        (S.twoCenterPrivate u r).indicator (fun _ => 1) + (S.twoCenterShared r u).indicator (fun _ => 1) := by
    rw [hp, S.twoCenter_source_partition r u, indicator_union_of_disjoint hds,
      indicator_union_of_disjoint hd.1]
    funext x
    rfl
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (c₁ + c₂) c₁₂, Lp.coeFn_add c₁ c₂,
    R.privateMean_coe r u hp,
    R.privateMean_coe u r (by simpa only [Finset.pair_comm] using hp),
    R.sharedMean_coe r u hp,
    R.entireSourceMean_coe]
    with x ha hb hc hd he hf
  change (c₁ + c₂ + c₁₂) x = R.entireSourceMean x
  rw [ha, Pi.add_apply, hb, Pi.add_apply, hc, hd, he, hf]
  exact (congrFun hi x).symm

/-- The actual original L² representative of the entire source direction. -/
def sourceDirectionL2 (r u : S.I) : Lp ℝ 2 μ :=
  R.headReceipt r u • S.normalizedHead r + R.headReceipt u r • S.normalizedHead u - R.entireSourceMean

/-- The constructed original L² vector represents the actual physical
source-slice direction, with no supplied direction identification. -/
theorem sourceDirectionL2_coe [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    (R.sourceDirectionL2 r u : Ω → ℝ) =ᵐ[μ]
      MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow) := by
  have hdir : MissingFlow.direction μ
      (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow) =ᵐ[μ]
      fun x => R.headReceipt r u * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = r.val} x +
        R.headReceipt u r * MissingFlow.AtomicAssignment.recipientDensity μ {x | S.ρ x = u.val} x -
          (S.reverseCompulsorySource R.plateau).indicator (fun _ => 1) x := by
    simpa only [hp] using R.direction_sourceSlice_twoCenter r u hru hW hp
  filter_upwards [Lp.coeFn_sub
    (R.headReceipt r u • S.normalizedHead r + R.headReceipt u r • S.normalizedHead u) R.entireSourceMean,
    Lp.coeFn_add (R.headReceipt r u • S.normalizedHead r) (R.headReceipt u r • S.normalizedHead u),
    Lp.coeFn_smul (R.headReceipt r u) (S.normalizedHead r),
    Lp.coeFn_smul (R.headReceipt u r) (S.normalizedHead u),
    S.normalizedHead_coe r, S.normalizedHead_coe u,
    R.entireSourceMean_coe,
    hdir] with x ha hb hc hd he hf hg hh
  change (R.headReceipt r u • S.normalizedHead r +
    R.headReceipt u r • S.normalizedHead u - R.entireSourceMean) x = _
  rw [ha, Pi.sub_apply, hb, Pi.add_apply, hc, hd, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, he, hf, hg, hh]

/-- Actual physical source energy is the original L² source Gram value. -/
theorem sourceDirectionL2_energy [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    schurForm W m (R.sourceDirectionL2 r u) (R.sourceDirectionL2 r u) =
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) :=
  schurForm_energy_of_ae_coe _ _ (R.sourceDirectionL2_coe r u hru hW hp)

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual full reverse energy dominates the entire source's actual
energy, including when that source is null. -/
theorem source_energy_le_full {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice (S.reverseCompulsorySource R.plateau) R.flow)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ R.flow) := by
  have hsum := R.isFullReverseFlow.sourceSlice_energy_add_le hW hd hgap R.measurableSet_source
  have hc := R.isFullReverseFlow.sourceSlice_energy_nonnegative hW hd hgap R.measurableSet_source.compl
  linarith only [hsum, hc]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
