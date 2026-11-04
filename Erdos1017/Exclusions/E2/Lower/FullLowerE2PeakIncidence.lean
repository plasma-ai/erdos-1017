module

public import Erdos1017.Exclusions.E2.Lower.FullLowerE2Saturation
public import Erdos1017.Exclusions.E2.Lower.OriginalMissingCrossInventory
public import Erdos1017.Exclusions.E2.Lower.LowerE2PeakScalar
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedCommonMass
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation

/-!
# Universal saturated peak at the lower `E₂` contact

At the selected lower `E₂` contact, the original common forward peak is a
saturated endpoint and is universal (`exists_lowerE2_universal_saturated_peak`):
original square majority forces an atom outside the saturated pair to see both
heads, which would make it both smaller and larger than `2/7`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- Original square majority forces an atom outside the saturated pair
to see both heads throughout the lower-E2 interval. The stronger missing
inventory removes the separate middle-interval scalar comparison. -/
theorem IsSaturatedAtomPair.lowerE2_majority_atom_joined
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (k : S.I) (hkr : k ≠ r) (hku : k ≠ u)
    (hmajority : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 ≤
      (S.originalAtomMass k) ^ 2)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 1) ∧
    (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 1) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem ⟨hq.1, by linarith [hq.2]⟩
  obtain ⟨_, hell, hfloor⟩ := hW.lowerE2_saturated_mass_floor hq hdq hgap hglobal
  rw [hpair.saturated_mass_eq hW hd hgap hell.2] at hfloor
  change LowerE2Scalar.pairFloor q <
    2 * S.originalAtomMass r * S.originalAtomMass u / 2 at hfloor
  have hproduct : LowerE2Scalar.pairFloor q < S.originalAtomMass r * S.originalAtomMass u :=
    by linarith
  have hscalar := LowerE2Scalar.missingMass_lt_thirtyThree_fifths_pairFloor ⟨hq.1.le, hq.2⟩
  have hmissing : 1 - 2 * density W = LowerE2Scalar.missingMass q := by
    rw [hW.density_eq, hdq]
    ring
  have hjoined (v : S.I)
      (hbound : (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = v.val →
          adjacencyKernel W p.1 p.2 = 0) →
        (33 / 5 : ℝ) * S.originalAtomMass r * S.originalAtomMass u ≤ 1 - 2 * density W) :
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = v.val →
        adjacencyKernel W p.1 p.2 = 1 := by
    have hIk := S.hfibers k.val k.property
    have hIv := S.hfibers v.val v.property
    have hcases := KernelOperator.whole_row_cross_block_missing_or_joined
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
      k.val v.val hIk.2.1 hIv.2.1 hIk.2.2.2 hIv.2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm)) hW.moment_mem
    rcases hcases with hzero | hone
    · rw [Measure.prod_restrict] at hzero
      have hraw := (ae_restrict_iff' (hIk.1.prod hIv.1)).mp hzero
      have hz : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = v.val →
          adjacencyKernel W p.1 p.2 = 0 := by
        filter_upwards [hraw] with p hp hk hv
        exact hp ⟨hk, hv⟩
      have hi := hbound hz
      rw [hmissing] at hi
      exact False.elim (by linarith)
    · rw [Measure.prod_restrict] at hone
      have hraw := (ae_restrict_iff' (hIk.1.prod hIv.1)).mp hone
      filter_upwards [hraw] with p hp hk hv
      exact hp ⟨hk, hv⟩
  constructor
  · exact hjoined r (S.thirtyThree_fifths_product_le_missing_density
      k r u hkr hku hpair.1 hmajority)
  · apply hjoined u
    intro hz
    have h := S.thirtyThree_fifths_product_le_missing_density
      k u r hku hkr hpair.1.symm (by simpa only [add_comm] using hmajority) hz
    nlinarith

/-- Both joined saturated heads would make an outside square-majority
atom simultaneously smaller and larger than `2/7`. -/
theorem IsSaturatedAtomPair.not_lowerE2_off_pair_majority
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (k : S.I) (hkr : k ≠ r) (hku : k ≠ u)
    (hmajority : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 <
      (S.originalAtomMass k) ^ 2)
    (hW : FullStationaryClass d c W m) (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨hq.1, by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  obtain ⟨hkrJoin, hkuJoin⟩ :=
    hpair.lowerE2_majority_atom_joined k hkr hku hmajority.le hW hq hdq hgap hglobal
  have hbudget := hpair.joined_atom_mass_bound k hW hd hgap hell.2 hkrJoin hkuJoin
  have hdelta : 0 < 1 + m := by linarith [hell.2]
  have hratio : S.originalAtomMass k < 9 * q / (2 * LowerE2Scalar.denominator q) := by
    apply (mul_lt_mul_iff_of_pos_left hdelta).mp
    calc
      (1 + m) * S.originalAtomMass k ≤ 1 - m - 2 * (2 * (c - m * d)) := hbudget
      _ < 1 + m - 2 * LowerE2Scalar.gapFloor q := by linarith
      _ = (1 + m) * (9 * q / (2 * LowerE2Scalar.denominator q)) := by
        rw [hm]
        simpa only [sub_eq_add_neg] using LowerE2Scalar.deficit_eq_gap_mul_ratio hq.1.le
  have hupper : S.originalAtomMass k < 2 / 7 :=
    hratio.trans (LowerE2Scalar.ratio_lt_two_sevenths ⟨hq.1.le, by linarith [hq.2]⟩)
  obtain ⟨_, _, hfloor⟩ := hW.lowerE2_saturated_mass_floor hq hdq hgap hglobal
  rw [hpair.saturated_mass_eq hW hd hgap hell.2] at hfloor
  change LowerE2Scalar.pairFloor q <
    2 * S.originalAtomMass r * S.originalAtomMass u / 2 at hfloor
  have hP := LowerE2Scalar.pairFloor_gt_two_fortyNine ⟨hq.1.le, hq.2⟩
  have hA := S.originalAtomMass_summable.1 k
  have hprod := mul_pos (sub_pos.mpr hupper)
    (by linarith : 0 < 2 / 7 + S.originalAtomMass k)
  nlinarith [sq_nonneg (S.originalAtomMass r - S.originalAtomMass u)]

/-- At the actual selected lower-E2 contact, the original common forward
peak is a saturated endpoint and is universal. The atom, strict square
majority, saturation capacity and endpoint orientation are all derived. -/
theorem exists_lowerE2_universal_saturated_peak
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 10))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ k u : S.I, S.IsSaturatedAtomPair k u ∧ S.IsCommonForwardPeak d c k ∧
      (∀ j : S.I, j ≠ k → S.originalAtomMass j < S.originalAtomMass k) ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.N) ∧
      (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val →
        adjacencyKernel W p.1 p.2 = if S.ρ p.2 = k.val then 0 else 1) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem ⟨hq.1, by linarith [hq.2]⟩
  have hell := (hW.e2_gamma_floor ⟨hq.1, by linarith [hq.2]⟩ hdq hgap hglobal).2.1.2
  obtain ⟨_, k, _, hside, hpeak, hlargest, _, hmajority⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  obtain ⟨r, u, hru, _⟩ := S.exists_lowerE2_saturated_atoms hW hq hdq hgap hglobal
  obtain ⟨v, hkv⟩ : ∃ v : S.I, S.IsSaturatedAtomPair k v := by
    by_cases hkr : k = r
    · subst r
      exact ⟨u, hru⟩
    by_cases hku : k = u
    · subst u
      exact ⟨r, hru.symm⟩
    let r' : {j : S.I // j ≠ k} := ⟨r, fun h => hkr h.symm⟩
    let u' : {j : S.I // j ≠ k} := ⟨u, fun h => hku h.symm⟩
    have hne : r' ≠ u' := fun h => hru.1 (congrArg Subtype.val h)
    have hsum : Summable (fun j : {j : S.I // j ≠ k} => (S.originalAtomMass j.val) ^ 2) :=
      S.originalAtomMass_sq_summable.comp_injective Subtype.val_injective
    have hfinite := Summable.sum_le_tsum (s := {r', u'})
      (fun j _ => sq_nonneg (S.originalAtomMass j.val)) hsum
    have hpairMajority : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 <
        (S.originalAtomMass k) ^ 2 := by
      have hle : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 ≤
          ∑' j : {j : S.I // j ≠ k}, (S.originalAtomMass j.val) ^ 2 := by
        simpa only [Finset.sum_pair hne] using hfinite
      exact hle.trans_lt hmajority
    exact False.elim (hru.not_lowerE2_off_pair_majority k hkr hku
      hpairMajority hW hq hdq hgap hglobal)
  have hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.N := by
    rcases hside with hH | hN
    · have hz := hkv.high_head_null hW hd hgap hell
      have hraw := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hH
      have heq : μ ({x | S.ρ x = k.val} ∩ S.H) = μ {x | S.ρ x = k.val} := by
        apply measure_congr
        filter_upwards [hraw] with x hx
        exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
      rw [heq] at hz
      exact False.elim ((S.hfibers k.val k.property).2.1.ne' hz)
    · exact hN
  exact ⟨k, v, hkv, hpeak, hlargest, hN, S.neutral_atom_adjacency k hW hd hgap hN⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
