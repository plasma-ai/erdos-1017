module

public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePeakBound
public import Erdos1017.Exclusions.Common.ConditionalMissingMassCap
public import Erdos1017.Exclusions.Common.Flows.FullForwardQuarterFloor

/-!
# Private radius bounds at the lower `E₂` contact

The lower-`E₂` contact has the strict original intercept guard needed by the
private two-center mass estimate (`e2_intercept_guard`), and the original
private atom fixes the radius and bounds both original heads and every atom
incident to the entire second private source (`private_e2_radius_bounds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.LowerE2Scalar

private theorem gapFloor_gt_delta_quarter {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    (1 - multiplier q) / 4 < gapFloor q := by
  have hR : denominator q ≠ 0 := (denominator_pos hq.1.le).ne'
  have hq2 : q + 2 ≠ 0 := by linarith [hq.1]
  have hq2' : 2 + q ≠ 0 := by linarith [hq.1]
  have hidentity : gapFloor q - (1 - multiplier q) / 4 =
      q * (q - 1) ^ 2 / (2 * denominator q * (q + 2)) := by
    unfold gapFloor multiplier
    field_simp [hq2']
    unfold denominator
    ring
  rw [← sub_pos, hidentity]
  apply div_pos
  · have hq1 : 0 < 1 - q := by linarith [hq.2]
    have hs : 0 < (q - 1) ^ 2 := by nlinarith [sq_pos_of_pos hq1]
    exact mul_pos hq.1 hs
  · exact mul_pos (mul_pos (by norm_num) (denominator_pos hq.1.le))
      (by linarith [hq.1])

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

/-- The genuine lower-E2 contact has the strict original intercept guard
needed by the private two-center mass estimate. -/
theorem FullStationaryClass.e2_intercept_guard (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    (1 + m) / 4 < 2 * (c - m * d) + m := by
  obtain ⟨hm, _, hγ⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  have hscalar := LowerE2Scalar.gapFloor_gt_delta_quarter hq
  rw [hm]
  rw [hm] at hγ
  nlinarith

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The original private atom fixes the actual radius and bounds both
original heads and every atom incident to the entire second private source.
The largest-atom and private-pattern hypotheses concern this same recovery. -/
theorem private_e2_radius_bounds (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let B := missingMassCapRadius d c m (S.originalAtomMass i)
    0 ≤ B ∧
      (-m) * B ^ 2 = (2 + m) * (S.originalAtomMass i) ^ 2 -
        (2 * (c - m * d) + m) ∧
      B < S.originalAtomMass i ∧
      S.originalAtomMass r ≤ B ∧ S.originalAtomMass u ≤ B ∧
      ∀ k : S.I, 0 < μ (S.twoCenterPrivate u r ∩ {x | S.ρ x = k.val}) →
        S.originalAtomMass k + S.originalAtomMass u ≤ B := by
  let B := missingMassCapRadius d c m (S.originalAtomMass i)
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  obtain ⟨_, hell, _⟩ := hW.e2_gamma_floor hq hdq hgap hglobal
  have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
  have hthird := R.private_atom_mass_lt_third i r u hru hW hd hgap hp
    hintercept hprivate
  have hApos : 0 < S.originalAtomMass i :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  have hA2 : (S.originalAtomMass i) ^ 2 < (1 / 3 : ℝ) ^ 2 := by
    change S.originalAtomMass i < 1 / 3 at hthird
    nlinarith [hApos]
  have hδ : 0 < 1 + m := by linarith [hell.2]
  have hguard : 2 * (1 + m) * (S.originalAtomMass i) ^ 2 <
      2 * (c - m * d) + m := by
    have hsmall : 2 * (S.originalAtomMass i) ^ 2 < (1 / 4 : ℝ) := by
      nlinarith [hA2]
    have hmul := mul_lt_mul_of_pos_left hsmall hδ
    nlinarith [hmul, hintercept]
  obtain ⟨j, _, _, hjpeak, hjlargest, _, _, hhighcap, hneutralcap, htail⟩ :=
    S.exists_conditional_missing_mass_cap hW hd hgap
  have hji : j = i := by
    by_contra hne
    have hlt := hjlargest i (fun h => hne h.symm)
    have hle := hmax j
    linarith
  subst j
  obtain ⟨hBlt, _, hLowcap⟩ := htail hguard
  have hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H :=
    hprivate.mono (fun _ hx => hx.1.1.1)
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L :=
    hhigh.mono (fun _ hx hy => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hy)
  obtain ⟨v, hv, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  obtain ⟨_, hBnonneg, hidentity⟩ := hv.missingMassCapRadius_properties
    hW hd hgap i hnonlow (hjpeak v hv).2.1 havoid
  have hneq := R.private_atom_ne_heads i r u hp hprivate
  have hhead (k : S.I) (hk : k ∈ R.plateau) (hki : k ≠ i) :
      S.originalAtomMass k ≤ B := by
    rcases S.eligibleReverseAtom_low_or_neutral k (R.plateau_eligible k hk) with hL | hN
    · exact hLowcap k hL
    · exact hneutralcap k hki hN
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hu : u ∈ R.plateau := by rw [hp]; simp
  have hrbound := hhead r hr hneq.1.symm
  have hubound := hhead u hu hneq.2.symm
  refine ⟨hBnonneg, ?_, hBlt, hrbound, hubound, ?_⟩
  · nlinarith [hidentity]
  intro k hkpos
  have hkhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.H :=
    S.high_fiber_of_positive_high_subset k
      (S.twoCenterPrivate u r ∩ {x | S.ρ x = k.val}) hkpos
      (fun _ hx => hx.1.1.1.1) (fun _ hx => hx.2)
  have hki : k ≠ i := by
    intro heq
    subst k
    have hglobalPrivate := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hprivate
    obtain ⟨x, hx, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hkpos.ne' (ae_restrict_of_ae hglobalPrivate)
    exact Set.disjoint_left.mp (S.twoCenter_patterns_disjoint r u).1
      (hgood hx.2) hx.1
  have hcap := hhighcap k hki hkhigh
  have hmissing := S.ae_atomMass_le_outsideSectionMass_on_missing hW u
  have hrow := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp
    (S.ae_outsideSectionMass_eq_missingRegion_on_fiber hW k.val k.property)
  obtain ⟨x, hx, hxmissing, hxrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hkpos.ne' ((ae_restrict_of_ae hmissing).and (ae_restrict_of_ae hrow))
  have huN : x ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val := hx.1.1.2
  have haubound := hxmissing huN
  rw [hxrow hx.2] at haubound
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
