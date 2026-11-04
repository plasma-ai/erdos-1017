module

public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairCapacity
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.Flows.FullForwardQuarterFloor

/-!
# Universal row or mass above one quarter at a lower `E₂` peak

The same original selected forward peak at a lower smooth-E₂ contact either has
a universal physical adjacency row or has original mass strictly above one
quarter (`exists_original_e2_peak_quarter_or_universal`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.LowerE2Scalar

private theorem pairFloor_pos_through_two_fifteen {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (2 / 15)) : 0 < pairFloor q := by
  have hq2 : q ^ 2 ≤ (2 / 15 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hq.1 hq.2 2
  have hq4 : q ^ 4 ≤ (2 / 15 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hq.1 hq.2 4
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
  have hP : 0 < pairNumerator q := by
    unfold pairNumerator
    nlinarith [hq.2]
  exact div_pos hP (mul_pos (by norm_num) (sq_pos_of_pos (denominator_pos hq.1)))

private theorem quarter_gap_pos_through_two_fifteen {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (2 / 15)) :
    (2 - multiplier q) / 16 <
      gapFloor q + multiplier q * (2 * pairFloor q) := by
  have hR : denominator q ≠ 0 := (denominator_pos hq.1).ne'
  have hq2p : 2 + q ≠ 0 := by linarith [hq.1]
  have hid :
      16 * (denominator q) ^ 2 * (q + 2) *
        (gapFloor q + multiplier q * (2 * pairFloor q) -
          (2 - multiplier q) / 16) =
      14 - 87 * q - 116 * q ^ 2 + 433 * q ^ 3 - 24 * q ^ 4 + 23 * q ^ 5 := by
    unfold gapFloor multiplier pairFloor pairNumerator
    field_simp
    unfold denominator
    ring
  have hq2 : q ^ 2 ≤ (2 / 15 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hq.1 hq.2 2
  have hq4 : q ^ 4 ≤ (2 / 15 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hq.1 hq.2 4
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
  have hq5 : 0 ≤ q ^ 5 := pow_nonneg hq.1 5
  have hP : 0 < 14 - 87 * q - 116 * q ^ 2 + 433 * q ^ 3 -
      24 * q ^ 4 + 23 * q ^ 5 := by
    nlinarith [hq.2]
  rw [← hid] at hP
  have hmul : 0 < 16 * (denominator q) ^ 2 * (q + 2) := by
    have hRpos := denominator_pos hq.1
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hRpos)) (by linarith [hq.1])
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hmul).mp hP)

end Erdos1017.LowerE2Scalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
private theorem high_peak_ne_saturated_head
    {S : SelectedHighLowStructure W m} {i r u : S.I}
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) : i ≠ r := by
  intro heq
  subst r
  have hIi : MeasurableSet {x | S.ρ x = i.val} := (S.hfibers i.val i.property).1
  have hnot : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.H := by
    apply (ae_restrict_iff' hIi).mpr
    filter_upwards [compl_mem_ae_iff.mpr (hpair.high_head_null hW hd hgap hell)]
      with x hx hi hH
    exact hx ⟨hi, hH⟩
  obtain ⟨x, _, hxH, hxnot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne' (hhigh.and hnot)
  exact hxnot hxH

/-- The same original selected forward peak at a lower smooth-E2 contact
either has its actual universal physical adjacency row or has original
mass strictly above one quarter. All reserve, capacity and contact inputs
are derived from the model. -/
theorem exists_original_e2_peak_quarter_or_universal
    (S : SelectedHighLowStructure W m)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (0 : ℝ) (2 / 15))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.N)) ∧
      (∀ (v : Ω × Ω → ℝ), S.IsFullForwardFlow v →
        0 < S.forwardClassMass v i ∧
        ForwardPeak.massPeak (S.forwardClassMass v) = S.forwardClassMass v i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass v) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) *
        (∑' k, (S.originalAtomMass k) ^ 2) ≤
          2 * (S.originalAtomMass i) ^ 2) ∧
      ((∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) <
        (S.originalAtomMass i) ^ 2) ∧
      ((∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
        (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
          S.ρ p.2 ≠ i.val)) ∨ 1 / 4 < S.originalAtomMass i) := by
  have hq' : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨hq.1, by linarith [hq.2]⟩
  have hqClosed : q ∈ Icc (0 : ℝ) (2 / 15) := ⟨hq.1.le, hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ := hW.e2_gamma_floor hq' hdq hgap hglobal
  obtain ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  refine ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, hmajority, ?_⟩
  rcases hside with hhigh | hneutral
  · right
    have hB : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3) := by
      rw [hdq]
      exact Benchmark.benchmark_e2_q hq'
    have hpairEq : 2 * LowerE2Scalar.pairFloor q = 3 * benchmark d - d := by
      have h := LowerE2Scalar.pairFloor_eq_twoHeadValue hq.1.le
      rw [← hB, ← hdq] at h
      exact h
    have hpairPos := LowerE2Scalar.pairFloor_pos_through_two_fifteen hqClosed
    have h3c : d < 3 * c := by linarith [hpairEq, hgap]
    obtain ⟨r, u, hpair, hcap⟩ :=
      S.exists_saturated_atom_pair_with_capacity hW hd hgap hell.2 h3c
    have hir : i ≠ r := high_peak_ne_saturated_head hhigh hpair hW hd hgap hell.2
    have hiu : i ≠ u := high_peak_ne_saturated_head hhigh hpair.symm hW hd hgap hell.2
    let _ : Countable S.I := S.hI.to_subtype
    have hfinite := Summable.sum_le_tsum (s := {i, r, u})
      (fun k _ => sq_nonneg (S.originalAtomMass k)) S.originalAtomMass_sq_summable
    have hnot : i ∉ ({r, u} : Finset S.I) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hir hiu
    have hQ : (S.originalAtomMass i) ^ 2 + (S.originalAtomMass r) ^ 2 +
        (S.originalAtomMass u) ^ 2 ≤
        ∑' k, (S.originalAtomMass k) ^ 2 := by
      simpa only [Finset.sum_insert hnot, Finset.sum_pair hpair.1,
        add_assoc] using hfinite
    have hpairSq : 2 * S.originalAtomMass r * S.originalAtomMass u ≤
        (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 := by
      nlinarith [sq_nonneg (S.originalAtomMass r - S.originalAtomMass u)]
    change (3 * c - d) / 2 ≤ S.originalAtomMass r * S.originalAtomMass u at hcap
    have hcap2 : 3 * c - d ≤ 2 * S.originalAtomMass r * S.originalAtomMass u := by
      linarith [hcap]
    have hellpos : 0 < -m := hell.1
    have hQmul := mul_le_mul_of_nonneg_left hQ hellpos.le
    have hSqmul := mul_le_mul_of_nonneg_left hpairSq hellpos.le
    have hCapmul := mul_le_mul_of_nonneg_left hcap2 hellpos.le
    have hpairBound : 2 * LowerE2Scalar.pairFloor q < 3 * c - d := by
      linarith [hpairEq, hgap]
    have hPairmul := mul_lt_mul_of_pos_left hpairBound hellpos
    have hmneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
    have hscalar := LowerE2Scalar.quarter_gap_pos_through_two_fifteen hqClosed
    rw [← hmneg] at hscalar
    have hstrict : (2 + m) / 16 <
        2 * (c - m * d) + m + (-m) * (3 * c - d) := by
      nlinarith [hgamma, hscalar, hPairmul]
    have hmain : 2 * (c - m * d) + m + (-m) * (3 * c - d) ≤
        (2 + m) * (S.originalAtomMass i) ^ 2 := by
      nlinarith [hreserve, hQmul, hSqmul, hCapmul]
    by_contra hnotQuarter
    have hAquarter : S.originalAtomMass i ≤ 1 / 4 := le_of_not_gt hnotQuarter
    have hA2 : (S.originalAtomMass i) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      nlinarith [hA.le]
    have hcoef : 0 < 2 + m := by linarith [hell.2]
    have hA2mul := mul_le_mul_of_nonneg_left hA2 hcoef.le
    nlinarith
  · left
    exact S.neutral_atom_physical_adjacency i hW hd hgap hneutral

end Erdos1017.CappedModel.SelectedHighLowStructure
