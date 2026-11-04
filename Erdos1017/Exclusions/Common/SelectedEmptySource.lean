module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.Flows.OriginalForwardPeakLargest

/-!
# Recovered head with an empty singleton source

When the entire singleton source of the recovered head is null, the head keeps
its original mass, the objective is bounded by its square, and the head is the
original peak, neutral, and universal outside its own independent fiber, giving
a universal common forward peak.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A null entire original singleton source contributes no mass to the
actual recovered head height. -/
theorem empty_source_height_eq_original_mass (r : S.I) (hr : R.plateau = {r})
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    R.height = μ.real {x | S.ρ x = r.val} := by
  have h := R.singleton_height_eq_mass_add_source r hr
  rw [hr] at hnull
  simpa only [measureReal_def, hnull, ENNReal.toReal_zero, add_zero] using h

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual singleton credit and null entire source give the original
objective bound, even if the remaining reverse flow is nonzero. -/
theorem empty_source_objective_le_sq (r : S.I) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    c ≤ (μ.real {x | S.ρ x = r.val}) ^ 2 := by
  have h := R.singleton_source_credit hW hd hgap r hr
  rw [hr] at hnull
  have hp : (μ.prod μ) (S.reverseCompulsorySource {r} ×ˢ S.reverseCompulsorySource {r}) = 0 := by
    rw [Measure.prod_prod, hnull, zero_mul]
  have hz : (μ.prod μ).restrict
      (S.reverseCompulsorySource {r} ×ˢ S.reverseCompulsorySource {r}) = 0 :=
    Measure.restrict_eq_zero.mpr hp
  simpa only [hz, integral_zero_measure, zero_div, mul_zero, add_zero,
    measureReal_def, hnull, ENNReal.toReal_zero] using h

/-- The benchmark gap supplies the scalar strict missing-density bound
used to identify the recovered head, without a separate reserve premise. -/
theorem empty_source_missing_lt_twice_objective
    {d c : ℝ} (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    1 - 2 * d < 2 * c := by
  have h := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
  linarith

/-- Two distinct original independent squares exclude every largest
original atom other than the actual null-source recovered head. -/
theorem empty_source_is_original_peak (r : S.I) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    S.IsCommonForwardPeak d c r ∧
      ∀ k : S.I, k ≠ r → S.originalAtomMass k < S.originalAtomMass r := by
  have hb := R.empty_source_objective_le_sq r hr hW hd hgap hnull
  have hstrict := empty_source_missing_lt_twice_objective hd hgap
  obtain ⟨_, i, _, _, hpeak, _, hlt, _, _⟩ :=
    S.exists_unique_largest_original_forward_peak hW hd hgap
  have hir : i = r := by
    by_contra hne
    have hs := S.two_originalAtomMass_sq_le_missing_density i r hne
    rw [hW.density_eq] at hs
    have hl := hlt r (Ne.symm hne)
    have hri := S.originalAtomMass_summable.1 r
    change c ≤ (S.originalAtomMass r) ^ 2 at hb
    nlinarith
  subst i
  exact ⟨hpeak, hlt⟩

/-- The same recovered original head is neutral once its actual common
forward-peak identity has been derived. -/
theorem empty_source_head_neutral (r : S.I) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N := by
  apply R.common_peak_head_neutral r
    (show r ∈ R.plateau by rw [hr]; simp)
  exact (R.empty_source_is_original_peak r hr hW hd hgap hnull).1

/-- Empty entire source forces the original head to be universal outside
its own original independent fiber, with one product-null exception. -/
theorem empty_source_head_adjacency (r : S.I) (hr : R.plateau = {r})
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → adjacencyKernel W p.1 p.2 =
      if S.ρ p.2 = r.val then 0 else 1 :=
  S.neutral_atom_adjacency r hW hd hgap
    (R.empty_source_head_neutral r hr hW hd hgap hnull)

/-- Cardinality one and a null entire original source identify an actual
universal common forward peak and its original square objective bound. -/
theorem exists_empty_source_universal_peak
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hcard : R.plateau.card = 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    ∃ r : S.I, R.plateau = {r} ∧ S.IsCommonForwardPeak d c r ∧
      (∀ k : S.I, k ≠ r → S.originalAtomMass k < S.originalAtomMass r) ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) ∧
      R.height = S.originalAtomMass r ∧ c ≤ (S.originalAtomMass r) ^ 2 ∧
      ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val then 0 else 1 := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
  have hp := R.empty_source_is_original_peak r hr hW hd hgap hnull
  exact ⟨r, hr, hp.1, hp.2, R.empty_source_head_neutral r hr hW hd hgap hnull,
    R.empty_source_height_eq_original_mass r hr hnull,
    R.empty_source_objective_le_sq r hr hW hd hgap hnull,
    R.empty_source_head_adjacency r hr hW hd hgap hnull⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
