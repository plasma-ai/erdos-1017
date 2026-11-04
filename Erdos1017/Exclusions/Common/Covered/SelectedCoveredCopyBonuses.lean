module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPairCopy

/-!
# Penalty bonuses of the zero-body copy inequality

In the zero-body model the missing-row integrals of the covered copy inequality
are nonpositive, every exterior edge receives the common-missing mass bonus, so
its charge penalty is at least gamma divided by the cover mass and, under the
contact ratio, exceeds half of delta.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Missing sections of exterior points omit the universal root. Thus
both signed missing-row integrals in the actual covered copy inequality
are nonpositive on one original product-law event. -/
theorem ae_missing_row_integrals_nonpositive_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1,
        PhysicalRepresentative.charge W m p.2 z ∂μ) ≤ 0 ∧
      (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2,
        PhysicalRepresentative.charge W m p.1 z ∂μ) ≤ 0 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hbody : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → Y p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hb he hx hy
    exact he.trans_le (hb hx hy)
  have huniversal := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_universal_of_zero_body r hW hd hgap hzero)
  have hrow : ∀ᵐ x ∂μ, S.ρ x ≠ r.val →
      ∀ᵐ z ∂μ, (S.ρ z = r.val → A x z = true) ∧ (S.ρ z ≠ r.val → Y x z ≤ 0) := by
    filter_upwards [Measure.ae_ae_of_ae_prod huniversal, Measure.ae_ae_of_ae_prod hbody]
      with x hu hb hx
    filter_upwards [hu, hb] with z hz hc
    refine ⟨?_, hc hx⟩
    intro hr
    exact (PhysicalRepresentative.adjacency_symm W m x z).trans ((hz hr).mpr hx)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow] with p hx hy hpx hpy
  have hbound (x y : Ω)
      (hx : ∀ᵐ z ∂μ, (S.ρ z = r.val → A x z = true) ∧ (S.ρ z ≠ r.val → Y x z ≤ 0))
      (hy : ∀ᵐ z ∂μ, (S.ρ z = r.val → A y z = true) ∧ (S.ρ z ≠ r.val → Y y z ≤ 0)) :
      (∫ z in IndependentAtomCopy.missingSection A x, Y y z ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_of_ae hy,
      ae_restrict_mem (IndependentAtomCopy.measurableSet_missingSection A
        (PhysicalRepresentative.measurable_adjacency W m) x)] with z hz hw hm
    apply hw.2
    intro hr
    have ht := hz.1 hr
    change A x z = false at hm
    exact Bool.noConfusion (ht.symm.trans hm)
  exact ⟨hbound p.1 p.2 (hx hpx) (hy hpy), hbound p.2 p.1 (hy hpy) (hx hpx)⟩

/-- Every exterior physical edge has the full original common-missing
mass bonus. No regional averaging or supplied copy inequality is needed. -/
theorem ae_body_penalty_common_missing_lower_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      2 * (c - m * d) + m - m * μ.real
        (IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1 ∩
          IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2) ≤
        -μ.real {x | S.ρ x = r.val} * PhysicalRepresentative.charge W m p.1 p.2 := by
  filter_upwards [S.ae_zero_body_copy_inequality r hW hd hgap hzero,
    S.ae_missing_row_integrals_nonpositive_of_zero_body r hW hd hgap hzero]
    with p hc hi hx hy hA
  have h := hc hx hy hA
  obtain ⟨h₁, h₂⟩ := hi hx hy
  linarith

/-- All actual original exterior edges have charge penalty at least
gamma divided by the original cover mass, including diffuse self blocks. -/
theorem ae_body_penalty_mass_lower_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      adjacencyKernel W p.1 p.2 = 1 →
      2 * (c - m * d) + m ≤ -μ.real {x | S.ρ x = r.val} * chargeKernel W p.1 p.2 := by
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [S.ae_body_penalty_common_missing_lower_of_zero_body r hW hd hgap hzero,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
    PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hb ha hy hx hyy hG
  have hA : PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
    change W.moment CappedColor.adjacency p = 1 at hG
    cases h : PhysicalRepresentative.adjacency W m p.1 p.2 <;> simp_all
  have h := hb hx hyy hA
  rw [hy] at h
  have hn := mul_nonpos_of_nonpos_of_nonneg hs.multiplier_neg.le
    (ENNReal.toReal_nonneg (a := μ
      (IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1 ∩
        IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2)))
  dsimp only [Measure.real] at h ⊢
  linarith

/-- The actual contact ratio makes every original exterior penalty exceed
half of delta. The contact ratio is kept explicit, rather than inferred
from a different optimum's multiplier. -/
theorem ae_body_penalty_gt_half_delta_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      adjacencyKernel W p.1 p.2 = 1 → (1 + m) / 2 < -chargeKernel W p.1 p.2 := by
  have hb : 0 < μ.real {x | S.ρ x = r.val} := ENNReal.toReal_pos
    (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)
  filter_upwards [S.ae_body_penalty_mass_lower_of_zero_body r hW hd hgap hzero]
    with p hp hx hy hG
  have he := hp hx hy hG
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure
