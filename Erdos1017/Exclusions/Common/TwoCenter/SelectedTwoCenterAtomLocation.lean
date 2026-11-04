module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns

/-!
# Location of large atoms in a two-center recovery

This module defines the region outside the two recovered heads and the whole
compulsory source, computes its mass from the whole-source balance, and shows
that any original atom larger than this region lies in a head or a
compulsory-source pattern.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The literal original region outside the recovered heads and the
entire compulsory source, before any change of measure. -/
def outsidePlateauSource : Set Ω :=
  (R.plateauRegion ∪ S.reverseCompulsorySource R.plateau)ᶜ

/-- The original outside region is measurable. -/
theorem measurableSet_outsidePlateauSource : MeasurableSet R.outsidePlateauSource :=
  (R.measurableSet_plateauRegion.union R.measurableSet_source).compl

/-- The entire original source balance gives the exact original outside
mass, not the mass of a chosen convenient source subset. -/
theorem outsidePlateauSource_mass (r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u}) :
    μ.real R.outsidePlateauSource = 1 - 2 * R.height := by
  have hdisj : AEDisjoint μ R.plateauRegion (S.reverseCompulsorySource R.plateau) := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [R.ae_plateau_not_high] with x hx hm
    exact hx hm.1 hm.2.1
  have hh : μ.real R.plateauRegion =
      μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val} := by
    rw [R.plateauRegion_eq_pair r u hp]
    apply measureReal_union _ (S.hfibers u.val u.property).1
    apply disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hb : 2 * R.height =
      μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val} +
        μ.real (S.reverseCompulsorySource R.plateau) := by
    have h := R.original_source_balance
    simpa only [hp, Finset.card_pair hru, Nat.cast_ofNat, Finset.sum_pair hru] using h
  rw [outsidePlateauSource,
    measureReal_compl (R.measurableSet_plateauRegion.union R.measurableSet_source),
    probReal_univ, measureReal_union₀ R.measurableSet_source.nullMeasurableSet hdisj, hh]
  linarith

/-- Any original atom lying outside both heads and the entire source is
bounded by the exact original outside mass. -/
theorem original_atom_mass_le_outside (k : S.I)
    (hout : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ R.outsidePlateauSource) :
    μ.real {x | S.ρ x = k.val} ≤ μ.real R.outsidePlateauSource := by
  have hsub := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hout
  exact ENNReal.toReal_mono (measure_ne_top μ R.outsidePlateauSource) (measure_mono_ae hsub)

/-- An original atom larger than the original outside region lies in one
of the two actual heads or three actual compulsory-source patterns. No
common-peak or whole-fiber pattern premise is supplied. -/
theorem original_atom_twoCenter_location (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hp : R.plateau = {r, u})
    (hlarge : 1 - 2 * R.height < μ.real {x | S.ρ x = k.val}) :
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, S.ρ x = r.val) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, S.ρ x = u.val) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate u r) ∨
    (∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterShared r u) := by
  rcases R.whole_fiber_twoCenter_pattern k r u hW hp with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · have hle := R.original_atom_mass_le_outside k h
    rw [R.outsidePlateauSource_mass r u hru hp] at hle
    exact False.elim (not_le_of_gt hlarge hle)

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
