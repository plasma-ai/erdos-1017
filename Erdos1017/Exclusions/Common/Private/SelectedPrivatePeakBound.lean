module

public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePeakGeometry
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadPrice
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation

/-!
# Private atoms have mass below one third

Every atom in a private two-center source has mass strictly below one third
under the intercept guard, derived from the private geometry, the star variation
and the receipt balance, with nonsaturation supplying the head-charge slack.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The concrete private geometry and actual star variation bound the
original atom by the remaining original private and outside masses. The
strict original head-charge hypothesis is displayed explicitly. -/
theorem private_atom_mass_bound_of_unsaturated_head (k r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u)
    (hslack : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x < 1) :
    μ.real {x | S.ρ x = k.val} ≤ μ.real (S.twoCenterPrivate r u) -
      μ.real {x | S.ρ x = k.val} + (1 - 2 * R.height) := by
  have hblock := (R.private_atom_head_blocks k r u hru hW hd hgap hp hprivate).2
  have hjoined : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, x ∈ S.rootNeighborhood k := by
    have h := S.ae_rootNeighborhood_on_constant_block k u hW hd hgap true hblock
    filter_upwards [ae_restrict_of_ae h,
      ae_restrict_mem (S.hfibers u.val u.property).1] with x hx hm
    exact (hx hm).mpr rfl
  exact (S.root_mass_le_cover_of_unsaturated_head k hW hd hgap
    {x | S.ρ x = u.val} (R.privatePeakCover k r u)
    (S.hfibers u.val u.property).1 (S.hfibers u.val u.property).2.1
    (R.measurableSet_privatePeakCover k r u hp) hjoined hslack
    (R.privatePeakCover_common_neighbors k r u hru hW hd hgap hp hprivate)).trans
      (R.privatePeakCover_mass_le k r u hru hp hprivate)

/-- The original receipt balance makes the private mass strictly below
one third, including null shared sources and zero original outside mass.
This conditional leaf does not assert the HIGH-star unsaturation result. -/
theorem private_atom_mass_lt_third_of_unsaturated_head (k r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) (ht : 1 / 3 < R.height)
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u)
    (hslack : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x < 1) :
    μ.real {x | S.ρ x = k.val} < 1 / 3 := by
  have hb := R.twoCenter_receipt_balances r u hru hp
  apply CliqueStarVariation.private_mass_lt_third
    (R.private_atom_mass_bound_of_unsaturated_head k r u hru hW hd hgap hp hprivate hslack)
    hb.2.2.2.1
  · exact ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)
  · exact hb.1
  · exact ht

/-- Cardinality two and the actual intercept guard supply the required
head-mass range internally. Only the strict original head-charge adapter
remains an explicit hypothesis of this conditional private-sector leaf. -/
theorem private_atom_mass_lt_third_of_intercept_and_unsaturated_head
    (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u)
    (hslack : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x < 1) :
    μ.real {x | S.ρ x = k.val} < 1 / 3 := by
  have hc : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  exact R.private_atom_mass_lt_third_of_unsaturated_head k r u hru hW hd hgap hp
    (R.two_center_parameters hW hd hgap hc hintercept).2.2.1 hprivate hslack

/-- The homogeneous block adapter turns actual nonsaturation into the
strict charge slack needed by the actual private-star comparison. -/
theorem private_atom_mass_lt_third_of_intercept_and_not_saturated
    (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u)
    (hnot : ¬S.IsSaturatedAtomPair k u) :
    μ.real {x | S.ρ x = k.val} < 1 / 3 := by
  exact R.private_atom_mass_lt_third_of_intercept_and_unsaturated_head
    k r u hru hW hd hgap hp hintercept hprivate
    (S.ae_rootChargeRow_lt_one_of_not_saturated k u
      (R.private_atom_ne_heads k r u hp hprivate).2 hW hd hgap hnot)

/-- Every actual original atom in a private two-center source has mass
below one third under the genuine intercept guard. HIGH-star slack is
derived from the original saturated-head orientation theorem. -/
theorem private_atom_mass_lt_third (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) :
    μ.real {x | S.ρ x = k.val} < 1 / 3 := by
  have hc : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  have hell := (R.two_center_parameters hW hd hgap hc hintercept).2.1
  have hnot : ¬S.IsSaturatedAtomPair k u := by
    intro hpair
    have hz := hpair.high_head_null hW hd hgap hell
    have hhigh := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hprivate
    have heq : μ ({x | S.ρ x = k.val} ∩ S.H) = μ {x | S.ρ x = k.val} := by
      apply measure_congr
      filter_upwards [hhigh] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, (hx h).1.1.1⟩⟩
    rw [heq] at hz
    exact (S.hfibers k.val k.property).2.1.ne' hz
  exact R.private_atom_mass_lt_third_of_intercept_and_not_saturated
    k r u hru hW hd hgap hp hintercept hprivate hnot

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
