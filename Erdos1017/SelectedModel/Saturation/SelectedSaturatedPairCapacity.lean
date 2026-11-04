module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairBlocks
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairUniqueness
public import Erdos1017.SelectedModel.Saturation.PhysicalPrimalSaturatedMass

/-!
# Saturated atom pairs and their capacity bound

Positive saturated charge mass yields a saturated whole-fiber pair, every
charge-one pair lies in the two orientations of that block, the ordered pair
mass is twice the product of the atom masses, and the physical primal gives a
capacity lower bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Positive original saturated charge mass gives an actual saturated
whole-fiber pair, using a simultaneous countable block license. -/
theorem exists_saturated_atom_pair_of_positive_mass
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hpos : 0 < (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1}) :
    ∃ r u : S.I, S.IsSaturatedAtomPair r u := by
  have hne : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} ≠ 0 := by
    intro hz
    have hreal : (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} = 0 := by
      simp only [measureReal_def, hz, ENNReal.toReal_zero]
    linarith
  obtain ⟨p, hp, hblock⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (S.ae_saturated_pair_has_saturated_atom_block hW hd hgap hell))
  obtain ⟨r, u, hru, _, _⟩ := hblock hp
  exact ⟨r, u, hru⟩

/-- Every original charge-one pair lies in the two orientations of the
specified unique saturated atom block, and both orientations are saturated. -/
theorem IsSaturatedAtomPair.ae_charge_one_iff_between_heads
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 = 1 ↔
      (S.ρ p.1 = r.val ∧ S.ρ p.2 = u.val) ∨
        (S.ρ p.1 = u.val ∧ S.ρ p.2 = r.val) := by
  filter_upwards [S.ae_saturated_pair_has_saturated_atom_block hW hd hgap hell,
    hpair.2, hpair.symm.2] with p hp hru hur
  constructor
  · intro hy
    obtain ⟨v, w, hvw, hv, hw⟩ := hp hy
    rcases hpair.unique hvw hW hd hgap hell with ⟨hr, hu⟩ | ⟨hr, hu⟩
    · subst v
      subst w
      exact Or.inl ⟨hv, hw⟩
    · subst w
      subst v
      exact Or.inr ⟨hv, hw⟩
  · rintro (⟨hr, hu⟩ | ⟨hu, hr⟩)
    · exact hru hr hu
    · exact hur hu hr

/-- The ordered original saturated-pair mass is twice the product of the
two positive original atom masses. No topology or parent-law hypothesis
is required for this support identity. -/
theorem IsSaturatedAtomPair.saturated_mass_eq
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} =
      2 * μ.real {x | S.ρ x = r.val} * μ.real {x | S.ρ x = u.val} := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have heq : {p | chargeKernel W p.1 p.2 = 1} =ᵐ[μ.prod μ]
      (Ir ×ˢ Iu) ∪ (Iu ×ˢ Ir) := by
    filter_upwards [hpair.ae_charge_one_iff_between_heads hW hd hgap hell] with p hp
    exact propext hp
  have hdis : Disjoint (Ir ×ˢ Iu) (Iu ×ˢ Ir) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hpair.1 (Subtype.ext (hp.1.symm.trans hq.1))
  rw [measureReal_congr heq, measureReal_union hdis (hIu.prod hIr),
    measureReal_prod_prod, measureReal_prod_prod]
  ring

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual same-model bounded-order physical primal gives the capacity
lower bound on the unique original saturated block. -/
theorem IsSaturatedAtomPair.capacity_lower_bound
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (3 * c - d) / 2 ≤ μ.real {x | S.ρ x = r.val} * μ.real {x | S.ρ x = u.val} := by
  have hmass := hW.saturated_charge_mass_lower_bound hd.2 hgap
  change (3 * c - d) / 2 ≤ (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} / 2 at hmass
  rw [hpair.saturated_mass_eq hW hd hgap hell] at hmass
  linarith

/-- A positive actual order-two reserve constructs the original saturated
pair and its capacity bound; no primal law or pair is supplied. -/
theorem exists_saturated_atom_pair_with_capacity
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hreserve : d < 3 * c) :
    ∃ r u : S.I, S.IsSaturatedAtomPair r u ∧
      (3 * c - d) / 2 ≤ μ.real {x | S.ρ x = r.val} * μ.real {x | S.ρ x = u.val} := by
  have hmass := hW.saturated_charge_mass_lower_bound hd.2 hgap
  change (3 * c - d) / 2 ≤ (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} / 2 at hmass
  have hpos : 0 < (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} := by linarith
  obtain ⟨r, u, hru⟩ := S.exists_saturated_atom_pair_of_positive_mass hW hd hgap hell hpos
  exact ⟨r, u, hru, hru.capacity_lower_bound hW hd hgap hell⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
