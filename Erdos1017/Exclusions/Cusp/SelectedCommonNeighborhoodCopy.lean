module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality

/-!
# Copied-competitor inequality on a common neighborhood

The two signed source charges cost at most one at every source point, vanishing
when both incidences are missing, and the copied competitor gives the signed
missing-row inequality on the entire neighborhood of any original atom without
universality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*}

/-- The two signed source charges cost at most one at every source point.
When both incidences are missing, both charges vanish. -/
theorem missing_row_tax_le_one (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hzero : ∀ v w, A v w = false → Y v w = 0)
    (hcap : ∀ v w, Y v w ≤ 1) (x y z : Ω) :
    (missingSection A x).indicator (Y y) z +
      (missingSection A y).indicator (Y x) z ≤ 1 := by
  cases hx : A x z <;> cases hy : A y z
  · simp [missingSection, hx, hy, hzero x z hx, hzero y z hy]
  · simpa [missingSection, hx, hy] using hcap y z
  · simpa [missingSection, hx, hy] using hcap x z
  · simp [missingSection, hx, hy]

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual copied competitor gives the signed original missing-row
inequality on the entire neighborhood of any original atom. Universality
is unnecessary: both copied vertices see the same whole atom here. -/
theorem ae_common_neighborhood_copy_inequality
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood r → p.2 ∈ S.rootNeighborhood r →
      0 < PhysicalRepresentative.charge W m p.1 p.2 →
      μ.real {x | S.ρ x = r.val} * PhysicalRepresentative.charge W m p.1 p.2 +
        (2 * (c - m * d) + m) - m * μ.real
          (IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1 ∩
            IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2) ≤
        (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.1,
          PhysicalRepresentative.charge W m p.2 z ∂μ) +
        (∫ z in IndependentAtomCopy.missingSection (PhysicalRepresentative.adjacency W m) p.2,
          PhysicalRepresentative.charge W m p.1 z ∂μ) := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency r hW hd hgap)
  have hrow : ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r →
      ∀ᵐ z ∂μ, z ∈ I → A x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with x hx hxn
    filter_upwards [hx] with z hz hzi
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzi).mpr hxn
  have hflat := S.ae_physical_shifted_stationary hW hd hgap
  filter_upwards [S.ae_atom_copy_shifted_row_le_stationary r hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hrow, Measure.quasiMeasurePreserving_snd.ae hrow,
    Measure.quasiMeasurePreserving_fst.ae hflat, Measure.quasiMeasurePreserving_snd.ae hflat]
    with p hp hx hy hfx hfy hpx hpy hq
  have hA : A p.1 p.2 = true := by
    by_contra hn
    have hz := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2
      (Bool.eq_false_iff.mpr hn)
    linarith
  have hcommon : ∀ᵐ z ∂μ, z ∈ I → A p.1 z = true ∧ A p.2 z = true := by
    filter_upwards [hx hpx, hy hpy] with z hx hy hi
    exact ⟨hx hi, hy hi⟩
  have he := IndependentAtomCopy.integrated_row_inventory A
    (PhysicalRepresentative.measurable_adjacency W m) Y
    (PhysicalRepresentative.measurable_charge W m) I (S.hfibers r.val r.property).1
    3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
    (PhysicalRepresentative.charge_zero_of_nonedge W m) m p.1 p.2 hcommon
  have hb := hp hA hq.le
  change (∫ z, IndependentAtomCopy.rowCharge A Y I p.1 p.2 z ∂μ) -
    m * (∫ z, IndependentAtomCopy.rowAdjacency A p.1 p.2 z ∂μ) ≤ _ at hb
  rw [hfx, hfy] at he
  dsimp only [I, A, Y] at he hb
  linarith only [he, hb]

end Erdos1017.CappedModel.SelectedHighLowStructure
