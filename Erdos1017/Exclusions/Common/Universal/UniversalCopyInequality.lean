module

public import Erdos1017.Exclusions.Common.SelectedAtomCopyVariation
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal

/-!
# Missing-row copy inequality at a universal atom

This module takes a pointwise and integrated inventory of the original rows and
the copied row, shows the physical shifted rows and columns keep the same
stationary constant, and derives the missing-row copy inequality at a universal
atom from the density-corrected copied competitor and flat rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original missing section; for sources outside a universal atom,
this agrees almost everywhere with its outside missing section. -/
def missingSection (A : Ω → Ω → Bool) (x : Ω) : Set Ω := {z | A x z = false}

theorem measurableSet_missingSection (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (x : Ω) : MeasurableSet (missingSection A x) :=
  measurableSet_eq_fun (hA.comp (measurable_const.prodMk measurable_id)) measurable_const

omit [MeasurableSpace Ω] in
/-- Pointwise inventory of the original two rows and the actual copied
row. The common-neighborhood root increment uses the original atom. -/
theorem row_inventory (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I : Set Ω) (m : ℝ) (x y z : Ω)
    (hzero : ∀ v w, A v w = false → Y v w = 0)
    (hI : z ∈ I → A x z = true ∧ A y z = true) :
    rowCharge A Y I x y z - m * rowAdjacency A x y z =
      (Y x z - m * (if A x z = true then 1 else 0)) +
        (Y y z - m * (if A y z = true then 1 else 0)) + m -
        m * (missingSection A x ∩ missingSection A y).indicator (fun _ => 1) z +
        Y x y * I.indicator (fun _ => 1) z -
        (missingSection A x).indicator (Y y) z -
        (missingSection A y).indicator (Y x) z := by
  by_cases hi : z ∈ I
  · obtain ⟨hx, hy⟩ := hI hi
    simp [rowCharge, rowAdjacency, missingSection, hx, hy, hi]
    ring
  · cases hx : A x z <;> cases hy : A y z <;>
      simp [rowCharge, rowAdjacency, missingSection, hx, hy, hi, hzero]
    all_goals ring

/-- Exact integrated copy inventory. All signed row integrals are
integrable; no unsigned treatment of original charges is used. -/
theorem integrated_row_inventory (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I : Set Ω) (hI : MeasurableSet I)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ v w, ‖Y v w‖ ≤ B)
    (hzero : ∀ v w, A v w = false → Y v w = 0)
    (m : ℝ) (x y : Ω)
    (hcommon : ∀ᵐ z ∂μ, z ∈ I → A x z = true ∧ A y z = true) :
    (∫ z, rowCharge A Y I x y z ∂μ) - m * (∫ z, rowAdjacency A x y z ∂μ) =
      (∫ z, Y x z - m * (if A x z = true then 1 else 0) ∂μ) +
        (∫ z, Y y z - m * (if A y z = true then 1 else 0) ∂μ) + m -
        m * μ.real (missingSection A x ∩ missingSection A y) + μ.real I * Y x y -
        (∫ z in missingSection A x, Y y z ∂μ) -
        (∫ z in missingSection A y, Y x z ∂μ) := by
  have hmX := measurableSet_missingSection A hA x
  have hmY := measurableSet_missingSection A hA y
  have hmJ := hmX.inter hmY
  have hYi (v : Ω) : Integrable (Y v) μ := Integrable.of_bound
    ((hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B
    (Eventually.of_forall (hbound v))
  have hAi (v : Ω) : Integrable (fun z => if A v z = true then (1 : ℝ) else 0) μ :=
    Integrable.of_bound (Measurable.ite (measurableSet_eq_fun
      (hA.comp (measurable_const.prodMk measurable_id)) measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by split_ifs <;> norm_num))
  have hX : Integrable (fun z => Y x z - m * (if A x z = true then 1 else 0)) μ :=
    (hYi x).sub ((hAi x).const_mul m)
  have hY' : Integrable (fun z => Y y z - m * (if A y z = true then 1 else 0)) μ :=
    (hYi y).sub ((hAi y).const_mul m)
  have hJ : Integrable ((missingSection A x ∩ missingSection A y).indicator
      (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hmJ
  have hI' : Integrable (I.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hI
  have hCX : Integrable ((missingSection A x).indicator (Y y)) μ := (hYi y).indicator hmX
  have hCY : Integrable ((missingSection A y).indicator (Y x)) μ := (hYi x).indicator hmY
  have hcopyY : Integrable (rowCharge A Y I x y) μ := Integrable.of_bound
    (measurable_rowCharge A hA Y hY I hI x y).aestronglyMeasurable (3 * B)
    (Eventually.of_forall (rowCharge_bound A Y I B hB hbound x y))
  have hcopyA : Integrable (rowAdjacency A x y) μ := Integrable.of_bound
    (measurable_rowAdjacency A hA x y).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by unfold rowAdjacency; split_ifs <;> norm_num))
  let f₁ := fun z => (Y x z - m * (if A x z = true then 1 else 0)) +
    (Y y z - m * (if A y z = true then 1 else 0))
  let f₂ := fun z => f₁ z + m
  let f₃ := fun z => f₂ z - m * (missingSection A x ∩ missingSection A y).indicator (fun _ => 1) z
  let f₄ := fun z => f₃ z + Y x y * I.indicator (fun _ => 1) z
  let f₅ := fun z => f₄ z - (missingSection A x).indicator (Y y) z
  have h₁ : Integrable f₁ μ := hX.add hY'
  have h₂ : Integrable f₂ μ := h₁.add (integrable_const m)
  have h₃ : Integrable f₃ μ := h₂.sub (hJ.const_mul m)
  have h₄ : Integrable f₄ μ := h₃.add (hI'.const_mul (Y x y))
  have h₅ : Integrable f₅ μ := h₄.sub hCX
  have he := integral_congr_ae (hcommon.mono (fun z hz => row_inventory A Y I m x y z hzero hz))
  change (∫ z, rowCharge A Y I x y z - m * rowAdjacency A x y z ∂μ) =
    ∫ z, f₅ z - (missingSection A y).indicator (Y x) z ∂μ at he
  rw [integral_sub hcopyY (hcopyA.const_mul m), integral_const_mul,
    integral_sub h₅ hCY, integral_sub h₄ hCX, integral_add h₃ (hI'.const_mul (Y x y)),
    integral_sub h₂ (hJ.const_mul m), integral_add h₁ (integrable_const m), integral_add hX hY',
    integral_const, integral_const_mul, integral_const_mul,
    integral_indicator hmJ, integral_indicator hI,
    integral_indicator hmX, integral_indicator hmY] at he
  simp only [probReal_univ, setIntegral_const, smul_eq_mul, mul_one] at he
  linarith only [he]

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original physical shifted rows retain the same old stationary
constant on a common almost-everywhere event. -/
theorem ae_physical_shifted_stationary (_S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, (∫ z, PhysicalRepresentative.charge W m x z -
      m * (if PhysicalRepresentative.adjacency W m x z = true then 1 else 0) ∂μ) =
      2 * (c - m * d) := by
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have he : ∀ᵐ p ∂μ.prod μ,
      PhysicalRepresentative.charge W m p.1 p.2 -
        m * (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) =
      shiftedKernel W m p.1 p.2 := by
    filter_upwards [PhysicalRepresentative.charge_ae_eq W m hs,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with p hy ha
    rw [hy, ← ha]
    exact (shiftedMoment_eq W m p).symm
  filter_upwards [Measure.ae_ae_of_ae_prod he, hW.stationary] with x hx hs
  exact (integral_congr_ae hx).trans hs

/-- Pointwise physical symmetry gives the same original constant in
incoming columns, including at source points chosen on the common event. -/
theorem ae_physical_shifted_column_stationary (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, (∫ z, PhysicalRepresentative.charge W m z x -
      m * (if PhysicalRepresentative.adjacency W m z x = true then 1 else 0) ∂μ) =
      2 * (c - m * d) := by
  filter_upwards [S.ae_physical_shifted_stationary hW hd hgap] with x hx
  calc
    _ = ∫ z, PhysicalRepresentative.charge W m x z -
        m * (if PhysicalRepresentative.adjacency W m x z = true then 1 else 0) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [PhysicalRepresentative.charge_symm W m z x,
          PhysicalRepresentative.adjacency_symm W m z x])
    _ = _ := hx

/-- Original missing-row copy inequality at an actual universal atom.
It follows from the genuinely density-corrected copied competitor and old
flat rows; no insertion or trace bound is assumed. -/
theorem ae_universal_copy_inequality (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
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
  have huniversal := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  have hrow : ∀ᵐ x ∂μ, S.ρ x ≠ r.val → ∀ᵐ z ∂μ, z ∈ I → A x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod huniversal] with x hx hxr
    filter_upwards [hx] with z hz hzr
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzr).mpr hxr
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
