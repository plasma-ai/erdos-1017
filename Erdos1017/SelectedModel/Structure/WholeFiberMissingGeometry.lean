module

public import Erdos1017.SelectedModel.Structure.WholeRowAtoms

/-!
# Missing region outside a whole row fiber

This module defines the measurable nonneighbor region `wholeFiberMissingSet`
outside a whole row fiber; a positive fiber and its positive missing set lie on
opposite sides of the zero-pair cut, and differing degrees inside the missing
region force a positive original kernel value.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual nonneighbor region outside the displayed whole row fiber. -/
def wholeFiberMissingSet (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ) : Set Ω :=
  {x | R x ≠ r ∧ r x ≤ 0}

theorem measurableSet_wholeFiberMissingSet
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r : Lp ℝ 2 μ) :
    MeasurableSet (wholeFiberMissingSet R r) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  exact (hR.measurable (measurableSet_singleton r)).compl.inter
    (measurableSet_le (Lp.stronglyMeasurable r).measurable measurable_const)

variable [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Original nonnegative kernel rows vanish on the actual nonpositive-row
missing region. Tonelli licenses the original restricted product statement. -/
theorem ae_zero_fiber_prod_missingSet
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r : Lp ℝ 2 μ)
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2) :
    ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict (wholeFiberMissingSet R r)),
      K p.1 p.2 = 0 := by
  let s := {x | R x = r}
  let N := wholeFiberMissingSet R r
  have hN : MeasurableSet N := measurableSet_wholeFiberMissingSet R hR r
  have hle : (μ.restrict s).prod (μ.restrict N) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hnonneg : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict N), 0 ≤ K p.1 p.2 :=
    ae_mono hle hK0
  have hzero : ∀ᵐ x ∂μ.restrict s, ∀ᵐ y ∂μ.restrict N, K x y = 0 := by
    filter_upwards [hrows, Measure.ae_ae_of_ae_prod hnonneg] with x hx hk
    filter_upwards [ae_restrict_of_ae hx, hk, ae_restrict_mem hN] with y hy hky hNy
    exact le_antisymm (hy.trans_le hNy.2) hky
  have hm : AEMeasurable (fun p : Ω × Ω => ENNReal.ofReal (K p.1 p.2))
      ((μ.restrict s).prod (μ.restrict N)) :=
    (hK.mono_measure hle).aemeasurable.ennreal_ofReal
  have hi : (∫⁻ p : Ω × Ω, ENNReal.ofReal (K p.1 p.2)
      ∂(μ.restrict s).prod (μ.restrict N)) = 0 := by
    rw [lintegral_prod _ hm]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero] with x hx
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hx] with y hy
    simp only [hy, ENNReal.ofReal_zero, Pi.zero_apply]
  filter_upwards [(lintegral_eq_zero_iff' hm).mp hi, hnonneg] with p hp hk
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hp) hk

/-- A positive whole fiber and its positive actual missing set lie on
opposite sides of the given zero-pair cut. Both side conclusions are derived
from common-good cross sections, without a preassigned fiber side. -/
theorem opposite_cut_sides_of_positive_missingSet
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hNpos : 0 < μ (wholeFiberMissingSet R r))
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (B : Set Ω)
    (hcross : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B)) :
    ((∀ᵐ x ∂μ.restrict {x | R x = r}, x ∈ B) ∧
      (∀ᵐ y ∂μ.restrict (wholeFiberMissingSet R r), y ∉ B)) ∨
    ((∀ᵐ x ∂μ.restrict {x | R x = r}, x ∉ B) ∧
      (∀ᵐ y ∂μ.restrict (wholeFiberMissingSet R r), y ∈ B)) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let s := {x | R x = r}
  let N := wholeFiberMissingSet R r
  have hs : MeasurableSet s := hR.measurable (measurableSet_singleton r)
  have hN : MeasurableSet N := measurableSet_wholeFiberMissingSet R hR r
  have hle : (μ.restrict s).prod (μ.restrict N) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hrect : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict N),
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B) := by
    filter_upwards [ae_zero_fiber_prod_missingSet K R hR r hrows hK hK0,
      ae_mono hle hcross, Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hN)] with p hp hc hx hy
    exact hc hp (fun he => hy.1 (he.symm.trans hx))
  have hsections := Measure.ae_ae_of_ae_prod hrect
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hrpos.ne' hsections
  by_cases hxB : x ∈ B
  · have hNside : ∀ᵐ y ∂μ.restrict N, y ∉ B := by
      filter_upwards [hx] with y hy
      exact hy.elim (fun h => h.2) (fun h => False.elim (h.2 hxB))
    refine Or.inl ⟨?_, hNside⟩
    filter_upwards [hsections] with z hz
    obtain ⟨y, _, hy, hyB⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hNpos.ne'
      (hz.and hNside)
    exact hy.elim (fun h => h.1) (fun h => False.elim (hyB h.1))
  · have hNside : ∀ᵐ y ∂μ.restrict N, y ∈ B := by
      filter_upwards [hx] with y hy
      exact hy.elim (fun h => False.elim (hxB h.1)) (fun h => h.1)
    refine Or.inr ⟨?_, hNside⟩
    filter_upwards [hsections] with z hz
    obtain ⟨y, _, hy, hyB⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hNpos.ne'
      (hz.and hNside)
    exact hy.elim (fun h => False.elim (h.2 hyB)) (fun h => h.2)

/-- Two missing-region points on the same derived cut side can form a zero
pair only if their actual supplied whole-row values agree. -/
theorem ae_zero_same_row_on_missingSet
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hNpos : 0 < μ (wholeFiberMissingSet R r))
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (B : Set Ω)
    (hcross : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B)) :
    ∀ᵐ p ∂(μ.restrict (wholeFiberMissingSet R r)).prod
      (μ.restrict (wholeFiberMissingSet R r)), K p.1 p.2 = 0 → R p.1 = R p.2 := by
  let N := wholeFiberMissingSet R r
  have hle : (μ.restrict N).prod (μ.restrict N) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hc := ae_mono hle hcross
  rcases opposite_cut_sides_of_positive_missingSet K R hR r hrpos hNpos hrows hK hK0 B hcross
    with ⟨_, hside⟩ | ⟨_, hside⟩
  · filter_upwards [hc, Measure.quasiMeasurePreserving_fst.ae hside,
      Measure.quasiMeasurePreserving_snd.ae hside] with p hp hx hy hzero
    by_contra hne
    exact (hp hzero hne).elim (fun h => hx h.1) (fun h => hy h.1)
  · filter_upwards [hc, Measure.quasiMeasurePreserving_fst.ae hside,
      Measure.quasiMeasurePreserving_snd.ae hside] with p hp hx hy hzero
    by_contra hne
    exact (hp hzero hne).elim (fun h => h.2 hy) (fun h => h.2 hx)

/-- If the actual original degree factors through whole rows, differing
degrees inside the missing region force a positive original kernel value.
This is the unequal-degree input used by the neighborhood-order argument. -/
theorem ae_positive_of_degree_ne_on_missingSet
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R) (r : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hNpos : 0 < μ (wholeFiberMissingSet R r))
    (hrows : ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ))
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (B : Set Ω)
    (hcross : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → R p.1 ≠ R p.2 →
      (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B))
    (g : Ω → ℝ)
    (hdegree : ∀ᵐ p ∂μ.prod μ, R p.1 = R p.2 → g p.1 = g p.2) :
    ∀ᵐ p ∂(μ.restrict (wholeFiberMissingSet R r)).prod
      (μ.restrict (wholeFiberMissingSet R r)), g p.1 ≠ g p.2 → 0 < K p.1 p.2 := by
  have hle : (μ.restrict (wholeFiberMissingSet R r)).prod
      (μ.restrict (wholeFiberMissingSet R r)) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_zero_same_row_on_missingSet K R hR r hrpos hNpos hrows hK hK0 B hcross,
    ae_mono hle hdegree, ae_mono hle hK0] with p hz hg hk hne
  have hnz : K p.1 p.2 ≠ 0 := fun he => hne (hg (hz he))
  exact lt_of_le_of_ne hk hnz.symm

end Erdos1017.KernelOperator
