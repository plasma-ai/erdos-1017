module

public import Erdos1017.SelectedModel.Structure.AffineIsotropicLine
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Common affine plane from middle interpolation

Positive left and right neighborhoods with almost-everywhere middle
interpolation lie on one affine plane, with anchors chosen from common
Fubini-good sections.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.OrderedZeroTripleGeometry

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Positive left and right neighborhoods with almost-everywhere middle
interpolation lie on one affine plane. Both anchors are selected from
common Fubini-good sections, rather than arbitrary physical points. -/
theorem exists_common_affinePlane_of_ae_interpolation
    (φ : Ω → ℝ) (V : Ω → H) (y : Ω)
    (L R : Set Ω) (hL : MeasurableSet L) (hR : MeasurableSet R)
    (hLpos : μ L ≠ 0) (hRpos : μ R ≠ 0)
    (hleft : ∀ᵐ x ∂μ.restrict L, φ x < φ y)
    (hright : ∀ᵐ z ∂μ.restrict R, φ y < φ z)
    (hinterpolation : ∀ᵐ p ∂(μ.restrict L).prod (μ.restrict R),
      V y = affineLine (φ p.1) (φ p.2) (V p.1) (V p.2) (φ y)) :
    ∃ x ∈ L, ∃ z ∈ R, φ x < φ y ∧ φ y < φ z ∧
      y ∈ affinePlane φ V x z ∧
      ∀ᵐ w ∂μ, w ∈ L ∪ R → w ∈ affinePlane φ V x z := by
  have hLR := Measure.ae_ae_of_ae_prod hinterpolation
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict R) (ν := μ.restrict L)).quasiMeasurePreserving.ae hinterpolation
  have hRL := Measure.ae_ae_of_ae_prod hswap
  obtain ⟨z, hzR, hyz, hzL⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hRpos (hright.and hRL)
  obtain ⟨x, hxL, hxy, hxR, hxyz⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hLpos (hleft.and (hLR.and hzL))
  have hxz : φ x ≠ φ z := ne_of_lt (hxy.trans hyz)
  have hyplane : y ∈ affinePlane φ V x z := hxyz
  have hxplane : x ∈ affinePlane φ V x z := left_mem_affinePlane φ V x z hxz
  have hzplane : z ∈ affinePlane φ V x z := right_mem_affinePlane φ V x z hxz
  have hleftplane : ∀ᵐ w ∂μ.restrict L, w ∈ affinePlane φ V x z := by
    have hreanchor : affinePlane φ V y z = affinePlane φ V x z :=
      affinePlane_reanchor hyplane hzplane (ne_of_lt hyz)
    filter_upwards [hleft, hzL] with w hwy hw
    rw [← hreanchor]
    exact affineLine_left_of_middle (ne_of_lt (hwy.trans hyz)) (ne_of_lt hyz) hw
  have hrightplane : ∀ᵐ w ∂μ.restrict R, w ∈ affinePlane φ V x z := by
    have hreanchor : affinePlane φ V x y = affinePlane φ V x z :=
      affinePlane_reanchor hxplane hyplane (ne_of_lt hxy)
    filter_upwards [hright, hxR] with w hyw hw
    rw [← hreanchor]
    exact affineLine_right_of_middle (ne_of_lt (hxy.trans hyw)) (ne_of_lt hxy) hw
  refine ⟨x, hxL, z, hzR, hxy, hyz, hyplane, ?_⟩
  filter_upwards [(ae_restrict_iff' hL).mp hleftplane,
    (ae_restrict_iff' hR).mp hrightplane] with w hwL hwR hw
  rcases hw with hw | hw
  · exact hwL hw
  · exact hwR hw

end Erdos1017.OrderedZeroTripleGeometry
