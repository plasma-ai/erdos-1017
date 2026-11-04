module

public import Erdos1017.SelectedModel.Structure.SelectedZeroPlaneRows
public import Erdos1017.SelectedModel.Structure.FullCanonicalFeatureRows
public import Erdos1017.SelectedModel.Structure.CanonicalZeroGeometry
public import Erdos1017.SelectedModel.Structure.AffineNeighborhoodExtraction
public import Erdos1017.SelectedModel.CountableZeroMiddleExclusion

/-!
# Canonical middle exclusion

A maximum-energy strict-gap model has one canonical geometry and row map for
which almost no vertex has positive strict zero neighborhoods on both sides.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

open OrderedZeroTripleGeometry

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual maximum-energy strict-gap model has one canonical geometry
and actual row map for which almost no vertex has positive strict zero
neighborhoods on both sides. All plane and countable-atom inputs are derived. -/
theorem FullStationaryClass.exists_canonical_middle_exclusion
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ U : Model Ω μ, FullStationaryClass d c U m →
      stationaryEnergy U m ≤ stationaryEnergy W m) :
    ∃ (σ : ℝ), 0 < σ ∧ ∃ (ι : Type u) (_ : Countable ι)
      (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2)
      (ρ : Ω → Lp ℝ 2 μ) (S : Set Ω),
      KernelOperator.CanonicalIndexTwoFeature μ (shiftedKernel W m) 4
        (2 * (c - m * d)) σ φ V ∧
      StronglyMeasurable ρ ∧ MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      KernelOperator.CanonicalZeroGeometry (2 * (c - m * d)) σ φ V S ∧
      (∀ x ∈ S, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧
      (∀ x ∈ S, ∀ z ∈ S, ρ x = ρ z ↔ φ x = φ z ∧ V x = V z) ∧
      ∀ᵐ y ∂μ,
        μ {x | x ∈ S ∧ φ x < φ y ∧
          KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V x y = 0} = 0 ∨
        μ {z | z ∈ S ∧ φ y < φ z ∧
          KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V y z = 0} = 0 := by
  classical
  obtain ⟨σ, hσ, ι, hcount, φ, V, ρ, S₀, hfeature, hρ, _, _, hS₀ae, hrow₀, _, _⟩ :=
    hW.exists_canonical_row_factorization hd hgap
  have : Countable ι := hcount
  have hrow : ∀ᵐ x ∂μ, (ρ x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x :=
    hS₀ae.mono fun x hx => hrow₀ x hx
  have hstructure := hW.strict_gap_structure hd hgap
  obtain ⟨S, hS, hSae, hgeometry, _, hrowS, _, hcoords⟩ :=
    hfeature.exists_conull_zero_geometry_and_rows hstructure.stationary_pos.le hσ
      (hW.moment_mem.mono (fun _ h => h.1)) ρ hrow
  let L : Ω → Set Ω := fun y => {x | x ∈ S ∧ φ x < φ y ∧
    KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V x y = 0}
  let R : Ω → Set Ω := fun y => {z | z ∈ S ∧ φ y < φ z ∧
    KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V y z = 0}
  have hleft (y : Ω) : MeasurableSet (L y) := by
    have hK : StronglyMeasurable (fun x =>
        KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V x y) := by
      unfold KernelOperator.canonicalPairing
      exact (stronglyMeasurable_const.add
        ((hfeature.scalar_measurable.const_mul σ).mul_const (φ y))).sub
          (hfeature.feature_measurable.inner stronglyMeasurable_const)
    exact hS.inter ((measurableSet_lt hfeature.scalar_measurable.measurable
      measurable_const).inter (measurableSet_eq_fun hK.measurable measurable_const))
  have hright (y : Ω) : MeasurableSet (R y) := by
    have hK : StronglyMeasurable (fun z =>
        KernelOperator.canonicalPairing (2 * (c - m * d)) σ φ V y z) := by
      unfold KernelOperator.canonicalPairing
      exact (stronglyMeasurable_const.add
        (hfeature.scalar_measurable.const_mul (σ * φ y))).sub
          (stronglyMeasurable_const.inner hfeature.feature_measurable)
    exact hS.inter ((measurableSet_lt measurable_const
      hfeature.scalar_measurable.measurable).inter
        (measurableSet_eq_fun hK.measurable measurable_const))
  have htwo (x z : Ω)
      (hpair : IsotropicPair (2 * (c - m * d)) σ φ V x z)
      (_ : μ (affinePlane φ V x z) ≠ 0) :
      ∃ q₁ q₂ : Lp ℝ 2 μ, ∀ᵐ w ∂μ,
        w ∈ affinePlane φ V x z → ρ w = q₁ ∨ ρ w = q₂ :=
    hW.isotropic_plane_two_rowMap_values_of_strict_gap hd hgap hmax ρ hrow
      φ V _ σ hfeature.representation x z hpair
      (measurableSet_affinePlane φ V hfeature.scalar_measurable hfeature.feature_measurable x z)
  have hextract : ∀ᵐ y ∂μ, μ (L y) ≠ 0 → μ (R y) ≠ 0 →
      ∃ x z, IsotropicPair (2 * (c - m * d)) σ φ V x z ∧
        y ∈ affinePlane φ V x z ∧
          ∀ᵐ w ∂μ, w ∈ L y ∪ R y → w ∈ affinePlane φ V x z := by
    filter_upwards [hSae] with y hy hLpos hRpos
    have hinterpolation : ∀ᵐ p ∂(μ.restrict (L y)).prod (μ.restrict (R y)),
        V y = affineLine (φ p.1) (φ p.2) (V p.1) (V p.2) (φ y) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (hleft y)),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hright y))] with p hx hz
      exact (hgeometry.strict_zero_triple hx.1 hy hz.1
        hx.2.1 hz.2.1 hx.2.2 hz.2.2).2.2.2.2
    obtain ⟨x, hx, z, hz, hxy, hyz, hyplane, hneighborhood⟩ :=
      exists_common_affinePlane_of_ae_interpolation φ V y (L y) (R y)
        (hleft y) (hright y) hLpos hRpos
        (by filter_upwards [ae_restrict_mem (hleft y)] with x hx; exact hx.2.1)
        (by filter_upwards [ae_restrict_mem (hright y)] with z hz; exact hz.2.1)
        hinterpolation
    have htriple := hgeometry.strict_zero_triple hx.1 hy hz.1 hxy hyz hx.2.2 hz.2.2
    refine ⟨x, z, ⟨ne_of_lt (hxy.trans hyz), htriple.2.1, htriple.2.2.2.1, ?_⟩,
      hyplane, hneighborhood⟩
    have hzero := htriple.1
    unfold KernelOperator.canonicalPairing at hzero
    linarith
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hnone := ae_not_two_positive_neighborhoods ρ hρ.measurable φ V
    (2 * (c - m * d)) σ S hSae (fun x hx z hz h => (hcoords x hx z hz).mp h)
    L R (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => ⟨h.1, h.2.1⟩) htwo hextract
  exact ⟨σ, hσ, ι, hcount, φ, V, ρ, S, hfeature, hρ, hS, hSae, hgeometry,
    hrowS, hcoords, hnone⟩

end Erdos1017.CappedModel
