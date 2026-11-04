module

public import Erdos1017.Models.Selection.FullEditComparison
public import Erdos1017.Models.Capped.CappedShiftedSelection

/-!
# Selecting the kernel of a full model

In the regular branch one multiplier governs the common-envelope edit signs, a
stationary shifted row and positive index at most two; in the singular branch
the index bound is one. Averaging then selects an equally good fully feasible
model whose sampled shifted color is the selected kernel almost surely, used in
`FullStationaryCompactness` and `FullStrictGapStructure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The mass of a one-endpoint convex edit. -/
def fullEndpointWeight (t : unitInterval) : NNReal := ⟨(t : ℝ), t.property.1⟩

@[simp] theorem fullEndpointWeight_coe (t : unitInterval) :
    (fullEndpointWeight t : ℝ) = (t : ℝ) := rfl

/-- The convex path to one common-envelope endpoint is an actual model path. -/
def fullEndpointMixture (W V : Model Ω μ) (t : unitInterval) : Model Ω μ :=
  editMixture W (fun _ : Fin 1 => V) (fun _ => fullEndpointWeight t) (by
    have hw : fullEndpointWeight t ≤ 1 := NNReal.coe_le_coe.mpr t.property.2
    simpa only [Fin.sum_univ_one] using hw)

omit [IsProbabilityMeasure μ] in
theorem fullEndpointMixture_moment (W V : Model Ω μ) (t : unitInterval)
    (h : CappedColor → ℝ) (hh : StronglyMeasurable h) (B : ℝ)
    (hB : ∀ c, ‖h c‖ ≤ B) (p : Ω × Ω) :
    (fullEndpointMixture W V t).moment h p =
      W.moment h p + (t : ℝ) * (V.moment h p - W.moment h p) := by
  rw [fullEndpointMixture, moment_editMixture W (fun _ : Fin 1 => V)
    (fun _ => fullEndpointWeight t) _ p h hh B hB]
  simp only [Fin.sum_univ_one, fullEndpointWeight_coe]
  ring

/-- The single-endpoint mixture packages every envelope-dominated model
as an actual affine edit, so regular signs cover arbitrary such endpoints. -/
def fullEndpointAffineEdit (W V : Model Ω μ)
    (hV : ∀ p, V.kernel p ≪ (editEnvelope W).kernel p) : AffineEdit W where
  model := fullEndpointMixture W V
  feasible := by
    intro r hW t
    exact feasible_editMixture W (fun _ : Fin 1 => V)
      (fun _ => fullEndpointWeight t) _ (fun _ p => hV p) hW
  adjacency := by
    intro t p
    have ht := fullEndpointMixture_moment W V t CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2) p
    have h1 := fullEndpointMixture_moment W V 1 CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2) p
    norm_num at h1
    rw [ht, h1]
  charge := by
    intro t p
    have hbound (c : CappedColor) : ‖CappedColor.charge c‖ ≤ 3 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩
    have ht := fullEndpointMixture_moment W V t CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable 3 hbound p
    have h1 := fullEndpointMixture_moment W V 1 CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable 3 hbound p
    norm_num at h1
    rw [ht, h1]

/-- The regular vertex multiplier controls every actual endpoint dominated
by the common envelope, including masked deletion and support insertion. -/
theorem full_regular_edit_signs (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W)) (m : ℝ)
    (hm : Variation.weightFirstVariation (chargeOperator W) =
      m • Variation.weightFirstVariation (adjacencyOperator W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    HasEditSigns W m := by
  intro V hV
  let E := fullEndpointAffineEdit W V hV
  have hsign := full_affine_edit_sign W hW hopt E m hm hregular
  have hA (p : Ω × Ω) : (E.model 1).moment CappedColor.adjacency p =
      V.moment CappedColor.adjacency p := by
    change (fullEndpointMixture W V 1).moment CappedColor.adjacency p = _
    have h := fullEndpointMixture_moment W V 1 CappedColor.adjacency
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
        rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
        exact (CappedColor.adjacency_mem c).2) p
    norm_num at h
    exact h
  have hY (p : Ω × Ω) : (E.model 1).moment CappedColor.charge p =
      V.moment CappedColor.charge p := by
    change (fullEndpointMixture W V 1).moment CappedColor.charge p = _
    have h := fullEndpointMixture_moment W V 1 CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
          (CappedColor.charge_mem c).2.trans (by norm_num)⟩) p
    norm_num at h
    exact h
  have hAfn : (fun p => (E.model 1).moment CappedColor.adjacency p) =
      (fun p => V.moment CappedColor.adjacency p) := funext hA
  have hYfn : (fun p => (E.model 1).moment CappedColor.charge p) =
      (fun p => V.moment CappedColor.charge p) := funext hY
  have hd : density (E.model 1) = density V := by simp only [density, hAfn]
  have hc : objective (E.model 1) = objective V := by simp only [objective, hYfn]
  rwa [hd, hc] at hsign

/-- One regular multiplier governs the actual common-envelope edit signs,
stationary shifted row, and positive spectral index at most two. -/
theorem exists_full_regular_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧ HasEditSigns W m ∧
      Variation.weightFirstVariation (chargeOperator W) =
        m • Variation.weightFirstVariation (adjacencyOperator W) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      ν = 2 * (objective W - m * density W) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2 := by
  obtain ⟨m, ν, hm, heigen, hfinite, hindex⟩ :=
    exists_full_regular_multiplier W hW hopt hregular
  have hsigns := full_regular_edit_signs W hW hopt m hm hregular
  have hbounds := multiplier_bounds_of_editSigns W m hsigns hd0 hdhalf
  have hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) ν
    change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = _
    rwa [shiftedOperator_eq]
  refine ⟨m, ν, hbounds, hsigns, hm, ?_,
    shiftedMoment_complementary_of_editSigns W m hsigns,
    hrow, shifted_stationary_value W m ν hrow, ?_, ?_⟩
  · filter_upwards [shiftedMoment_nonnegative_of_editSigns W m hsigns] with p hp
    refine ⟨hp, ?_⟩
    rw [shiftedMoment_eq]
    have ha := adjacency_moment_mem W p
    have hy := charge_moment_le_adjacency W p
    have hprod := mul_nonneg (by linarith [hbounds.1] : 0 ≤ m + 3) ha.1
    nlinarith [ha.2]
  · rwa [shiftedOperator_eq]
  · rwa [shiftedOperator_eq]

/-- Separation over the family of all actual common-envelope endpoints
gives one singular multiplier for every vertex and every such edit. -/
theorem exists_full_singular_common_multiplier (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0) :
    ∃ m : ℝ, -3 ≤ m ∧ m ≤ 3 ∧
      (∀ f : Variation.WeightDirections μ,
        Variation.weightSecondVariation (chargeOperator W) f f -
          m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) ∧
      HasEditSigns W m := by
  let endpoints := {V : Model Ω μ // ∀ p, V.kernel p ≪ (editEnvelope W).kernel p}
  obtain ⟨m, hlo, hhi, hweight, hedit⟩ := exists_full_singular_multiplier_with_edits W hW hopt hsingular
    (fun V : endpoints => V.val) (fun V => V.property)
  refine ⟨m, hlo, hhi, hweight, ?_⟩
  intro V hV
  exact hedit ⟨V, hV⟩

theorem full_singular_stationary_index_of_multiplier [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0) (m : ℝ)
    (hweight : ∀ f : Variation.WeightDirections μ,
      Variation.weightSecondVariation (chargeOperator W) f f -
        m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) :
    ∃ ν : ℝ, (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1 := by
  let one := Lp.const 2 μ (1 : ℝ)
  have hyzero : Variation.weightFirstVariation (chargeOperator W) = 0 := by
    have hdegree := (Variation.kernel_weightFirstVariation_eq_zero_iff
      (adjacencyKernel W) (by norm_num) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W)).mp hsingular
    exact full_singular_charge_firstVariation_zero W hW hopt hdegree
  obtain ⟨a, ha⟩ := (Variation.weightFirstVariation_eq_zero_iff (adjacencyOperator W)
    (KernelOperator.operator_range_bounded _ _ _ _ one)).mp hsingular
  obtain ⟨y, hy⟩ := (Variation.weightFirstVariation_eq_zero_iff (chargeOperator W)
    (KernelOperator.operator_range_bounded _ _ _ _ one)).mp hyzero
  have hrow : ∀ᵐ x ∂μ, (∫ y', shiftedKernel W m x y' ∂μ) = y - m * a := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    change shiftedOperator W m one = _
    rw [shiftedOperator_eq]
    change chargeOperator W one - m • adjacencyOperator W one = _
    rw [ha, hy, smul_smul, sub_smul]
  let C := (innerSL ℝ one).toLinearMap
  have htest (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ) (hc : C f = 0) :
      ⟪shiftedOperator W m f, f⟫ ≤ 0 := by
    have hmean : (∫ x, f x ∂μ) = 0 := by
      rw [← KernelOperator.inner_constant_one]
      exact hc
    obtain ⟨g, hg⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
    have h := hweight g
    change ⟪chargeOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ -
      m * ⟪adjacencyOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ ≤ 0 at h
    rw [hg] at h
    rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
    exact h
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hindex := KernelOperator.positive_subspace_dimension_le_range_constraints
    (shiftedOperator W m) (KernelOperator.operator_isCompact _ _ _ _)
    (KernelOperator.operator_symmetric _ _ _ _ hsym) C (KernelOperator.boundedL2Submodule μ)
    (KernelOperator.operator_range_bounded _ _ _ _) htest
  exact ⟨y - m * a, hrow, hindex.1, by simpa using hindex.2⟩

/-- The singular full-model branch has the actual kernel signs selected by its
common multiplier, with the stronger positive-index bound one. -/
theorem exists_full_singular_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧ HasEditSigns W m ∧
      (∀ f : Variation.WeightDirections μ,
        Variation.weightSecondVariation (chargeOperator W) f f -
          m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      ν = 2 * (objective W - m * density W) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1 := by
  obtain ⟨m, _, _, hweight, hsigns⟩ := exists_full_singular_common_multiplier W hW hopt hsingular
  obtain ⟨ν, hrow, hfinite, hindex⟩ := full_singular_stationary_index_of_multiplier W hW hopt hsingular m hweight
  have hbounds := multiplier_bounds_of_editSigns W m hsigns hd0 hdhalf
  refine ⟨m, ν, hbounds, hsigns, hweight, ?_,
    shiftedMoment_complementary_of_editSigns W m hsigns, hrow,
    shifted_stationary_value W m ν hrow, hfinite, hindex⟩
  filter_upwards [shiftedMoment_nonnegative_of_editSigns W m hsigns] with p hp
  refine ⟨hp, ?_⟩
  rw [shiftedMoment_eq]
  have ha := adjacency_moment_mem W p
  have hy := charge_moment_le_adjacency W p
  have hprod := mul_nonneg (by linarith [hbounds.1] : 0 ≤ m + 3) ha.1
  nlinarith [ha.2]

/-- Averaging selects an equally good fully feasible model whose actual
sampled shifted color equals the selected shifted kernel almost surely. -/
theorem exists_selected_full_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ (V : Model Ω μ) (m ν : ℝ), FullFeasible V ∧
      objective V = FractionalGraph.densityLimit (density V) ∧
      density V = density W ∧ objective V = objective W ∧
      m ∈ Set.Icc (-3) 1 ∧ HasEditSigns V m ∧
      (∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p, shiftedColor m c = shiftedMoment V m p) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment V m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - V.moment CappedColor.adjacency p) * shiftedMoment V m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν) ∧
      ν = 2 * (objective V - m * density V) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2 := by
  let V := averaged W
  have hV : FullFeasible V := fullFeasible_averaged W hW
  have hdV : density V = density W := density_averaged W
  have hcV : objective V = objective W := objective_averaged W
  have hoptV : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hcV, hdV]
    exact hopt
  have hdet (p : Ω × Ω) : ∀ᵐ c ∂V.kernel p,
      CappedColor.charge c = conditionalCharge V p * CappedColor.adjacency c := by
    change ∀ᵐ c ∂(averaged W).kernel p,
      CappedColor.charge c = conditionalCharge (averaged W) p * CappedColor.adjacency c
    rw [conditionalCharge_averaged]
    exact averaged_deterministic W p
  have hex : ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧ HasEditSigns V m ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment V m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - V.moment CappedColor.adjacency p) * shiftedMoment V m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν) ∧
      ν = 2 * (objective V - m * density V) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2 := by
    by_cases hs : Variation.weightFirstVariation (adjacencyOperator V) = 0
    · obtain ⟨m, ν, hm, hsigns, _, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
        exists_full_singular_kernel V hV hoptV hs (hdV.symm ▸ hd0) (hdV.symm ▸ hdhalf)
      exact ⟨m, ν, hm, hsigns, hmem, hcomp, hrow, hν, hfinite, hindex.trans (by norm_num)⟩
    · obtain ⟨m, ν, hm, hsigns, _, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
        exists_full_regular_kernel V hV hoptV hs (hdV.symm ▸ hd0) (hdV.symm ▸ hdhalf)
      exact ⟨m, ν, hm, hsigns, hmem, hcomp, hrow, hν, hfinite, hindex⟩
  obtain ⟨m, ν, hm, hsigns, hmem, hcomp, hrow, hν, hfinite, hindex⟩ := hex
  exact ⟨V, m, ν, hV, hoptV, hdV, hcV, hm, hsigns,
    shiftedColor_deterministic_of_complementary V m hcomp hdet,
    hmem, hcomp, hrow, hν, hfinite, hindex⟩

end Erdos1017.CappedModel
