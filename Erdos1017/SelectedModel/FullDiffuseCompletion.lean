module

public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.SelectedModel.Capped.CappedZeroCompletion
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.SelectedModel.StationaryFeature
public import Erdos1017.Models.Kernel.FeatureDiagonal
public import Erdos1017.SelectedModel.Selection.FullPositiveEigenvector
public import Erdos1017.SelectedModel.Capped.CappedCompletionDensityReturn

/-!
# Diffuse sets covered by two cliques are complete

Strict full optimality supplies a bounded direction transverse to the adjacency
constraint and positive for the shifted operator, and for the same full
stationary optimizer a measurable two-clique-covered diffuse set has no missing
adjacency pairs almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Strict full optimality supplies a bounded direction transverse to the
adjacency constraint and positive for the same shifted operator. -/
theorem FullStationaryClass.exists_transverse_positive_direction
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ u : Variation.WeightDirections μ,
      Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 ∧
        0 < Variation.weightSecondVariation (shiftedOperator W m) u u := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  have hfirst := shiftedFirstVariation_zero_of_stationary W m (2 * (c - m * d)) hW.stationary
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  exact ⟨u, full_positive_direction_transverse W hW.full hopt m hfirst hs.regular u hq, hq⟩

/-- The actual stationary optimizer supplies every scalar clique test for
completing a measurable set covered by two physical cliques. The feature
and its canonical diagonal bound are constructed from the shifted operator. -/
theorem FullStationaryClass.physical_completion_tests
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (D : Set Ω) [DecidablePred (· ∈ D)]
    (C : Bool → Set Ω) (hC : ∀ b, MeasurableSet (C b))
    (hcover : ∀ᵐ x ∂μ, x ∈ D → x ∈ C false ∨ x ∈ C true)
    (hclique : ∀ b, ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ C b → p.2 ∈ C b →
        PhysicalRepresentative.adjacency W m p.1 p.2 = true) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D)
      (FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) D (-m)) n := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  have hB : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hfour := shiftedOperator_eq_of_bound W m (by norm_num : (0 : ℝ) ≤ 4) hB
  have hfinite : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hB)) := by
    rw [← hfour]
    exact hW.finite_positive
  have hindex : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hB)) ≤ 2 := by
    rw [← hfour]
    exact hW.index_le_two
  have heigenFour : KernelOperator.operator (shiftedKernel W m)
      (by norm_num) (shiftedKernel_measurable W m) hB w = σ • w := by
    rw [← hfour]
    exact heigen
  have hsym : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  obtain ⟨ι, hcount, F₀, J, hF₀, _, hJsym, hrep₀⟩ :=
    KernelOperator.exists_uniform_feature_of_stationary_positive_index_two
      (shiftedKernel W m) (shiftedKernel_measurable W m) hB
      (hW.moment_mem.mono (fun _ hp => hp.1)) hsym
      (2 * (c - m * d)) hs.stationary_pos hW.stationary hfinite hindex
      w hw hmean σ σ hσ le_rfl heigenFour
  let := hcount
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  let F := hF₀.mk F₀
  have hFm : StronglyMeasurable F := hF₀.stronglyMeasurable_mk
  have hFe : F₀ =ᵐ[μ] F := hF₀.ae_eq_mk
  have hpairEq : ∀ᵐ p ∂μ.prod μ,
      shiftedKernel W m p.1 p.2 = ⟪J (F p.1), F p.2⟫ := by
    filter_upwards [hrep₀,
      Measure.quasiMeasurePreserving_fst.ae hFe,
      Measure.quasiMeasurePreserving_snd.ae hFe] with p hp hfst hsnd
    rwa [← hfst, ← hsnd]
  have hpairBound : ∀ᵐ p ∂μ.prod μ,
      0 ≤ ⟪J (F p.1), F p.2⟫ ∧ ⟪J (F p.1), F p.2⟫ ≤ 4 := by
    filter_upwards [hpairEq, hW.moment_mem] with p hp hb
    rw [← hp]
    exact hb
  have hdiag : ∀ᵐ x ∂μ, 0 ≤ ⟪J (F x), F x⟫ :=
    (KernelOperator.feature_diagonal_bounds F hFm.aestronglyMeasurable J 0 4
      hpairBound).mono (fun _ hx => hx.1)
  have hpositive : ∀ᵐ p ∂μ.prod μ,
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
        0 < shiftedKernel W m p.1 p.2) := by
    filter_upwards [PhysicalRepresentative.adjacency_ae_eq W m] with p hp
    rw [hp]
    simp [positiveAdjacency, shiftedKernel]
  have hcharge := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  have hadj := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hpair : ∀ᵐ p ∂μ.prod μ,
      0 ≤ ⟪J (F p.1), F p.2⟫ ∧
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
        0 < ⟪J (F p.1), F p.2⟫) ∧
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true →
        PhysicalRepresentative.charge W m p.1 p.2 =
          ⟪J (F p.1), F p.2⟫ - (-m)) := by
    filter_upwards [hpairBound, hpairEq, hpositive, hcharge, hadj] with
      p hb he hp hy ha
    refine ⟨hb.1, ?_, ?_⟩
    · rwa [← he]
    · intro hA
      have hAone : W.moment CappedColor.adjacency p = 1 := by rw [ha, hA]; rfl
      calc
        _ = chargeKernel W p.1 p.2 := hy
        _ = shiftedKernel W m p.1 p.2 + m := by
          rw [shiftedKernel, shiftedMoment_eq W m p, hAone]
          change W.moment CappedColor.charge p = W.moment CappedColor.charge p - m * 1 + m
          ring
        _ = ⟪J (F p.1), F p.2⟫ - (-m) := by rw [he]; ring
  intro n
  exact FiniteArity.feasibleOrder_complete_of_two_clique_cover μ
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
    F hFm.measurable J (fun x y => (hJsym x y).trans (real_inner_comm x (J y)).symm)
    (-m) hpair hdiag D C hC hcover hclique n
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic n)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Zero missing-pair mass is exactly almost-everywhere completeness on
the original model's D-square, under the actual strict-support identity. -/
theorem ZeroCompletion.ae_complete_of_missingMass_eq_zero
    (W : Model Ω μ) (m : ℝ) (D : Set Ω) [DecidablePred (· ∈ D)]
    (hD : MeasurableSet D)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hzero : ZeroCompletion.missingMass W m D = 0) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1 := by
  have hint : ∫ p : Ω × Ω, ZeroCompletion.missing W m D p ∂μ.prod μ = 0 := by
    unfold ZeroCompletion.missingMass at hzero
    linarith
  have hmissing := (integral_eq_zero_iff_of_nonneg
    (fun p => (ZeroCompletion.missing_mem W m D p).1)
    (ZeroCompletion.integrable_missing W m D hD)).mp hint
  filter_upwards [hmissing, PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport]
    with p hp ha hpD hqD
  by_cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 = true
  · simpa [hA] using ha
  · have hAf : PhysicalRepresentative.adjacency W m p.1 p.2 = false :=
      Bool.eq_false_iff.mpr hA
    have hbad : ZeroCompletion.missing W m D p = 1 := by
      simp [ZeroCompletion.missing, hpD, hqD, hAf]
    rw [hbad] at hp
    norm_num at hp

/-- For the same full stationary optimizer, a measurable two-clique-covered
diffuse set has no missing adjacency pairs almost everywhere. The completed
colored competitors and density return are derived from the original model. -/
theorem FullStationaryClass.ae_complete_diffuse_of_two_clique_cover
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (D : Set Ω) (hD : MeasurableSet D)
    (C : Bool → Set Ω) (hC : ∀ b, MeasurableSet (C b))
    (hcover : ∀ᵐ x ∂μ, x ∈ D → x ∈ C false ∨ x ∈ C true)
    (hclique : ∀ b, ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ C b → p.2 ∈ C b →
        PhysicalRepresentative.adjacency W m p.1 p.2 = true) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D →
      W.moment CappedColor.adjacency p = 1 := by
  classical
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨u, hL, hQ⟩ := hW.exists_transverse_positive_direction hd hgap
  have hcap := hW.physical_completion_tests hd hgap D C hC hcover hclique
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hzero := ZeroCompletion.missingMass_eq_zero_of_full_optimum W hopt m
    (2 * (c - m * d)) hW.multiplier_mem hs.strict_support hW.stationary
    u hL hQ D hD (fun n _ => hcap n)
  exact ZeroCompletion.ae_complete_of_missingMass_eq_zero W m D hD hs.strict_support hzero

end Erdos1017.CappedModel
