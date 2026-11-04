module

public import Erdos1017.Models.Kernel.KernelReindexing

/-!
# Kernel transport between two probability measures

A supplied measure-preserving measurable equivalence induces a surjective L2
isometry, so positive index is preserved without assuming an index-transfer
certificate or using a merely measure-preserving map.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}

/-- Contravariant L2 transport between the two actual probability laws. -/
def measureTransportL2 (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e he) (by
    intro f
    refine ⟨Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he) f, ?_⟩
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he) f) = f
    have h := Lp.compMeasurePreserving_comp_apply f (MeasurePreserving.symm e he) he
    simpa only [e.symm_comp_self, Lp.compMeasurePreserving_id_apply] using h.symm)

theorem measureTransportL2_ae (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂μ, measureTransportL2 e he f x = f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem measureTransportKernel_measurable (K : Ω → Ω → ℝ) (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ ν)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (ν.prod ν)) :
    AEStronglyMeasurable (fun p : Ω × Ω => reindexKernel K e p.1 p.2) (μ.prod μ) :=
  hK.comp_measurePreserving (he.prod he)

omit [IsProbabilityMeasure ν] in
theorem measureTransportKernel_bound (K : Ω → Ω → ℝ) (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ ν) {B : ℝ}
    (hB : ∀ᵐ p : Ω × Ω ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖reindexKernel K e p.1 p.2‖ ≤ B :=
  (he.prod he).quasiMeasurePreserving.ae hB

/-- The actual operators for the two measures intertwine under the derived
surjective L2 isometry, by a product-measure change of variables. -/
theorem operator_measureTransport_intertwines
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (ν.prod ν))
    (hB : ∀ᵐ p : Ω × Ω ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) (f : Lp ℝ 2 ν) :
    operator (reindexKernel K e) hB0 (measureTransportKernel_measurable K e he hK)
        (measureTransportKernel_bound K e he hB) (measureTransportL2 e he f) =
      measureTransportL2 e he (operator K hB0 hK hB f) := by
  apply ext_inner_right ℝ
  intro g
  obtain ⟨g, rfl⟩ := (measureTransportL2 e he).surjective g
  rw [(measureTransportL2 e he).inner_map_map, operator_inner, operator_inner]
  calc
    _ = ∫ p : Ω × Ω, K (e p.1) (e p.2) * f (e p.2) * g (e p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (measureTransportL2_ae e he g),
        Measure.quasiMeasurePreserving_snd.ae (measureTransportL2_ae e he f)] with p hp hq
      rw [hp, hq]
      rfl
    _ = _ := (he.prod he).integral_comp (e.prodCongr e).measurableEmbedding
      (fun p : Ω × Ω => K p.1 p.2 * f p.2 * g p.1)

/-- Unitary conjugacy holds for the actual transported integral operators. -/
theorem operator_measureTransport_conjugate
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (ν.prod ν))
    (hB : ∀ᵐ p : Ω × Ω ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ ν) (f : Lp ℝ 2 μ) :
    operator (reindexKernel K e) hB0 (measureTransportKernel_measurable K e he hK)
        (measureTransportKernel_bound K e he hB) f =
      measureTransportL2 e he (operator K hB0 hK hB ((measureTransportL2 e he).symm f)) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    operator_measureTransport_intertwines K hB0 hK hB e he ((measureTransportL2 e he).symm f)

section PositiveSubspaces

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Intertwining across different Hilbert spaces carries every eigenspace. -/
theorem eigenspace_map_of_cross_intertwines (S : F →L[ℝ] F) (T : E →L[ℝ] E)
    (e : E ≃ₗ[ℝ] F) (h : ∀ x, S (e x) = e (T x)) (a : ℝ) :
    (Module.End.eigenspace T.toLinearMap a).map e.toLinearMap = Module.End.eigenspace S.toLinearMap a := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : T x = a • x := Module.End.mem_eigenspace_iff.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    exact (h x).trans ((congrArg e hx').trans (e.map_smul a x))
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have hy' : S y = a • y := Module.End.mem_eigenspace_iff.mp hy
    apply Module.End.mem_eigenspace_iff.mpr
    apply e.injective
    exact (h (e.symm y)).symm.trans ((congrArg S (e.apply_symm_apply y)).trans
      (hy'.trans (by rw [map_smul, e.apply_symm_apply])))

/-- The positive spectral subspace is transported exactly between the
actual L2 spaces, without a rank preservation hypothesis. -/
theorem positiveSpectralSubspace_map_of_cross_intertwines
    (S : F →L[ℝ] F) (T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] F)
    (h : ∀ x, S (e x) = e (T x)) :
    (positiveSpectralSubspace T).map e.toLinearMap = positiveSpectralSubspace S := by
  simp only [positiveSpectralSubspace, Submodule.map_iSup,
    eigenspace_map_of_cross_intertwines S T e h]

/-- The derived linear equivalence of the two actual positive subspaces. -/
def positiveSubspaceEquivOfCrossIntertwines
    (S : F →L[ℝ] F) (T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] F)
    (h : ∀ x, S (e x) = e (T x)) : positiveSpectralSubspace T ≃ₗ[ℝ] positiveSpectralSubspace S :=
  e.ofSubmodules _ _ (positiveSpectralSubspace_map_of_cross_intertwines S T e h)

theorem finiteDimensional_positive_of_cross_intertwines
    (S : F →L[ℝ] F) (T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] F)
    (h : ∀ x, S (e x) = e (T x)) [FiniteDimensional ℝ (positiveSpectralSubspace T)] :
    FiniteDimensional ℝ (positiveSpectralSubspace S) := by
  let f := positiveSubspaceEquivOfCrossIntertwines S T e h
  exact FiniteDimensional.of_injective f.symm.toLinearMap f.symm.injective

theorem finrank_positive_eq_of_cross_intertwines
    (S : F →L[ℝ] F) (T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] F) (h : ∀ x, S (e x) = e (T x)) :
    Module.finrank ℝ (positiveSpectralSubspace S) = Module.finrank ℝ (positiveSpectralSubspace T) :=
  (positiveSubspaceEquivOfCrossIntertwines S T e h).finrank_eq.symm

end PositiveSubspaces

end Erdos1017.KernelOperator
