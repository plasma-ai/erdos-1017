module

public import Erdos1017.Models.Kernel.PositiveSpectralSubspace
public import Erdos1017.Models.Capped.CappedRegularKernel
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Reindexing kernels along measure-preserving equivalences

Composition with a measure-preserving measurable equivalence is a surjective
linear isometry of L2 (`reindexL2`), and positive spectral subspaces, the
positive index and constant shifted rows are preserved by this alignment,
including for the shifted operator of a pulled-back model.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Composition with an actual measure-preserving measurable equivalence
is a surjective linear isometry of the original L2 space. -/
def reindexL2 (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e he) (by
    intro f
    refine ⟨Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he) f, ?_⟩
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he) f) = f
    have h := Lp.compMeasurePreserving_comp_apply f (MeasurePreserving.symm e he) he
    simpa only [e.symm_comp_self, Lp.compMeasurePreserving_id_apply] using h.symm)

theorem reindexL2_ae (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, reindexL2 e he f x = f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

variable [IsProbabilityMeasure μ]

/-- The actual kernel in the reindexed coordinates. -/
def reindexKernel (K : Ω → Ω → ℝ) (e : Ω ≃ᵐ Ω) : Ω → Ω → ℝ :=
  fun x y => K (e x) (e y)

theorem reindexKernel_measurable (K : Ω → Ω → ℝ) (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ μ)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ)) :
    AEStronglyMeasurable (fun p : Ω × Ω => reindexKernel K e p.1 p.2) (μ.prod μ) :=
  hK.comp_measurePreserving (he.prod he)

theorem reindexKernel_bound (K : Ω → Ω → ℝ) (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ μ) {B : ℝ}
    (hB : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖reindexKernel K e p.1 p.2‖ ≤ B :=
  (he.prod he).quasiMeasurePreserving.ae hB

/-- The actual reindexed integral operator intertwines with L2 composition.
The equality follows from the original product-measure change of variables. -/
theorem operator_reindex_intertwines
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) (f : Lp ℝ 2 μ) :
    operator (reindexKernel K e) hB0 (reindexKernel_measurable K e he hK)
        (reindexKernel_bound K e he hB) (reindexL2 e he f) =
      reindexL2 e he (operator K hB0 hK hB f) := by
  apply ext_inner_right ℝ
  intro g
  obtain ⟨g, rfl⟩ := (reindexL2 e he).surjective g
  rw [(reindexL2 e he).inner_map_map, operator_inner, operator_inner]
  calc
    _ = ∫ p : Ω × Ω, K (e p.1) (e p.2) * f (e p.2) * g (e p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (reindexL2_ae e he g),
        Measure.quasiMeasurePreserving_snd.ae (reindexL2_ae e he f)] with p hp hq
      rw [hp, hq]
      rfl
    _ = _ := (he.prod he).integral_comp (e.prodCongr e).measurableEmbedding
      (fun p : Ω × Ω => K p.1 p.2 * f p.2 * g p.1)

/-- Pointwise unitary conjugacy of the actual reindexed integral operator. -/
theorem operator_reindex_conjugate
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) (f : Lp ℝ 2 μ) :
    operator (reindexKernel K e) hB0 (reindexKernel_measurable K e he hK)
        (reindexKernel_bound K e he hB) f =
      reindexL2 e he (operator K hB0 hK hB ((reindexL2 e he).symm f)) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    operator_reindex_intertwines K hB0 hK hB e he ((reindexL2 e he).symm f)

section PositiveSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual intertwining by a linear equivalence transports every eigenspace. -/
theorem eigenspace_map_of_intertwines (S T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] E)
    (h : ∀ x, S (e x) = e (T x)) (a : ℝ) :
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

/-- The actual positive spectral subspaces are transported by the same
linear equivalence; no aligned spectral-rank premise is needed. -/
theorem positiveSpectralSubspace_map_of_intertwines (S T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] E)
    (h : ∀ x, S (e x) = e (T x)) :
    (positiveSpectralSubspace T).map e.toLinearMap = positiveSpectralSubspace S := by
  simp only [positiveSpectralSubspace, Submodule.map_iSup, eigenspace_map_of_intertwines S T e h]

/-- Reindexing gives an actual linear equivalence of the positive subspaces. -/
def positiveSubspaceEquivOfIntertwines (S T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] E)
    (h : ∀ x, S (e x) = e (T x)) : positiveSpectralSubspace T ≃ₗ[ℝ] positiveSpectralSubspace S :=
  e.ofSubmodules _ _ (positiveSpectralSubspace_map_of_intertwines S T e h)

theorem finiteDimensional_positive_of_intertwines (S T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] E)
    (h : ∀ x, S (e x) = e (T x))
    [FiniteDimensional ℝ (positiveSpectralSubspace T)] :
    FiniteDimensional ℝ (positiveSpectralSubspace S) := by
  let f := positiveSubspaceEquivOfIntertwines S T e h
  exact FiniteDimensional.of_injective f.symm.toLinearMap f.symm.injective

theorem finrank_positive_eq_of_intertwines (S T : E →L[ℝ] E) (e : E ≃ₗ[ℝ] E)
    (h : ∀ x, S (e x) = e (T x)) :
    Module.finrank ℝ (positiveSpectralSubspace S) = Module.finrank ℝ (positiveSpectralSubspace T) :=
  (positiveSubspaceEquivOfIntertwines S T e h).finrank_eq.symm

end PositiveSubspace

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The shifted operator of an actual pulled-back model is conjugate to
the old shifted operator by the actual measure-preserving L2 isometry. -/
theorem shiftedOperator_pullback_intertwines (W : Model Ω μ) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) (f : Lp ℝ 2 μ) :
    shiftedOperator (W.pullback e he) m (KernelOperator.reindexL2 e he f) =
      KernelOperator.reindexL2 e he (shiftedOperator W m f) := by
  exact KernelOperator.operator_reindex_intertwines (shiftedKernel W m) (by positivity)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) e he f

/-- Positive spectral dimension is preserved under the actual alignment. -/
theorem finiteDimensional_positive_shiftedOperator_pullback (W : Model Ω μ) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))] :
    FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator (W.pullback e he) m)) :=
  KernelOperator.finiteDimensional_positive_of_intertwines _ _ (KernelOperator.reindexL2 e he).toLinearEquiv
    (shiftedOperator_pullback_intertwines W m e he)

/-- The actual positive index is unchanged by an invertible alignment. -/
theorem finrank_positive_shiftedOperator_pullback (W : Model Ω μ) (m : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator (W.pullback e he) m)) =
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) :=
  KernelOperator.finrank_positive_eq_of_intertwines _ _ (KernelOperator.reindexL2 e he).toLinearEquiv
    (shiftedOperator_pullback_intertwines W m e he)

/-- A constant actual shifted row is preserved by the same alignment. -/
theorem shifted_row_pullback (W : Model Ω μ) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    ∀ᵐ x ∂μ, (∫ y, shiftedKernel (W.pullback e he) m x y ∂μ) = ν := by
  filter_upwards [he.quasiMeasurePreserving.ae hrow] with x hx
  change (∫ y, shiftedKernel W m (e x) (e y) ∂μ) = ν
  rw [he.integral_comp' (fun y => shiftedKernel W m (e x) y)]
  exact hx

end Erdos1017.CappedModel
