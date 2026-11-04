module

public import Erdos1017.Models.Capped.CappedEditEnvelope

/-!
# Convex mixtures of capped edits

A finite convex mixture of edits (`editMixture`) is probability valued, keeps
the original pair law on unused mass, is feasible and has computed moments;
squared edit amplitudes give a mixture (`squaredEditMixture`) on the local
domain `tau * sum a_i^2 <= 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]

def editMixtureKernel (W : Model Ω μ) (V : ι → Model Ω μ) (w : ι → NNReal) :
    Kernel (Ω × Ω) CappedColor where
  toFun p := (1 - ∑ i, w i) • W.kernel p + ∑ i, w i • (V i).kernel p
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply]
    exact (measurable_const.mul ((Measure.measurable_coe hs).comp W.kernel.measurable)).add
      (Finset.measurable_sum _ (fun i _ => measurable_const.mul
        ((Measure.measurable_coe hs).comp (V i).kernel.measurable)))

/-- A genuine probability-valued finite convex mixture. The unused mass
retains the original pair law, and the weight sum is explicitly at most one. -/
def editMixture (W : Model Ω μ) (V : ι → Model Ω μ) (w : ι → NNReal)
    (hw : ∑ i, w i ≤ 1) : Model Ω μ where
  kernel := editMixtureKernel W V w
  markov := ⟨fun p => ⟨by
    change ((1 - ∑ i, w i) • W.kernel p + ∑ i, w i • (V i).kernel p) Set.univ = 1
    simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
      measure_univ, ENNReal.smul_one]
    exact_mod_cast tsub_add_cancel_of_le hw⟩⟩
  symm := by
    have hV : ∀ᵐ p ∂μ.prod μ, ∀ i, (V i).kernel p.swap = (V i).kernel p :=
      ae_all_iff.mpr (fun i => (V i).symm)
    filter_upwards [W.symm, hV] with p hp hV
    change (1 - ∑ i, w i) • W.kernel p.swap + ∑ i, w i • (V i).kernel p.swap = _
    simp only [hp, hV]
    rfl

theorem editMixture_absolutelyContinuous (W : Model Ω μ) (V : ι → Model Ω μ)
    (w : ι → NNReal) (hw : ∑ i, w i ≤ 1)
    (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p) (p : Ω × Ω) :
    (editMixture W V w hw).kernel p ≪ (editEnvelope W).kernel p := by
  change (1 - ∑ i, w i) • W.kernel p + ∑ i, w i • (V i).kernel p ≪ _
  apply ((old_absolutelyContinuous_editEnvelope W p).smul_left _).add_left
  exact Finset.sum_induction (fun i => w i • (V i).kernel p)
    (fun ν => ν ≪ (editEnvelope W).kernel p)
    (fun _ _ hν hη => hν.add_left hη) (Measure.AbsolutelyContinuous.zero _)
    (fun i _ => (hV i p).smul_left _)

theorem feasible_editMixture [IsProbabilityMeasure μ] (W : Model Ω μ) (V : ι → Model Ω μ)
    (w : ι → NNReal) (hw : ∑ i, w i ≤ 1)
    (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p)
    {r : ℕ} (hW : Feasible r W) : Feasible r (editMixture W V w hw) :=
  feasible_of_pair_absolutelyContinuous _ _ (feasible_editEnvelope W hW)
    (editMixture_absolutelyContinuous W V w hw hV)

theorem moment_editMixture (W : Model Ω μ) (V : ι → Model Ω μ) (w : ι → NNReal)
    (hw : ∑ i, w i ≤ 1) (p : Ω × Ω) (h : CappedColor → ℝ)
    (hh : StronglyMeasurable h) (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (editMixture W V w hw).moment h p =
      (1 - ∑ i, (w i : ℝ)) * W.moment h p + ∑ i, (w i : ℝ) * (V i).moment h p := by
  have hint (U : Model Ω μ) : Integrable h (U.kernel p) :=
    Integrable.of_bound hh.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  change (∫ c, h c ∂((1 - ∑ i, w i) • W.kernel p + ∑ i, w i • (V i).kernel p)) = _
  have hsum : Integrable h (∑ i, w i • (V i).kernel p) :=
    integrable_finsetSum_measure.mpr (fun i _ => (hint (V i)).smul_measure_nnreal)
  rw [integral_add_measure (hint W).smul_measure_nnreal hsum,
    integral_finsetSum_measure (fun i _ => (hint (V i)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_sub hw, NNReal.coe_one, NNReal.coe_sum]
  rfl

def editAmplitudeWeights (a : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) : ι → NNReal :=
  fun i => ⟨τ * (a i) ^ 2, mul_nonneg hτ (sq_nonneg _)⟩

theorem editAmplitudeWeights_mass (a : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hmass : τ * ∑ i, (a i) ^ 2 ≤ 1) : ∑ i, editAmplitudeWeights a τ hτ i ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_sum]
  change (∑ i, τ * (a i) ^ 2) ≤ 1
  simpa only [Finset.mul_sum] using hmass

/-- Simultaneous squared edit amplitudes use a genuine convex mixture on
the explicit local domain `tau * sum a_i^2 <= 1`. -/
def squaredEditMixture (W : Model Ω μ) (V : ι → Model Ω μ) (a : ι → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hmass : τ * ∑ i, (a i) ^ 2 ≤ 1) : Model Ω μ :=
  editMixture W V (editAmplitudeWeights a τ hτ) (editAmplitudeWeights_mass a τ hτ hmass)

theorem feasible_squaredEditMixture [IsProbabilityMeasure μ] (W : Model Ω μ)
    (V : ι → Model Ω μ) (a : ι → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hmass : τ * ∑ i, (a i) ^ 2 ≤ 1)
    (hV : ∀ i p, (V i).kernel p ≪ (editEnvelope W).kernel p)
    {r : ℕ} (hW : Feasible r W) : Feasible r (squaredEditMixture W V a τ hτ hmass) :=
  feasible_editMixture W V _ _ hV hW

theorem moment_squaredEditMixture (W : Model Ω μ) (V : ι → Model Ω μ) (a : ι → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hmass : τ * ∑ i, (a i) ^ 2 ≤ 1)
    (p : Ω × Ω) (h : CappedColor → ℝ) (hh : StronglyMeasurable h)
    (B : ℝ) (hB : ∀ c, ‖h c‖ ≤ B) :
    (squaredEditMixture W V a τ hτ hmass).moment h p = W.moment h p +
      τ * ∑ i, (a i) ^ 2 * ((V i).moment h p - W.moment h p) := by
  rw [squaredEditMixture, moment_editMixture W V _ _ p h hh B hB]
  have hc (i : ι) : (editAmplitudeWeights a τ hτ i : ℝ) = τ * (a i) ^ 2 := rfl
  simp only [hc]
  rw [sub_mul, one_mul, Finset.sum_mul, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc]
  ring

end Erdos1017.CappedModel
