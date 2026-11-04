module

public import Erdos1017.Models.Capped.CappedAffineEdit

/-!
# Absolute continuity of capped edits

Thinning, sprinkling, masked thinning, insertion and support insertion are each
absolutely continuous with respect to a common edit envelope, and pairwise
absolute continuity transfers all imposed finite independent sampled tests
(`feasible_of_pair_absolutelyContinuous`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem map_prod_bernoulli {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure C) [IsProbabilityMeasure ν] (f : C × Bool → D) (hf : Measurable f)
    (t : unitInterval) :
    (ν.prod (bernoulliMeasure true false t)).map f =
      unitInterval.toNNReal t • ν.map (fun c => f (c, true)) +
        unitInterval.toNNReal (unitInterval.symm t) • ν.map (fun c => f (c, false)) := by
  rw [bernoulliMeasure_def, Measure.prod_add, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.map_add _ _ hf,
    Measure.map_smul _ hf.aemeasurable, Measure.map_smul _ hf.aemeasurable,
    Measure.prod_dirac, Measure.prod_dirac,
    Measure.map_map hf measurable_prodMk_right, Measure.map_map hf measurable_prodMk_right]
  rfl

theorem thin_kernel (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (thin W t).kernel p = unitInterval.toNNReal t • Measure.dirac CappedColor.absent +
      unitInterval.toNNReal (unitInterval.symm t) • W.kernel p := by
  change (W.couple (bernoulliMeasure true false t)).editKernel coinDelete p = _
  rw [DecoratedKernel.editKernel_apply _ _ measurable_coinDelete]
  simp only [DecoratedKernel.couple, Kernel.prod_apply, Kernel.const_apply]
  rw [map_prod_bernoulli (W.kernel p) (fun c => coinDelete (p, c))
    (measurable_coinDelete.comp measurable_prodMk_left) t]
  simp [coinDelete]

theorem sprinkle_kernel (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (sprinkle W t).kernel p = unitInterval.toNNReal t • (insertAbsent W).kernel p +
      unitInterval.toNNReal (unitInterval.symm t) • W.kernel p := by
  change (W.couple (bernoulliMeasure true false t)).editKernel insertCoin p = _
  rw [DecoratedKernel.editKernel_apply _ _ measurable_insertCoin]
  simp only [DecoratedKernel.couple, Kernel.prod_apply, Kernel.const_apply]
  rw [map_prod_bernoulli (W.kernel p) (fun c => insertCoin (p, c))
    (measurable_insertCoin.comp measurable_prodMk_left) t]
  have htrue : (fun c : CappedColor => insertCoin (p, (c, true))) = insertColor := by
    funext c
    simp [insertCoin, insertColor]
  have hfalse : (fun c : CappedColor => insertCoin (p, (c, false))) = id := by
    funext c
    simp [insertCoin]
  rw [htrue, hfalse, Measure.map_id]
  simp only [insertAbsent, DecoratedKernel.map, Kernel.map_apply _ measurable_insertColor]

def editHalf : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

theorem editHalf_coeff_ne_zero : unitInterval.toNNReal editHalf ≠ 0 := by
  intro h
  have heq := congrArg (fun a : NNReal => (a : ℝ)) h
  norm_num [editHalf] at heq

theorem editHalf_symm : unitInterval.symm editHalf = editHalf := by
  apply Subtype.ext
  norm_num [unitInterval.coe_symm_eq, editHalf]

theorem ac_positive_nnreal_smul {C : Type*} [MeasurableSpace C] (ν : Measure C)
    (q : NNReal) (hq : q ≠ 0) : ν ≪ q • ν := by
  change ν ≪ (q : ENNReal) • ν
  exact Measure.absolutelyContinuous_smul (by exact_mod_cast hq)

theorem old_absolutelyContinuous_thin_half (W : Model Ω μ) (p : Ω × Ω) :
    W.kernel p ≪ (thin W editHalf).kernel p := by
  rw [thin_kernel, editHalf_symm]
  exact (ac_positive_nnreal_smul _ _ editHalf_coeff_ne_zero).add_right' _

theorem absent_absolutelyContinuous_thin_half (W : Model Ω μ) (p : Ω × Ω) :
    Measure.dirac CappedColor.absent ≪ (thin W editHalf).kernel p := by
  rw [thin_kernel]
  exact (ac_positive_nnreal_smul _ _ editHalf_coeff_ne_zero).add_right _

theorem old_absolutelyContinuous_sprinkle_half (W : Model Ω μ) (p : Ω × Ω) :
    W.kernel p ≪ (sprinkle W editHalf).kernel p := by
  rw [sprinkle_kernel, editHalf_symm]
  exact (ac_positive_nnreal_smul _ _ editHalf_coeff_ne_zero).add_right' _

theorem inserted_absolutelyContinuous_sprinkle_half (W : Model Ω μ) (p : Ω × Ω) :
    (insertAbsent W).kernel p ≪ (sprinkle W editHalf).kernel p := by
  rw [sprinkle_kernel]
  exact (ac_positive_nnreal_smul _ _ editHalf_coeff_ne_zero).add_right _

/-- A single actually feasible kernel carries the old law and positive
mass on both the absent and charge-minus-three colors at every pair. -/
def editEnvelope (W : Model Ω μ) : Model Ω μ := sprinkle (thin W editHalf) editHalf

theorem feasible_editEnvelope [IsProbabilityMeasure μ] (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) :
    Feasible r (editEnvelope W) := feasible_sprinkle _ (feasible_thin W hW _) _

theorem old_absolutelyContinuous_editEnvelope (W : Model Ω μ) (p : Ω × Ω) :
    W.kernel p ≪ (editEnvelope W).kernel p :=
  (old_absolutelyContinuous_thin_half W p).trans (old_absolutelyContinuous_sprinkle_half _ p)

theorem absent_absolutelyContinuous_editEnvelope (W : Model Ω μ) (p : Ω × Ω) :
    Measure.dirac CappedColor.absent ≪ (editEnvelope W).kernel p :=
  (absent_absolutelyContinuous_thin_half W p).trans (old_absolutelyContinuous_sprinkle_half _ p)

theorem negativeThree_absolutelyContinuous_editEnvelope (W : Model Ω μ) (p : Ω × Ω) :
    Measure.dirac negativeThree ≪ (editEnvelope W).kernel p := by
  have h := (absent_absolutelyContinuous_thin_half W p).map measurable_insertColor
  have hleft : (Measure.dirac CappedColor.absent).map insertColor = Measure.dirac negativeThree := by
    rw [Measure.map_dirac' measurable_insertColor]
    simp [insertColor]
  rw [hleft] at h
  have hright : ((thin W editHalf).kernel p).map insertColor = (insertAbsent (thin W editHalf)).kernel p := by
    simp only [insertAbsent, DecoratedKernel.map, Kernel.map_apply _ measurable_insertColor]
  rw [hright] at h
  exact h.trans (inserted_absolutelyContinuous_sprinkle_half _ p)

theorem inserted_absolutelyContinuous_editEnvelope (W : Model Ω μ) (p : Ω × Ω) :
    (insertAbsent W).kernel p ≪ (editEnvelope W).kernel p := by
  have h := (old_absolutelyContinuous_thin_half W p).map measurable_insertColor
  have h' : (insertAbsent W).kernel p ≪ (insertAbsent (thin W editHalf)).kernel p := by
    simpa only [insertAbsent, DecoratedKernel.map, Kernel.map_apply _ measurable_insertColor] using h
  exact h'.trans (inserted_absolutelyContinuous_sprinkle_half _ p)

theorem thin_absolutelyContinuous_editEnvelope (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (thin W t).kernel p ≪ (editEnvelope W).kernel p := by
  rw [thin_kernel]
  exact ((absent_absolutelyContinuous_editEnvelope W p).smul_left _).add_left
    ((old_absolutelyContinuous_editEnvelope W p).smul_left _)

theorem sprinkle_absolutelyContinuous_editEnvelope (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (sprinkle W t).kernel p ≪ (editEnvelope W).kernel p := by
  rw [sprinkle_kernel]
  exact ((inserted_absolutelyContinuous_editEnvelope W p).smul_left _).add_left
    ((old_absolutelyContinuous_editEnvelope W p).smul_left _)

open scoped Classical in
theorem maskedThin_kernel (W : Model Ω μ) (t : unitInterval) (s : Set (Ω × Ω))
    (hs : MeasurableSet s) (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) (p : Ω × Ω) :
    (maskedThin W t s hs hsym).kernel p = if p ∈ s then (thin W t).kernel p else W.kernel p := by
  change (W.couple (bernoulliMeasure true false t)).editKernel (maskedCoinDelete s) p = _
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_maskedCoinDelete s hs)]
  simp only [DecoratedKernel.couple, Kernel.prod_apply, Kernel.const_apply]
  rw [map_prod_bernoulli (W.kernel p) (fun c => maskedCoinDelete s (p, c))
    ((measurable_maskedCoinDelete s hs).comp measurable_prodMk_left) t]
  by_cases hp : p ∈ s
  · simp [maskedCoinDelete, hp, thin_kernel]
  · simp [maskedCoinDelete, hp, ← add_smul]

theorem maskedThin_absolutelyContinuous_editEnvelope (W : Model Ω μ) (t : unitInterval)
    (s : Set (Ω × Ω)) (hs : MeasurableSet s)
    (hsym : ∀ᵐ p ∂μ.prod μ, p.swap ∈ s ↔ p ∈ s) (p : Ω × Ω) :
    (maskedThin W t s hs hsym).kernel p ≪ (editEnvelope W).kernel p := by
  classical
  rw [maskedThin_kernel]
  split_ifs
  · exact thin_absolutelyContinuous_editEnvelope W t p
  · exact old_absolutelyContinuous_editEnvelope W p

theorem supportInsert_absolutelyContinuous_editEnvelope (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (supportInsert W t).kernel p ≪ (editEnvelope W).kernel p :=
  (supportInsert_absolutelyContinuous W t p).trans (old_absolutelyContinuous_editEnvelope W p)

/-- Pairwise absolute continuity transfers all actually imposed finite
independent sampled tests. -/
theorem feasible_of_pair_absolutelyContinuous (W V : Model Ω μ) {r : ℕ}
    (hW : Feasible r W) (hVW : ∀ p, V.kernel p ≪ W.kernel p) : Feasible r V := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  exact (DecoratedKernel.pi_absolutelyContinuous_of_coordinates
    (fun p : CliquePair n => V.kernel (x p.val.1, x p.val.2))
    (fun p : CliquePair n => W.kernel (x p.val.1, x p.val.2))
    (fun p => hVW (x p.val.1, x p.val.2))).ae_le hx

end Erdos1017.CappedModel
