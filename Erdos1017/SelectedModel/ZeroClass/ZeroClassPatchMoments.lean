module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassMeasurablePatch

/-!
# Moment changes under a class patch

The same-label and distinct-label pair masses inside a patched class give the
exact change of every continuous color moment, of the density and of the charge,
so matching the internal adjacency with the original multiplier charge law
preserves both global means on the same carrier.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The mass of vertices in the patched class carrying one finite label. -/
def patchLabelMass {k : ℕ} (s : Set Ω) (L : Ω → Fin k) (i : Fin k) : ℝ :=
  μ.real (s ∩ L ⁻¹' {i})

/-- The actual pair mass inside one class with equal finite labels. -/
theorem patch_same_label_mass {k : ℕ} (s : Set Ω) (hs : MeasurableSet s)
    (L : Ω → Fin k) (hL : Measurable L) :
    (μ.prod μ).real {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 = L p.2} =
      ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 := by
  classical
  let cell : Fin k → Set Ω := fun i => s ∩ L ⁻¹' {i}
  have hcell (i : Fin k) : MeasurableSet (cell i) :=
    hs.inter (hL (measurableSet_singleton i))
  have hset : {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 = L p.2} =
      ⋃ i : Fin k, (cell i) ×ˢ (cell i) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_inter_iff,
      mem_preimage, mem_singleton_iff, cell]
    constructor
    · rintro ⟨hp1, hp2, heq⟩
      exact ⟨L p.1, ⟨hp1, rfl⟩, ⟨hp2, heq.symm⟩⟩
    · rintro ⟨i, ⟨hp1, hi⟩, ⟨hp2, hj⟩⟩
      exact ⟨hp1, hp2, hi.trans hj.symm⟩
  have hd : Pairwise (fun i j : Fin k =>
      Disjoint ((cell i) ×ˢ (cell i)) ((cell j) ×ˢ (cell j))) := by
    intro i j hij
    rw [disjoint_left]
    intro p hi hj
    exact hij (hi.1.2.symm.trans hj.1.2)
  rw [hset, measureReal_iUnion_fintype hd (fun i => (hcell i).prod (hcell i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [measureReal_prod_prod]
  simp only [patchLabelMass, cell, pow_two]

/-- The actual pair mass inside one class with distinct finite labels. -/
theorem patch_distinct_label_mass {k : ℕ} (s : Set Ω) (hs : MeasurableSet s)
    (L : Ω → Fin k) (hL : Measurable L) :
    (μ.prod μ).real {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 ≠ L p.2} =
      (μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 := by
  let t : Set (Ω × Ω) := {p | L p.1 = L p.2}
  have ht : MeasurableSet t :=
    measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)
  have hsplit := measureReal_inter_add_sdiff (μ := μ.prod μ) (s := s ×ˢ s) ht
  have hsame : (s ×ˢ s) ∩ t =
      {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 = L p.2} := by
    ext p
    simp [t, and_assoc]
  have hdiff : (s ×ˢ s) \ t =
      {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 ≠ L p.2} := by
    ext p
    simp [t, and_assoc]
  rw [hsame, hdiff, patch_same_label_mass s hs L hL,
    measureReal_prod_prod] at hsplit
  nlinarith

/-- The patched deterministic internal color has the exact same-label
and distinct-label masses under the original pair law. -/
theorem integral_patch_internal_color {k : ℕ} (s : Set Ω)
    (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) (f : CappedColor → ℝ) :
    (∫ p in s ×ˢ s,
      f (if L p.1 = L p.2 then CappedColor.absent else CappedColor.present m hm)
        ∂μ.prod μ) =
      f CappedColor.absent * (∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) +
        f (CappedColor.present m hm) *
          ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) := by
  classical
  let t : Set (Ω × Ω) := {p | L p.1 = L p.2}
  have ht : MeasurableSet t :=
    measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)
  have hsame : ((μ.prod μ).restrict (s ×ˢ s)).real t =
      ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 := by
    rw [measureReal_restrict_apply ht]
    have heq : t ∩ (s ×ˢ s) =
        {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 = L p.2} := by
      ext p
      simp [t, and_comm, and_left_comm]
    rw [heq, patch_same_label_mass s hs L hL]
  have hdiff : ((μ.prod μ).restrict (s ×ˢ s)).real tᶜ =
      (μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 := by
    rw [measureReal_restrict_apply ht.compl]
    have heq : tᶜ ∩ (s ×ˢ s) =
        {p : Ω × Ω | p.1 ∈ s ∧ p.2 ∈ s ∧ L p.1 ≠ L p.2} := by
      ext p
      simp [t, and_comm, and_left_comm]
    rw [heq, patch_distinct_label_mass s hs L hL]
  calc
    (∫ p in s ×ˢ s,
      f (if L p.1 = L p.2 then CappedColor.absent else CappedColor.present m hm)
        ∂μ.prod μ) =
        ∫ p, t.piecewise (fun _ => f CappedColor.absent)
          (fun _ => f (CappedColor.present m hm)) p
          ∂(μ.prod μ).restrict (s ×ˢ s) := by
            apply integral_congr_ae
            filter_upwards with p
            by_cases h : L p.1 = L p.2 <;> simp [Set.piecewise, t, h]
    _ = _ := by
      rw [integral_piecewise ht
        (integrable_const (f CappedColor.absent)).integrableOn
        (integrable_const (f (CappedColor.present m hm))).integrableOn]
      simp only [setIntegral_const, smul_eq_mul, hsame, hdiff]
      ring

/-- Every continuous global color moment changes by the exact internal
same-label and distinct-label masses of the measurable patch. -/
theorem integral_moment_patchZeroClass {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) (f : C(CappedColor, ℝ)) :
    (∫ p, (patchZeroClass W s hs m hm L hL).moment f p ∂μ.prod μ) =
      (∫ p, W.moment f p ∂μ.prod μ) +
        f CappedColor.absent * (∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) +
        f (CappedColor.present m hm) *
          ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) -
        ∫ p in s ×ˢ s, W.moment f p ∂μ.prod μ := by
  classical
  let g : Ω × Ω → ℝ := W.moment f
  let internal : Ω × Ω → ℝ := fun p =>
    f (if L p.1 = L p.2 then CappedColor.absent else CappedColor.present m hm)
  have hlabel : MeasurableSet {p : Ω × Ω | L p.1 = L p.2} :=
    measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)
  have hism : StronglyMeasurable internal := by
    have hc : Measurable (fun p : Ω × Ω =>
        if L p.1 = L p.2 then CappedColor.absent else CappedColor.present m hm) :=
      measurable_const.ite hlabel measurable_const
    exact (f.continuous.measurable.comp hc).stronglyMeasurable
  have hibound (p : Ω × Ω) : ‖internal p‖ ≤ ‖f‖ := f.norm_coe_le_norm _
  have hii : Integrable internal (μ.prod μ) :=
    Integrable.of_bound hism.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall hibound)
  have hgsm : StronglyMeasurable g :=
    W.stronglyMeasurable_moment f.continuous.stronglyMeasurable
  have hgbound (p : Ω × Ω) : ‖g p‖ ≤ ‖f‖ := by
    change ‖∫ c, f c ∂W.kernel p‖ ≤ ‖f‖
    have h := norm_integral_le_of_norm_le_const
      (μ := W.kernel p)
      (Filter.Eventually.of_forall fun c => f.norm_coe_le_norm c)
    simpa using h
  have hgi : Integrable g (μ.prod μ) :=
    Integrable.of_bound hgsm.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall hgbound)
  have hadd := integral_add_compl (hs.prod hs) hgi
  calc
    (∫ p, (patchZeroClass W s hs m hm L hL).moment f p ∂μ.prod μ) =
        ∫ p, (s ×ˢ s).piecewise internal g p ∂μ.prod μ := by
          apply integral_congr_ae
          filter_upwards with p
          rw [patchZeroClass_moment]
          rfl
    _ = (∫ p in s ×ˢ s, internal p ∂μ.prod μ) +
        ∫ p in (s ×ˢ s)ᶜ, g p ∂μ.prod μ :=
      integral_piecewise (hs.prod hs) hii.integrableOn hgi.integrableOn
    _ = _ := by
      rw [integral_patch_internal_color s hs m hm L hL f]
      change _ = (∫ p, g p ∂μ.prod μ) + _ + _ - ∫ p in s ×ˢ s, g p ∂μ.prod μ
      linarith

/-- Global adjacency density changes by the new distinct-label pair
mass minus the actual old internal adjacency integral, divided by two. -/
theorem density_patchZeroClass {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) :
    density (patchZeroClass W s hs m hm L hL) = density W +
      ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) / 2 -
        (∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ) / 2 := by
  have h := integral_moment_patchZeroClass W s hs m hm L hL
    ⟨CappedColor.adjacency, CappedColor.continuous_adjacency⟩
  change (∫ p, (patchZeroClass W s hs m hm L hL).moment CappedColor.adjacency p
      ∂μ.prod μ) =
    (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) +
      0 * (∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) +
      1 * ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) -
      ∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ at h
  unfold density
  rw [h]
  ring

/-- Global charge changes by multiplier times the new distinct-label
pair mass minus the actual old internal charge integral, divided by two. -/
theorem objective_patchZeroClass {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L) :
    objective (patchZeroClass W s hs m hm L hL) = objective W +
      m * ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) / 2 -
        (∫ p in s ×ˢ s, W.moment CappedColor.charge p ∂μ.prod μ) / 2 := by
  have h := integral_moment_patchZeroClass W s hs m hm L hL
    ⟨CappedColor.charge, CappedColor.continuous_charge⟩
  change (∫ p, (patchZeroClass W s hs m hm L hL).moment CappedColor.charge p
      ∂μ.prod μ) =
    (∫ p, W.moment CappedColor.charge p ∂μ.prod μ) +
      0 * (∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) +
      m * ((μ.real s) ^ 2 - ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2) -
      ∫ p in s ×ˢ s, W.moment CappedColor.charge p ∂μ.prod μ at h
  unfold objective
  rw [h]
  ring

/-- Exact internal adjacency matching and the actual old multiplier
charge law preserve both global means on the same carrier. -/
theorem density_objective_patchZeroClass_eq {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L)
    (hmatch : (μ.real s) ^ 2 -
      ∑ i, (patchLabelMass (μ := μ) s L i) ^ 2 =
        ∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ)
    (hcharge : ∀ᵐ p ∂(μ.prod μ).restrict (s ×ˢ s),
      W.moment CappedColor.charge p = m * W.moment CappedColor.adjacency p) :
    density (patchZeroClass W s hs m hm L hL) = density W ∧
      objective (patchZeroClass W s hs m hm L hL) = objective W := by
  have hchargeIntegral : (∫ p in s ×ˢ s, W.moment CappedColor.charge p ∂μ.prod μ) =
      m * ∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae hcharge
  constructor
  · rw [density_patchZeroClass, hmatch]
    ring
  · rw [objective_patchZeroClass, hchargeIntegral, hmatch]
    ring

end Erdos1017.CappedModel
