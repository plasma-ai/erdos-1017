module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassPrefixFacts
public import Erdos1017.SelectedModel.ZeroClass.CountableZeroClassEncoding
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatchMoments
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatchStructure
public import Erdos1017.SelectedModel.DecoratedKernelExtensionality

/-!
# Feasibility of every prefix of the zero-class edit

The empty prefix is the original decorated model, an absent label adds no edit,
and by induction every finite prefix of the countable zero-class edit is fully
feasible and preserves both original means, each successor being licensed by an
original positive class.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The empty positive-class prefix is the actual original decorated model. -/
theorem prefixClassEdit_zero_eq (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) : prefixClassEdit W t ht m hm 0 = W := by
  apply DecoratedKernel.ext_kernel
  intro p
  rw [prefixClassEdit_kernel_ite]
  apply ite_eq_right
  omega

omit [IsProbabilityMeasure μ] in
/-- An absent positive label contributes no new edit to the actual prefix. -/
theorem prefixClassEdit_succ_eq_of_missing_label
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N : ℕ)
    (hmissing : ∀ x, (t x).1 ≠ N + 1) :
    prefixClassEdit W t ht m hm (N + 1) = prefixClassEdit W t ht m hm N := by
  apply DecoratedKernel.ext_kernel
  intro p
  rw [prefixClassEdit_kernel_ite, prefixClassEdit_kernel_ite]
  have hiff : (0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N + 1) ↔
      (0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N) := by
    have hp := hmissing p.1
    omega
  simp only [hiff]

/-- Every finite prefix of the actual countable zero-class edit is fully
feasible and preserves both original means. Each successor is licensed by
an actual old positive clique and its fixed exact internal matching identity. -/
theorem prefixClassEdit_fullFeasible_means
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [BorelSpace H]
    [OpensMeasurableSpace H] [SecondCountableTopology H]
    (W : Model Ω μ) (hW : FullFeasible W) (F : Ω → H) (hF : Measurable F)
    (ν m : ℝ) (hν : 0 ≤ ν) (hm : m ∈ Icc (-3 : ℝ) 1)
    (v : ι → H) (hv : ∀ i, ‖v i‖ = Real.sqrt ν)
    (hpos : ∀ i, 0 < μ {x | F x = v i}) (k : ι → ℕ)
    (hclique : ∀ i, 0 < restrictedCliquePresence W {x | F x = v i} (k i))
    (L : ∀ i, Ω → Fin (k i)) (hL : ∀ i, Measurable (L i))
    (hmatch : ∀ i, (μ.real {x | F x = v i}) ^ 2 -
      ∑ j, (patchLabelMass (μ := μ) {x | F x = v i} (L i) j) ^ 2 =
        ∫ p in {x | F x = v i} ×ˢ {x | F x = v i},
          W.moment CappedColor.adjacency p ∂μ.prod μ)
    (e : ι ↪ ℕ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (htag : ∀ i x, F x = v i → t x = (e i + 1, (L i x).val))
    (houtside : ∀ x, (∀ i, F x ≠ v i) → t x = (0, 0))
    (hclassZero : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ N, FullFeasible (prefixClassEdit W t ht m hm N) ∧
      density (prefixClassEdit W t ht m hm N) = density W ∧
      objective (prefixClassEdit W t ht m hm N) = objective W := by
  classical
  intro N
  induction N with
  | zero =>
      rw [prefixClassEdit_zero_eq]
      exact ⟨hW, rfl, rfl⟩
  | succ N ih =>
      by_cases hcode : ∃ i, e i = N
      · obtain ⟨i, hi⟩ := hcode
        let V := prefixClassEdit W t ht m hm N
        have hclass : {x : Ω | (t x).1 = N + 1} = {x | F x = v i} := by
          ext x
          change (t x).1 = N + 1 ↔ F x = v i
          simpa only [hi, mem_ofPred_eq] using countableClassLabels_encoding_index_eq_iff
            (fun j => {x | F x = v j}) L e t htag houtside i x
        have hgeometry := prefixClassEdit_preserves_shifted_geometry W t ht F ν m hm
          hclassZero hrep hzero hnonneg N
        have hcliqueV : 0 < restrictedCliquePresence V {x | F x = v i} (k i) := by
          have heq := restrictedCliquePresence_prefixClassEdit_eq_of_unreached
            W t ht m hm N (N + 1) (Nat.lt_succ_self N) (k i)
          rw [hclass] at heq
          exact heq.symm ▸ hclique i
        have hinternal : (∫ p in {x | F x = v i} ×ˢ {x | F x = v i},
            V.moment CappedColor.adjacency p ∂μ.prod μ) =
            ∫ p in {x | F x = v i} ×ˢ {x | F x = v i},
              W.moment CappedColor.adjacency p ∂μ.prod μ := by
          have heq := integral_moment_prefixClassEdit_eq_of_unreached
            W t ht m hm N (N + 1) (Nat.lt_succ_self N) CappedColor.adjacency
          simpa only [hclass] using heq
        have hmatchV := (hmatch i).trans hinternal.symm
        have hs : MeasurableSet {x | F x = v i} := hF (measurableSet_singleton (v i))
        have hzeroClass := ae_shiftedMoment_zero_on_featureFiber V F (v i) ν m hν (hv i) hgeometry.1
        have hcharge : ∀ᵐ p ∂(μ.prod μ).restrict ({x | F x = v i} ×ˢ {x | F x = v i}),
            V.moment CappedColor.charge p = m * V.moment CappedColor.adjacency p := by
          filter_upwards [ae_restrict_mem (hs.prod hs), ae_restrict_of_ae hzeroClass] with p hp hz
          have hM := hz hp
          rw [shiftedMoment_eq] at hM
          linarith
        have hfull := fullFeasible_patchZeroClass_of_positive_clique V ih.1 F hF (v i) ν m
          hν (hv i) (hpos i) hcliqueV hm (L i) (hL i) hgeometry.1 hgeometry.2.1 hgeometry.2.2
          (prefixClassEdit_complementary W t ht m hm hcomp N)
          (prefixClassEdit_shifted_deterministic W t ht m hm hdet N)
        have hmean := density_objective_patchZeroClass_eq V {x | F x = v i} hs m hm
          (L i) (hL i) hmatchV hcharge
        have hpart : ∀ x : Ω, (t x).1 = N + 1 → (L i x).val = (t x).2 := by
          intro x hx
          have hFx : F x = v i := by
            change x ∈ {x | F x = v i}
            rw [← hclass]
            exact hx
          exact (congrArg Prod.snd (htag i x hFx)).symm
        have hstep : prefixClassEdit W t ht m hm (N + 1) =
            patchZeroClass V {x | F x = v i} hs m hm (L i) (hL i) := by
          apply DecoratedKernel.ext_kernel
          intro p
          have heq := prefixClassEdit_succ_kernel_eq_patchZeroClass W t ht m hm N (L i) (hL i) hpart p
          simpa only [hclass] using heq
        rw [hstep]
        exact ⟨hfull, hmean.1.trans ih.2.1, hmean.2.trans ih.2.2⟩
      · have hmissing : ∀ x, (t x).1 ≠ N + 1 := by
          intro x hx
          by_cases hex : ∃ i, F x = v i
          · obtain ⟨i, hFx⟩ := hex
            have htagx := htag i x hFx
            have hei : e i = N := by
              have hfirst := congrArg Prod.fst htagx
              omega
            exact hcode ⟨i, hei⟩
          · have hnot : ∀ i, F x ≠ v i := by
              intro i hi
              exact hex ⟨i, hi⟩
            rw [houtside x hnot] at hx
            omega
        rw [prefixClassEdit_succ_eq_of_missing_label W t ht m hm N hmissing]
        exact ih

end Erdos1017.CappedModel
