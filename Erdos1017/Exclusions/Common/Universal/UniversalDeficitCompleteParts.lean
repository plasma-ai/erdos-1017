module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lower integral bound for complete-part deficits

Complete-part deficits have a lower bound on their integral, including the case
of countably many parts and dust.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.UniversalDeficit

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

/-- A product almost-everywhere exclusion cannot contain a positive rectangle. -/
private theorem null_side_of_ae_product_exclusion
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hexclude : ∀ᵐ p ∂ν.prod ν, p.1 ∈ A → p.2 ∈ B → False) :
    ν A = 0 ∨ ν B = 0 := by
  by_cases hApos : ν A = 0
  · exact Or.inl hApos
  by_cases hBpos : ν B = 0
  · exact Or.inr hBpos
  exfalso
  have hexclude' : ∀ᵐ p ∂ν.prod ν, p ∉ A ×ˢ B := by
    filter_upwards [hexclude] with p hp
    intro hpAB
    exact hp hpAB.1 hpAB.2
  have hsec := (Measure.ae_prod_iff_ae_ae
    (hA.prod hB).compl).1 hexclude'
  obtain ⟨x, hxA, hxsec⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hApos (ae_restrict_of_ae hsec)
  obtain ⟨y, hyB, hxy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hBpos (ae_restrict_of_ae hxsec)
  exact hxy ⟨hxA, hyB⟩

private theorem low_pair_null (label : Ω → ℕ) (f : Ω → ℝ)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : ∀ x ∈ A, f x < 1 / 2) (hb : ∀ x ∈ B, f x < 1 / 2)
    (hcross : ∀ x ∈ A, ∀ y ∈ B,
      label x = 0 ∨ label y = 0 ∨ label x ≠ label y)
    (hpair : ∀ᵐ p ∂ν.prod ν,
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        1 ≤ f p.1 + f p.2) : ν A = 0 ∨ ν B = 0 := by
  apply null_side_of_ae_product_exclusion A B hA hB
  filter_upwards [hpair] with p hp hx hy
  have h := hp (hcross p.1 hx p.2 hy)
  have h₁ := ha p.1 hx
  have h₂ := hb p.2 hy
  linarith

private theorem exists_positive_low_cell (label : Ω → ℕ) (hlabel : Measurable label)
    (f : Ω → ℝ) (hf : Measurable f)
    (hpair : ∀ᵐ p ∂ν.prod ν,
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        1 ≤ f p.1 + f p.2)
    (hlow : 0 < ν {x | f x < 1 / 2}) :
    ∃ i : ℕ, 0 < ν {x | f x < 1 / 2 ∧ label x = i + 1} := by
  let L : Set Ω := {x | f x < 1 / 2}
  let D : Set Ω := {x | label x = 0}
  have hLm : MeasurableSet L := measurableSet_lt hf measurable_const
  have hDm : MeasurableSet D := measurableSet_eq_fun hlabel measurable_const
  have hLD : ν (L ∩ D) = 0 := by
    have h := low_pair_null label f (L ∩ D) L (hLm.inter hDm) hLm
      (by intro x hx; exact hx.1) (by intro x hx; exact hx)
      (by intro x hx y hy; exact Or.inl hx.2) hpair
    exact h.resolve_right hlow.ne'
  have hpositive : ν (L ∩ Dᶜ) ≠ 0 := by
    intro hz
    have hcover : L ⊆ (L ∩ D) ∪ (L ∩ Dᶜ) := by
      intro x hx
      by_cases hd : x ∈ D
      · exact Or.inl ⟨hx, hd⟩
      · exact Or.inr ⟨hx, hd⟩
    exact hlow.ne' (measure_mono_null hcover (measure_union_null hLD hz))
  have hcover : L ∩ Dᶜ ⊆ ⋃ i : ℕ, {x | f x < 1 / 2 ∧ label x = i + 1} := by
    intro x hx
    have hne : label x ≠ 0 := hx.2
    cases hval : label x with
    | zero => exact False.elim (hne hval)
    | succ i =>
        exact Set.mem_iUnion.mpr ⟨i, hx.1, by simpa only [Nat.succ_eq_add_one] using hval⟩
  have hne : ν (⋃ i : ℕ, {x | f x < 1 / 2 ∧ label x = i + 1}) ≠ 0 := by
    intro hz
    exact hpositive (measure_mono_null hcover hz)
  exact exists_measure_pos_of_not_measure_iUnion_null hne

private theorem integral_ge_half_of_low_null (f : Ω → ℝ) (hf : Integrable f ν)
    (hlow : ν {x | f x < 1 / 2} = 0) :
    ν.real Set.univ / 2 ≤ ∫ x, f x ∂ν := by
  have hae : ∀ᵐ x ∂ν, 1 / 2 ≤ f x := by
    have hnot : ∀ᵐ x ∂ν, ¬ f x < 1 / 2 :=
      ae_iff.mpr (by simpa only [not_not] using hlow)
    filter_upwards [hnot] with x hx
    exact le_of_not_gt hx
  have hint := integral_mono_ae (integrable_const (1 / 2 : ℝ)) hf hae
  simpa [integral_const, smul_eq_mul, div_eq_mul_inv] using hint

private theorem integral_lower_of_positive_low_cell
    (label : Ω → ℕ) (hlabel : Measurable label)
    (f : Ω → ℝ) (hfInt : Integrable f ν)
    (hfn : ∀ᵐ x ∂ν, 0 ≤ f x) (i : ℕ)
    (hlow : 0 < ν {x | f x < 1 / 2 ∧ label x = i + 1})
    (C : ℝ) (hcellmass : ν.real {x | label x = i + 1} ≤ C)
    (hconst : ∃ t : ℝ, ∀ᵐ x ∂ν.restrict {x | label x = i + 1}, f x = t)
    (hpair : ∀ᵐ p ∂ν.prod ν,
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        1 ≤ f p.1 + f p.2) :
    min (ν.real Set.univ / 2) (ν.real Set.univ - C) ≤ ∫ x, f x ∂ν := by
  let cell : Set Ω := {x | label x = i + 1}
  let lowcell : Set Ω := {x | f x < 1 / 2 ∧ label x = i + 1}
  have hcell : MeasurableSet cell := measurableSet_eq_fun hlabel measurable_const
  obtain ⟨t, ht⟩ := hconst
  have htlow : ∀ᵐ x ∂ν.restrict lowcell, f x = t :=
    ae_restrict_of_ae_restrict_of_subset (by intro x hx; exact hx.2) ht
  have hpairsec := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxlow, ⟨hxt, hxpair⟩, hxnonneg⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hlow.ne'
      ((htlow.and (ae_restrict_of_ae hpairsec)).and (ae_restrict_of_ae hfn))
  have ht0 : 0 ≤ t := by rw [← hxt]; exact hxnonneg
  have ht2 : t < 1 / 2 := by rw [← hxt]; exact hxlow.1
  have hout : ∀ᵐ y ∂ν.restrict cellᶜ, 1 - t ≤ f y := by
    filter_upwards [ae_restrict_of_ae hxpair, ae_restrict_mem hcell.compl] with y hy hyc
    have hdiff : label x ≠ label y := by
      rw [hxlow.2]
      exact (show label y ≠ i + 1 from hyc).symm
    have h := hy (Or.inr (Or.inr hdiff))
    linarith
  have hbound : ∀ᵐ y ∂ν,
      (if y ∈ cell then t else 1 - t) ≤ f y := by
    apply ae_of_ae_restrict_of_ae_restrict_compl cell
    · filter_upwards [ht, ae_restrict_mem hcell] with y hy hyc
      simp [hyc, hy]
    · filter_upwards [hout, ae_restrict_mem hcell.compl] with y hy hyc
      simpa [show y ∉ cell from hyc] using hy
  have hpieceInt : Integrable (fun y => if y ∈ cell then t else 1 - t) ν :=
    Integrable.piecewise hcell.nullMeasurableSet (integrable_const t).integrableOn
      (integrable_const (1 - t)).integrableOn
  have hint := integral_mono_ae hpieceInt hfInt hbound
  have hmeasure : ν.real cellᶜ = ν.real Set.univ - ν.real cell := by
    rw [measureReal_compl hcell]
  have hpiece : (∫ y, if y ∈ cell then t else 1 - t ∂ν) =
      t * ν.real cell + (1 - t) * (ν.real Set.univ - ν.real cell) := by
    change (∫ y, cell.piecewise (fun _ => t) (fun _ => 1 - t) y ∂ν) = _
    rw [integral_piecewise hcell (integrable_const t).integrableOn
      (integrable_const (1 - t)).integrableOn]
    simp only [setIntegral_const, smul_eq_mul]
    rw [hmeasure]
    ring
  have ha0 : 0 ≤ ν.real cell := measureReal_nonneg
  have has : ν.real cell ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
  have halg : min (ν.real Set.univ / 2) (ν.real Set.univ - C) ≤
      t * ν.real cell + (1 - t) * (ν.real Set.univ - ν.real cell) := by
    by_cases hhalf : ν.real cell ≤ ν.real Set.univ / 2
    · apply le_trans (min_le_left _ _)
      nlinarith
    · apply le_trans (min_le_right _ _)
      nlinarith [hcellmass]
  linarith [hpiece]

/-- The complete-part deficit bound for countably many whole parts and genuine dust. -/
private theorem normalized_complete_part_deficit_lower
    (label : Ω → ℕ) (hlabel : Measurable label)
    (f : Ω → ℝ) (hf : Measurable f) (B : ℝ)
    (hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ B) (hfn : ∀ᵐ x ∂ν, 0 ≤ f x)
    (C : ℝ) (hcellmass : ∀ i : ℕ, ν.real {x | label x = i + 1} ≤ C)
    (hconst : ∀ i : ℕ, ∃ t : ℝ,
      ∀ᵐ x ∂ν.restrict {x | label x = i + 1}, f x = t)
    (hpair : ∀ᵐ p ∂ν.prod ν,
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        1 ≤ f p.1 + f p.2) :
    min (ν.real Set.univ / 2) (ν.real Set.univ - C) ≤ ∫ x, f x ∂ν := by
  have hfInt : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable B hbound
  by_cases hlow : ν {x | f x < 1 / 2} = 0
  · exact (min_le_left _ _).trans (integral_ge_half_of_low_null f hfInt hlow)
  · have hlowpos : 0 < ν {x | f x < 1 / 2} := (pos_iff_ne_zero).2 hlow
    obtain ⟨i, hi⟩ := exists_positive_low_cell label hlabel f hf hpair hlowpos
    exact integral_lower_of_positive_low_cell label hlabel f hfInt hfn i hi
      C (hcellmass i) (hconst i) hpair

/-- Complete-part deficits have a lower integral bound, including countably many parts and dust. -/
theorem complete_part_deficit_integral_lower
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Set Ω) (_hR : MeasurableSet R)
    (label : Ω → ℕ) (hlabel : Measurable label)
    (D : Ω → ℝ) (hD : Measurable D) (B : ℝ)
    (hDnonneg : ∀ᵐ x ∂μ.restrict R, 0 ≤ D x)
    (hDbound : ∀ᵐ x ∂μ.restrict R, D x ≤ B)
    (δ C : ℝ) (hδ : 0 < δ)
    (hcellmass : ∀ i : ℕ,
      (μ.restrict R).real {x | label x = i + 1} ≤ C)
    (hconst : ∀ i : ℕ, ∃ t : ℝ,
      ∀ᵐ x ∂(μ.restrict R).restrict {x | label x = i + 1}, D x = t)
    (hpair : ∀ᵐ p ∂(μ.restrict R).prod (μ.restrict R),
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        δ ≤ D p.1 + D p.2) :
    min (μ.real R / 2) (μ.real R - C) ≤
      (∫ x in R, D x ∂μ) / δ := by
  have hnormbound : ∀ᵐ x ∂μ.restrict R, ‖D x / δ‖ ≤ B / δ := by
    filter_upwards [hDnonneg, hDbound] with x hxnonneg hxbound
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hxnonneg, abs_of_pos hδ]
    exact (div_le_div_iff_of_pos_right hδ).2 hxbound
  have hpairnorm : ∀ᵐ p ∂(μ.restrict R).prod (μ.restrict R),
      (label p.1 = 0 ∨ label p.2 = 0 ∨ label p.1 ≠ label p.2) →
        1 ≤ D p.1 / δ + D p.2 / δ := by
    filter_upwards [hpair] with p hp hcross
    rw [← add_div]
    exact (le_div_iff₀ hδ).2 (by simpa using hp hcross)
  have hconstnorm (i : ℕ) : ∃ t : ℝ,
      ∀ᵐ x ∂(μ.restrict R).restrict {x | label x = i + 1}, D x / δ = t := by
    obtain ⟨t, ht⟩ := hconst i
    refine ⟨t / δ, ?_⟩
    filter_upwards [ht] with x hx
    rw [hx]
  have hmeasure : (μ.restrict R).real Set.univ = μ.real R := by
    exact measureReal_restrict_apply_univ R
  have h := normalized_complete_part_deficit_lower label hlabel
    (fun x => D x / δ) (hD.div_const δ) (B / δ) hnormbound
    (hDnonneg.mono (fun x hx => div_nonneg hx hδ.le)) C hcellmass hconstnorm hpairnorm
  rw [hmeasure, integral_div] at h
  exact h

end Erdos1017.UniversalDeficit
