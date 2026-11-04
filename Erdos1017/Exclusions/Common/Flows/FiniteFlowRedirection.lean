module

public import Erdos1017.Exclusions.Common.Flows.FiniteMissingFlowEnergy

/-!
# Redirecting finitely many source columns

The flow `finiteRedirect` sends a prescribed fraction of each of finitely many
source columns to its assigned uniform recipient and keeps the rest
(`retainedFiniteSources`); its receipt, supply and support are computed, and the
full supply is preserved without disjointness of the recipient sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Retain the original flow after removing the specified fraction of
each of finitely many source columns. -/
def retainedFiniteSources {n : ℕ} (q : Ω × Ω → ℝ) (P : Fin n → Set Ω)
    (θ : Fin n → ℝ) (p : Ω × Ω) : ℝ :=
  q p - ∑ i, θ i * (Prod.snd ⁻¹' P i).indicator q p

/-- One actual flow redirects each source's own fraction to its assigned
uniform recipient and retains the remaining original source columns. -/
def finiteRedirect {n : ℕ} (μ : Measure Ω) (q : Ω × Ω → ℝ)
    (C P : Fin n → Set Ω) (θ : Fin n → ℝ) (p : Ω × Ω) : ℝ :=
  retainedFiniteSources q P θ p + ∑ i, uniformSubflow μ (C i) (P i) (θ i) p

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem retainedFiniteSources_of_mem {n : ℕ} (q : Ω × Ω → ℝ)
    (P : Fin n → Set Ω) (θ : Fin n → ℝ) (hdis : Pairwise (Disjoint on P))
    (p : Ω × Ω) (i : Fin n) (hi : p.2 ∈ P i) :
    retainedFiniteSources q P θ p = (1 - θ i) * q p := by
  have hsum : (∑ j, θ j * (Prod.snd ⁻¹' P j).indicator q p) = θ i * q p := by
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' P i from hi)]
    · intro j _ hji
      have hj : p.2 ∉ P j := fun hj => Set.disjoint_left.mp (hdis hji) hj hi
      simp only [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' P j from hj), mul_zero]
    · simp
  rw [retainedFiniteSources, hsum]
  ring

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem retainedFiniteSources_of_notMem {n : ℕ} (q : Ω × Ω → ℝ)
    (P : Fin n → Set Ω) (θ : Fin n → ℝ)
    (p : Ω × Ω) (hp : ∀ i, p.2 ∉ P i) : retainedFiniteSources q P θ p = q p := by
  have hout (i : Fin n) : p ∉ Prod.snd ⁻¹' P i := hp i
  simp only [retainedFiniteSources, indicator_of_notMem (hout _), mul_zero,
    Finset.sum_const_zero, sub_zero]

omit [IsProbabilityMeasure μ] in
theorem retainedFiniteSources_bounds {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (P : Fin n → Set Ω) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂μ.prod μ, retainedFiniteSources q P θ p ∈ Icc (0 : ℝ) (q p) := by
  filter_upwards [hq] with p hp
  by_cases hmem : ∃ i, p.2 ∈ P i
  · obtain ⟨i, hi⟩ := hmem
    rw [retainedFiniteSources_of_mem q P θ hdis p i hi]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hθ i).2) hp
    · nlinarith [(hθ i).1]
  · rw [retainedFiniteSources_of_notMem q P θ p (not_exists.mp hmem)]
    exact ⟨hp, le_rfl⟩

omit [IsProbabilityMeasure μ] in
theorem integrable_retainedFiniteSources {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (P : Fin n → Set Ω)
    (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ) :
    Integrable (retainedFiniteSources q P θ) (μ.prod μ) :=
  hq.sub (integrable_finsetSum _ (fun i _ =>
    (hq.indicator ((hP i).preimage measurable_snd)).const_mul (θ i)))

theorem integrable_finiteRedirect {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C P : Fin n → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ) :
    Integrable (finiteRedirect μ q C P θ) (μ.prod μ) :=
  (integrable_retainedFiniteSources q hq P hP θ).add
    (integrable_finsetSum _ (fun i _ => integrable_uniformSubflow _ _ (hC i) (hP i) (θ i)))

omit [IsProbabilityMeasure μ] in
theorem finiteRedirect_nonnegative {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C P : Fin n → Set Ω) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ finiteRedirect μ q C P θ p := by
  filter_upwards [retainedFiniteSources_bounds q hq P θ hdis hθ] with p hp
  exact add_nonneg hp.1 (Finset.sum_nonneg (fun i _ => uniformSubflow_nonnegative _ _ _ (hθ i).1 p))

omit [IsProbabilityMeasure μ] in
/-- The finite family of uniform replacements is dominated by the one
actual redirected flow because its retained original part is nonnegative. -/
theorem sum_uniformSubflow_le_finiteRedirect {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (C P : Fin n → Set Ω) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ p ∂μ.prod μ, (∑ i, uniformSubflow μ (C i) (P i) (θ i) p) ≤
      finiteRedirect μ q C P θ p := by
  filter_upwards [retainedFiniteSources_bounds q hq P θ hdis hθ] with p hp
  exact le_add_of_nonneg_left hp.1

/-- Actual retained receipt cannot exceed the old receipt, even when
neither receipt is bounded. -/
theorem receipt_retainedFiniteSources_le {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (P : Fin n → Set Ω) (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, receipt μ (retainedFiniteSources q P θ) x ≤ receipt μ q x := by
  filter_upwards [hq.prod_right_ae,
    (integrable_retainedFiniteSources q hq P hP θ).prod_right_ae,
    Measure.ae_ae_of_ae_prod (retainedFiniteSources_bounds q hq0 P θ hdis hθ)] with x hx hr hb
  exact integral_mono_ae hr hx (hb.mono (fun _ hp => hp.2))

omit [IsProbabilityMeasure μ] in
theorem receipt_uniformSubflow (C P : Set Ω) (hP : MeasurableSet P) (θ : ℝ) (x : Ω) :
    receipt μ (uniformSubflow μ C P θ) x =
      (θ * μ.real P) * C.indicator (fun _ => 1 / μ.real C) x := by
  unfold receipt uniformSubflow
  change (∫ y, (θ * C.indicator (fun _ => 1 / μ.real C) x) *
    P.indicator (fun _ => (1 : ℝ)) y ∂μ) = _
  rw [integral_const_mul, integral_indicator hP, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  ring

omit [IsProbabilityMeasure μ] in
theorem supply_uniformSubflow (C P : Set Ω) (hC : MeasurableSet C)
    (hpos : 0 < μ.real C) (θ : ℝ) (y : Ω) :
    supply μ (uniformSubflow μ C P θ) y = θ * P.indicator (fun _ => 1) y := by
  unfold supply uniformSubflow
  change (∫ x, (θ * C.indicator (fun _ => 1 / μ.real C) x) *
    P.indicator (fun _ => (1 : ℝ)) y ∂μ) = _
  rw [integral_mul_const, integral_const_mul, integral_indicator hC, setIntegral_const]
  simp only [smul_eq_mul]
  rw [mul_one_div, div_self hpos.ne', mul_one]

/-- Exact actual receipt decomposition retains all the old columns that
were not fully replaced. Atomic recipient sets are allowed to coincide. -/
theorem receipt_finiteRedirect {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C P : Fin n → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (hP : ∀ i, MeasurableSet (P i)) (θ : Fin n → ℝ) :
    ∀ᵐ x ∂μ, receipt μ (finiteRedirect μ q C P θ) x =
      receipt μ (retainedFiniteSources q P θ) x +
        ∑ i, (θ i * μ.real (P i)) * (C i).indicator (fun _ => 1 / μ.real (C i)) x := by
  have hu : ∀ᵐ x ∂μ, ∀ i, Integrable (fun y => uniformSubflow μ (C i) (P i) (θ i) (x, y)) μ :=
    ae_all_iff.mpr (fun i => (integrable_uniformSubflow _ _ (hC i) (hP i) (θ i)).prod_right_ae)
  filter_upwards [(integrable_retainedFiniteSources q hq P hP θ).prod_right_ae, hu] with x hr hu
  unfold receipt finiteRedirect
  rw [integral_add hr (integrable_finsetSum _ (fun i _ => hu i)),
    integral_finsetSum _ (fun i _ => hu i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact receipt_uniformSubflow (C i) (P i) (hP i) (θ i) x

/-- The actual sum decomposition gives the new supply from the retained
source column and the prescribed replacement fractions. -/
theorem supply_finiteRedirect {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C P : Fin n → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (hP : ∀ i, MeasurableSet (P i))
    (hpos : ∀ i, 0 < μ.real (C i)) (θ : Fin n → ℝ) :
    ∀ᵐ y ∂μ, supply μ (finiteRedirect μ q C P θ) y =
      supply μ (retainedFiniteSources q P θ) y +
        ∑ i, θ i * (P i).indicator (fun _ => 1) y := by
  have hu : ∀ᵐ y ∂μ, ∀ i, Integrable (fun x => uniformSubflow μ (C i) (P i) (θ i) (x, y)) μ :=
    ae_all_iff.mpr (fun i => (integrable_uniformSubflow _ _ (hC i) (hP i) (θ i)).prod_left_ae)
  filter_upwards [(integrable_retainedFiniteSources q hq P hP θ).prod_left_ae, hu] with y hr hu
  unfold supply finiteRedirect
  rw [integral_add hr (integrable_finsetSum _ (fun i _ => hu i)),
    integral_finsetSum _ (fun i _ => hu i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact supply_uniformSubflow (C i) (P i) (hC i) (hpos i) (θ i) y

omit [IsProbabilityMeasure μ] in
theorem supply_retainedFiniteSources_of_mem {n : ℕ} (q : Ω × Ω → ℝ)
    (P : Fin n → Set Ω) (θ : Fin n → ℝ) (hdis : Pairwise (Disjoint on P))
    (y : Ω) (i : Fin n) (hi : y ∈ P i) :
    supply μ (retainedFiniteSources q P θ) y = (1 - θ i) * supply μ q y := by
  unfold supply
  calc
    _ = ∫ x, (1 - θ i) * q (x, y) ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall (fun x => retainedFiniteSources_of_mem q P θ hdis (x, y) i hi))
    _ = _ := integral_const_mul _ _

omit [IsProbabilityMeasure μ] in
theorem supply_retainedFiniteSources_of_notMem {n : ℕ} (q : Ω × Ω → ℝ)
    (P : Fin n → Set Ω) (θ : Fin n → ℝ) (y : Ω) (hy : ∀ i, y ∉ P i) :
    supply μ (retainedFiniteSources q P θ) y = supply μ q y := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => retainedFiniteSources_of_notMem q P θ (x, y) hy)

/-- Replacing disjoint source fractions preserves the original full supply.
No disjointness of the recipient sets is required. -/
theorem supply_finiteRedirect_eq_indicator {n : ℕ} (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (C P : Fin n → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (hP : ∀ i, MeasurableSet (P i))
    (hpos : ∀ i, 0 < μ.real (C i)) (θ : Fin n → ℝ)
    (hdis : Pairwise (Disjoint on P)) (L : Set Ω)
    (hPL : ∀ i, ∀ᵐ y ∂μ, y ∈ P i → y ∈ L)
    (hsupply : ∀ᵐ y ∂μ, supply μ q y = L.indicator (fun _ => 1) y) :
    ∀ᵐ y ∂μ, supply μ (finiteRedirect μ q C P θ) y = L.indicator (fun _ => 1) y := by
  filter_upwards [supply_finiteRedirect q hq C P hC hP hpos θ,
    hsupply, ae_all_iff.mpr hPL] with y hy hq hPL
  rw [hy]
  by_cases hmem : ∃ i, y ∈ P i
  · obtain ⟨i, hi⟩ := hmem
    have hsum : (∑ j, θ j * (P j).indicator (fun _ => (1 : ℝ)) y) = θ i := by
      rw [Finset.sum_eq_single i]
      · simp only [indicator_of_mem hi, mul_one]
      · intro j _ hji
        have hj : y ∉ P j := fun hj => Set.disjoint_left.mp (hdis hji) hj hi
        simp only [indicator_of_notMem hj, mul_zero]
      · simp
    rw [supply_retainedFiniteSources_of_mem q P θ hdis y i hi, hq,
      indicator_of_mem (hPL i hi), hsum]
    ring
  · have hout : ∀ i, y ∉ P i := not_exists.mp hmem
    rw [supply_retainedFiniteSources_of_notMem q P θ y hout, hq]
    simp only [indicator_of_notMem (hout _), mul_zero, Finset.sum_const_zero, add_zero]

omit [IsProbabilityMeasure μ] in
/-- Actual support of the constructed flow follows from support of the old
flow and the finitely many genuine recipient-source rectangles. -/
theorem support_finiteRedirect {n : ℕ} (q : Ω × Ω → ℝ)
    (C P : Fin n → Set Ω) (θ : Fin n → ℝ) (R : Set (Ω × Ω))
    (hq : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → p ∈ R)
    (hCP : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ C i → p.2 ∈ P i → p ∈ R) :
    ∀ᵐ p ∂μ.prod μ, finiteRedirect μ q C P θ p ≠ 0 → p ∈ R := by
  filter_upwards [hq, ae_all_iff.mpr hCP] with p hp hCP hne
  by_contra hout
  have hqzero : q p = 0 := not_ne_iff.mp (fun hq => hout (hp hq))
  have hret : retainedFiniteSources q P θ p = 0 := by
    have hz (i : Fin n) : (Prod.snd ⁻¹' P i).indicator q p = 0 := by
      by_cases hi : p ∈ Prod.snd ⁻¹' P i
      · simp only [indicator_of_mem hi, hqzero]
      · exact indicator_of_notMem hi q
    simp only [retainedFiniteSources, hqzero, hz, mul_zero, Finset.sum_const_zero, sub_zero]
  have hu (i : Fin n) : uniformSubflow μ (C i) (P i) (θ i) p = 0 := by
    by_cases hx : p.1 ∈ C i
    · have hy : p.2 ∉ P i := fun hy => hout (hCP i hx hy)
      simp only [uniformSubflow, indicator_of_notMem hy, mul_zero]
    · simp only [uniformSubflow, indicator_of_notMem hx, mul_zero, zero_mul]
  exact hne (by simp only [finiteRedirect, hret, hu, Finset.sum_const_zero, add_zero])

end Erdos1017.MissingFlow
