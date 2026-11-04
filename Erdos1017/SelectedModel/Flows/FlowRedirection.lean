module

public import Erdos1017.SelectedModel.Flows.FlowClassMasses
public import Erdos1017.SelectedModel.Flows.ClassifiedRelationFlow

/-!
# Redirecting sources into one recipient set

`redirect` replaces every source in a region by uniform receipt in a
positive-mass recipient set, keeping integrability, nonnegativity, unit supply,
pair support and avoided atoms, and the recipient's endpoint mass becomes its
original mass plus the replaced source-region mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Replace every source in the displayed region by uniform receipt in the
actual positive-mass recipient set, retaining every other source column. -/
def redirect (μ : Measure Ω) (q : Ω × Ω → ℝ) (I N : Set Ω) (p : Ω × Ω) : ℝ :=
  if p.2 ∈ N then I.indicator (fun _ => 1 / μ.real I) p.1 else q p

/-- The explicit redirected density is integrable on the original product law. -/
theorem integrable_redirect (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N) :
    Integrable (redirect μ q I N) (μ.prod μ) := by
  let A : Set (Ω × Ω) := Prod.snd ⁻¹' N
  have hA : MeasurableSet A := hN.preimage measurable_snd
  have hi : Integrable (fun p : Ω × Ω => I.indicator (fun _ => 1 / μ.real I) p.1)
      (μ.prod μ) := ((integrable_const _).indicator hI).comp_fst μ
  have heq : redirect μ q I N = A.indicator
      (fun p : Ω × Ω => I.indicator (fun _ => 1 / μ.real I) p.1) + Aᶜ.indicator q := by
    funext p
    by_cases hp : p.2 ∈ N <;> simp [redirect, A, hp]
  rw [heq]
  exact (hi.indicator hA).add (hq.indicator hA.compl)

omit [IsProbabilityMeasure μ] in
/-- Redirection preserves nonnegativity without bounding the old receipt. -/
theorem redirect_nonnegative (q : Ω × Ω → ℝ)
    (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (I N : Set Ω) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ redirect μ q I N p := by
  filter_upwards [hq] with p hp
  by_cases hy : p.2 ∈ N
  · simp only [redirect, ite_eq_left hy]
    exact indicator_nonneg (fun _ _ => div_nonneg zero_le_one ENNReal.toReal_nonneg) _
  · simpa only [redirect, ite_eq_right hy] using hp

omit [IsProbabilityMeasure μ] in
/-- Every redirected column has exactly unit supply; other columns retain
all their original spatial supply. -/
theorem supply_redirect (q : Ω × Ω → ℝ) (I N : Set Ω)
    (hI : MeasurableSet I) (hpos : 0 < μ.real I) (y : Ω) :
    supply μ (redirect μ q I N) y = if y ∈ N then 1 else supply μ q y := by
  unfold supply
  by_cases hy : y ∈ N
  · simp only [redirect, hy, ↓reduceIte]
    rw [integral_indicator hI, setIntegral_const, smul_eq_mul]
    exact mul_div_cancel₀ _ hpos.ne'
  · simp only [redirect, hy, ↓reduceIte]

omit [IsProbabilityMeasure μ] in
/-- Full supply on LOW is preserved when the replaced sources lie in LOW
almost everywhere. No partial-supply resampling assumption is made. -/
theorem full_supply_redirect (q : Ω × Ω → ℝ) (I N L : Set Ω)
    (hI : MeasurableSet I) (hpos : 0 < μ.real I)
    (hq : supply μ q =ᵐ[μ] L.indicator (fun _ => 1))
    (hNL : ∀ᵐ y ∂μ, y ∈ N → y ∈ L) :
    supply μ (redirect μ q I N) =ᵐ[μ] L.indicator (fun _ => 1) := by
  filter_upwards [hq, hNL] with y hy hNy
  rw [supply_redirect q I N hI hpos]
  by_cases hn : y ∈ N
  · rw [ite_eq_left hn, indicator_of_mem (hNy hn)]
  · rw [ite_eq_right hn, hy]

omit [IsProbabilityMeasure μ] in
/-- Actual pair support is retained when the replacement rectangle lies
in the same relation almost everywhere. -/
theorem support_redirect (q : Ω × Ω → ℝ) (I N : Set Ω) (R : Set (Ω × Ω))
    (hq : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → p ∈ R)
    (hrect : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ N → p ∈ R) :
    ∀ᵐ p ∂μ.prod μ, redirect μ q I N p ≠ 0 → p ∈ R := by
  filter_upwards [hq, hrect] with p hp hr hne
  by_cases hn : p.2 ∈ N
  · have hi : p.1 ∈ I := by
      by_contra hi
      exact hne (by simp only [redirect, ite_eq_left hn, indicator_of_notMem hi])
    exact hr hi hn
  · exact hp (by simpa only [redirect, ite_eq_right hn] using hne)

omit [IsProbabilityMeasure μ] in
/-- A disjoint recipient cannot receive redirected mass if it received no
old mass. This keeps an actually avoided original atom avoided. -/
theorem avoids_redirect (q : Ω × Ω → ℝ) (I N I₀ : Set Ω) (hdis : Disjoint I I₀)
    (hq : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → p.1 ∉ I₀) :
    ∀ᵐ p ∂μ.prod μ, redirect μ q I N p ≠ 0 → p.1 ∉ I₀ := by
  apply support_redirect q I N {p | p.1 ∉ I₀} hq
  exact Eventually.of_forall (fun p hi _ => Set.disjoint_left.mp hdis hi)

/-- If the recipient's old receipt used only the replaced source region,
its new receipt density is exactly the uniform full-region mass. -/
theorem receipt_redirect_on_recipient (q : Ω × Ω → ℝ) (I N : Set Ω)
    (hN : MeasurableSet N)
    (hold : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → q p ≠ 0 → p.2 ∈ N) :
    ∀ᵐ x ∂μ, x ∈ I → receipt μ (redirect μ q I N) x = μ.real N / μ.real I := by
  filter_upwards [Measure.ae_ae_of_ae_prod hold] with x hx hIx
  unfold receipt
  have heq : (fun y => redirect μ q I N (x, y)) =ᵐ[μ]
      N.indicator (fun _ => 1 / μ.real I) := by
    filter_upwards [hx] with y hy
    by_cases hn : y ∈ N
    · simp only [redirect, ite_eq_left hn, indicator_of_mem hIx, indicator_of_mem hn]
    · have hz : q (x, y) = 0 := by
        by_contra hne
        exact hn (hy hIx hne)
      simp only [redirect, ite_eq_right hn, indicator_of_notMem hn, hz]
  rw [integral_congr_ae heq, integral_indicator hN, setIntegral_const, smul_eq_mul]
  ring

/-- The actual recipient receives exactly the mass of the replaced source
region, not a supplied closed-missing-mass certificate. -/
theorem integral_receipt_redirect (q : Ω × Ω → ℝ) (I N : Set Ω)
    (hI : MeasurableSet I) (hN : MeasurableSet N) (hpos : 0 < μ.real I)
    (hold : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → q p ≠ 0 → p.2 ∈ N) :
    (∫ x in I, receipt μ (redirect μ q I N) x ∂μ) = μ.real N := by
  rw [setIntegral_congr_ae hI (receipt_redirect_on_recipient q I N hN hold),
    setIntegral_const, smul_eq_mul, mul_div_cancel₀ _ hpos.ne']

/-- With full LOW supply and a disjoint HIGH recipient, the actual endpoint
mass is its original mass plus the entire replaced source-region mass. -/
theorem endpoint_redirect_recipient_mass (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (I N H L : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (hpos : 0 < μ.real I) (hdis : Disjoint H L)
    (hIH : ∀ᵐ x ∂μ, x ∈ I → x ∈ H) (hNL : ∀ᵐ x ∂μ, x ∈ N → x ∈ L)
    (hsupply : supply μ q =ᵐ[μ] L.indicator (fun _ => 1))
    (hold : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → q p ≠ 0 → p.2 ∈ N) :
    (CappedModel.missingFlowEndpointLaw μ (redirect μ q I N)).real I = μ.real I + μ.real N := by
  have hs := full_supply_redirect q I N L hI hpos hsupply hNL
  have hle : ∀ᵐ x ∂μ, supply μ (redirect μ q I N) x ≤ 1 := by
    filter_upwards [hs] with x hx
    rw [hx]
    by_cases hxL : x ∈ L <;> simp [hxL]
  have hzero : ∀ᵐ x ∂μ, x ∈ I → supply μ (redirect μ q I N) x = 0 := by
    filter_upwards [hs, hIH] with x hx hi hIx
    have hn : x ∉ L := fun hl => Set.disjoint_left.mp hdis (hi hIx) hl
    rw [hx, indicator_of_notMem hn]
  rw [endpoint_real_set_eq_add_receipt _ (integrable_redirect q hq I N hI hN)
    (redirect_nonnegative q hq0 I N) hle I hI hzero,
    integral_receipt_redirect q I N hI hN hpos hold]

end Erdos1017.MissingFlow
