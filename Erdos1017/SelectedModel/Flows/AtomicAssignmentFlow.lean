module

public import Erdos1017.SelectedModel.Flows.MissingFlowDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Product flow from assigned source fractions

Assigned source fractions define a nonnegative product flow density that
resamples uniformly inside each recipient atom; it supplies the sum of its
fractions, gives each disjoint atom exactly its assigned receipt, and with
supply at most one has an `L1` mean-zero direction with nonnegative endpoint
weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace Erdos1017.MissingFlow.AtomicAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Uniform resampling inside one original recipient atom. -/
def recipientDensity (μ : Measure Ω) (I : Set Ω) : Ω → ℝ :=
  I.indicator (fun _ => (μ.real I)⁻¹)

/-- The actual product density obtained from the assigned source fractions. -/
def density (μ : Measure Ω) (I : ℕ → Set Ω) (f : ℕ → Ω → ℝ) : Ω × Ω → ℝ :=
  fun p => ∑' i, recipientDensity μ (I i) p.1 * f i p.2

omit [IsFiniteMeasure μ] in
private theorem recipient_nonneg (I : Set Ω) (x : Ω) :
    0 ≤ recipientDensity μ I x :=
  indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) x

private theorem recipient_integrable (I : Set Ω) (hI : MeasurableSet I) :
    Integrable (recipientDensity μ I) μ :=
  (integrable_const _).indicator hI

private theorem recipient_integral (I : Set Ω) (hI : MeasurableSet I) :
    (∫ x, recipientDensity μ I x ∂μ) = if μ I = 0 then 0 else 1 := by
  rw [recipientDensity, integral_indicator hI, setIntegral_const]
  change μ.real I * (μ.real I)⁻¹ = _
  by_cases hzero : μ I = 0
  · simp [hzero, measureReal_def]
  · rw [ite_eq_right hzero]
    exact mul_inv_cancel₀ (ne_of_gt (ENNReal.toReal_pos hzero (measure_ne_top μ I)))

private theorem integrable_tsum_and_summable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (F : ℕ → X → ℝ) (hF : ∀ i, Integrable (F i) ν)
    (hsum : Summable (fun i => ∫ x, ‖F i x‖ ∂ν)) :
    Integrable (fun x => ∑' i, F i x) ν ∧
      ∀ᵐ x ∂ν, Summable (fun i => F i x) := by
  let L : ℕ → Lp ℝ 1 ν := fun i => (hF i).toL1 (F i)
  have hnorm : Summable (fun i => ‖L i‖) := by
    convert hsum using 1
    funext i
    exact (Integrable.norm_toL1_eq_lintegral_enorm (F i) (hF i)).trans
      (integral_norm_eq_lintegral_enorm (hF i).aestronglyMeasurable).symm
  have henorm : ∑' i, ‖L i‖ₑ ≠ ∞ := tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hpoint : ∀ᵐ x ∂ν, ∀ i, L i x = F i x :=
    ae_all_iff.mpr (fun i => (hF i).coeFn_toL1)
  have hhas : ∀ᵐ x ∂ν, HasSum (fun i => F i x) ((∑' i, L i) x) := by
    filter_upwards [Lp.hasSum_coeFn_tsum henorm, hpoint] with x hx hFx
    have heq : (fun i => L i x) = (fun i => F i x) := funext hFx
    rwa [heq] at hx
  exact ⟨(L1.integrable_coeFn (∑' i, L i)).congr
    (hhas.mono (fun _ hx => hx.tsum_eq.symm)), hhas.mono (fun _ hx => hx.summable)⟩

omit [IsFiniteMeasure μ] in
private theorem summable_integral_norm (f : ℕ → Ω → ℝ)
    (hf : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x) (hsum : Summable (fun i => ∫ x, f i x ∂μ)) :
    Summable (fun i => ∫ x, ‖f i x‖ ∂μ) := by
  convert hsum using 1
  funext i
  exact integral_congr_ae ((hf i).mono (fun _ hx => Real.norm_of_nonneg hx))

private theorem term_integrable (I : Set Ω) (hI : MeasurableSet I)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    Integrable (fun p : Ω × Ω => recipientDensity μ I p.1 * f p.2) (μ.prod μ) :=
  (recipient_integrable I hI).mul_prod hf

private theorem term_integral_norm (I : Set Ω) (hI : MeasurableSet I)
    (f : Ω → ℝ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (hzero : μ I = 0 → f =ᵐ[μ] 0) :
    (∫ p : Ω × Ω, ‖recipientDensity μ I p.1 * f p.2‖ ∂μ.prod μ) = ∫ x, f x ∂μ := by
  have heq : (fun p : Ω × Ω => ‖recipientDensity μ I p.1 * f p.2‖) =ᵐ[μ.prod μ]
      (fun p => recipientDensity μ I p.1 * f p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hf] with p hp
    exact Real.norm_of_nonneg (mul_nonneg (recipient_nonneg I p.1) hp)
  rw [integral_congr_ae heq, integral_prod_mul, recipient_integral I hI]
  by_cases hz : μ I = 0
  · rw [ite_eq_left hz, zero_mul, integral_congr_ae (hzero hz)]
    simp
  · rw [ite_eq_right hz, one_mul]

/-- Summable nonnegative assigned receipts define a genuine product L1 density.
Zero-mass inactive labels contribute no source fraction. -/
theorem integrable_density (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hf0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x)
    (hzero : ∀ i, μ (I i) = 0 → f i =ᵐ[μ] 0)
    (hsum : Summable (fun i => ∫ x, f i x ∂μ)) :
    Integrable (density μ I f) (μ.prod μ) := by
  apply (integrable_tsum_and_summable
    (fun i (p : Ω × Ω) => recipientDensity μ (I i) p.1 * f i p.2)
    (fun i => term_integrable (I i) (hI i) (f i) (hf i)) ?_).1
  convert hsum using 1
  funext i
  exact term_integral_norm (I i) (hI i) (f i) (hf0 i) (hzero i)

/-- The actual assignment density is nonnegative almost everywhere. -/
theorem nonnegative_density (I : ℕ → Set Ω) (f : ℕ → Ω → ℝ)
    (hf0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ density μ I f p := by
  have hsource : ∀ᵐ x ∂μ, ∀ i, 0 ≤ f i x := ae_all_iff.mpr hf0
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsource] with p hp
  exact tsum_nonneg (fun i => mul_nonneg (recipient_nonneg (I i) p.1) (hp i))

private theorem column_integral (I : Set Ω) (hI : MeasurableSet I) (z : ℝ)
    (hzero : μ I = 0 → z = 0) :
    (∫ x, recipientDensity μ I x * z ∂μ) = z := by
  rw [integral_mul_const, recipient_integral I hI]
  by_cases hz : μ I = 0
  · simp only [ite_eq_left hz, zero_mul, hzero hz]
  · rw [ite_eq_right hz, one_mul]

/-- The constructed flow supplies exactly the sum of its actual assigned
fractions, with genuine almost-everywhere series convergence. -/
theorem hasSum_supply (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hf0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x)
    (hzero : ∀ i, μ (I i) = 0 → f i =ᵐ[μ] 0)
    (hsum : Summable (fun i => ∫ x, f i x ∂μ)) :
    ∀ᵐ y ∂μ, HasSum (fun i => f i y) (supply μ (density μ I f) y) := by
  have hsource := (integrable_tsum_and_summable f hf
    (summable_integral_norm f hf0 hsum)).2
  have hnonneg : ∀ᵐ y ∂μ, ∀ i, 0 ≤ f i y := ae_all_iff.mpr hf0
  have hinactive : ∀ᵐ y ∂μ, ∀ i, μ (I i) = 0 → f i y = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : μ (I i) = 0
    · exact (hzero i hi).mono (fun _ hx _ => hx)
    · exact Eventually.of_forall (fun _ hx => (hi hx).elim)
  filter_upwards [hsource, hnonneg, hinactive] with y hy hfy hzy
  have hint (i : ℕ) : Integrable (fun x => recipientDensity μ (I i) x * f i y) μ :=
    (recipient_integrable (I i) (hI i)).mul_const _
  have hnorm (i : ℕ) :
      (∫ x, ‖recipientDensity μ (I i) x * f i y‖ ∂μ) = f i y := by
    rw [integral_congr_ae (Eventually.of_forall (fun x =>
      Real.norm_of_nonneg (mul_nonneg (recipient_nonneg (I i) x) (hfy i))))]
    exact column_integral (I i) (hI i) (f i y) (hzy i)
  have hnormSum : Summable
      (fun i => ∫ x, ‖recipientDensity μ (I i) x * f i y‖ ∂μ) :=
    hy.congr (fun i => (hnorm i).symm)
  have hhas := hasSum_integral_of_summable_integral_norm hint hnormSum
  have heq : (fun i => ∫ x, recipientDensity μ (I i) x * f i y ∂μ) =
      (fun i => f i y) := funext (fun i => column_integral (I i) (hI i) (f i y) (hzy i))
  rw [heq] at hhas
  exact hhas

/-- Total product-flow mass is the same sum of assigned original receipts. -/
theorem integral_density (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hf0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x)
    (hzero : ∀ i, μ (I i) = 0 → f i =ᵐ[μ] 0)
    (hsum : Summable (fun i => ∫ x, f i x ∂μ)) :
    (∫ p, density μ I f p ∂μ.prod μ) = ∑' i, ∫ x, f i x ∂μ := by
  have hq := integrable_density I hI f hf hf0 hzero hsum
  rw [← (integral_marginals hq).2,
    integral_congr_ae ((hasSum_supply I hI f hf hf0 hzero hsum).mono
      (fun _ hx => hx.tsum_eq.symm))]
  exact (hasSum_integral_of_summable_integral_norm hf
    (summable_integral_norm f hf0 hsum)).tsum_eq.symm

omit [IsFiniteMeasure μ] in
/-- Disjoint original atoms receive their own fraction uniformly, pointwise
on each atom, even if the countable series has exceptional source points. -/
theorem receipt_on_atom (I : ℕ → Set Ω) (f : ℕ → Ω → ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j)))
    (i : ℕ) (x : Ω) (hx : x ∈ I i) :
    receipt μ (density μ I f) x = (∫ y, f i y ∂μ) / μ.real (I i) := by
  have hrow (y : Ω) : density μ I f (x, y) = (μ.real (I i))⁻¹ * f i y := by
    have hterm (j : ℕ) (hji : j ≠ i) : recipientDensity μ (I j) x * f j y = 0 := by
      have hxj : x ∉ I j := fun hxj => Set.disjoint_left.mp (hdisjoint hji) hxj hx
      simp only [recipientDensity, indicator_of_notMem hxj, zero_mul]
    rw [density, tsum_eq_single i hterm]
    simp only [recipientDensity, indicator_of_mem hx]
  change (∫ y, density μ I f (x, y) ∂μ) = _
  simp_rw [hrow]
  rw [integral_const_mul, div_eq_mul_inv, mul_comm]

/-- Integrating over an original atom recovers exactly its assigned receipt,
including zero-mass inactive labels. -/
theorem receipt_mass (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) (i : ℕ)
    (hzero : μ (I i) = 0 → f i =ᵐ[μ] 0) :
    (∫ x in I i, receipt μ (density μ I f) x ∂μ) = ∫ y, f i y ∂μ := by
  rw [setIntegral_congr_fun (hI i) (fun x hx => receipt_on_atom I f hdisjoint i x hx),
    setIntegral_const]
  change μ.real (I i) * ((∫ y, f i y ∂μ) / μ.real (I i)) = _
  by_cases hz : μ (I i) = 0
  · rw [integral_congr_ae (hzero hz)]
    simp
  · have hmass : μ.real (I i) ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos hz (measure_ne_top μ (I i)))
    field_simp

/-- An original recipient atom retains its old mass and gains precisely its
assigned receipt when the actual source fractions vanish on that atom. -/
theorem endpoint_mass_on_atom (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hf : ∀ j, Integrable (f j) μ)
    (hf0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ f j x)
    (hzero : ∀ j, μ (I j) = 0 → f j =ᵐ[μ] 0)
    (hsum : Summable (fun j => ∫ x, f j x ∂μ))
    (hdisjoint : Pairwise (fun j k => Disjoint (I j) (I k))) (i : ℕ)
    (hsource : ∀ j, ∀ᵐ x ∂μ, x ∈ I i → f j x = 0) :
    (∫ x in I i, (1 + direction μ (density μ I f) x) ∂μ) =
      μ.real (I i) + ∫ x, f i x ∂μ := by
  have hq := integrable_density I hI f hf hf0 hzero hsum
  have hreceipt := (integrable_marginals hq).1
  have hsup : ∀ᵐ x ∂μ, x ∈ I i → supply μ (density μ I f) x = 0 := by
    filter_upwards [hasSum_supply I hI f hf hf0 hzero hsum, ae_all_iff.mpr hsource]
      with x hx hs hxi
    rw [← hx.tsum_eq]
    simp only [fun j => hs j hxi, tsum_zero]
  have heq : (fun x => 1 + direction μ (density μ I f) x) =ᵐ[μ.restrict (I i)]
      (fun x => 1 + receipt μ (density μ I f) x) := by
    apply (ae_restrict_iff' (hI i)).mpr
    filter_upwards [hsup] with x hx hxi
    simp only [direction, hx hxi, sub_zero]
  calc
    _ = ∫ x in I i, (1 + receipt μ (density μ I f) x) ∂μ := integral_congr_ae heq
    _ = μ.real (I i) + ∫ x in I i, receipt μ (density μ I f) x ∂μ := by
      rw [integral_add (integrable_const 1) hreceipt.integrableOn, setIntegral_const]
      simp
    _ = _ := by rw [receipt_mass I hI f hdisjoint i (hzero i)]

/-- Support is derived from the actual source fractions and licensed original
recipient/source rectangles, with one countable common null exception. -/
theorem supported_density (I E : ℕ → Set Ω) (f : ℕ → Ω → ℝ) (Z : Set (Ω × Ω))
    (hf : ∀ i, ∀ᵐ y ∂μ, y ∉ E i → f i y = 0)
    (hrect : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ I i → p.2 ∈ E i → p ∈ Z) :
    ∀ᵐ p ∂μ.prod μ, p ∉ Z → density μ I f p = 0 := by
  have hsource : ∀ᵐ y ∂μ, ∀ i, y ∉ E i → f i y = 0 := ae_all_iff.mpr hf
  have hrects : ∀ᵐ p ∂μ.prod μ, ∀ i, p.1 ∈ I i → p.2 ∈ E i → p ∈ Z :=
    ae_all_iff.mpr hrect
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsource, hrects] with p hp hr hZ
  have heq (i : ℕ) : recipientDensity μ (I i) p.1 * f i p.2 = 0 := by
    by_cases hx : p.1 ∈ I i
    · by_cases hy : p.2 ∈ E i
      · exact (hZ (hr i hx hy)).elim
      · rw [hp i hy, mul_zero]
    · simp only [recipientDensity, indicator_of_notMem hx, zero_mul]
  simp only [density, heq, tsum_zero]

/-- A constructed assignment with supply at most one has a genuine L1,
mean-zero direction and a nonnegative endpoint weight. -/
theorem direction_properties (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hf0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ f i x)
    (hzero : ∀ i, μ (I i) = 0 → f i =ᵐ[μ] 0)
    (hsum : Summable (fun i => ∫ x, f i x ∂μ))
    (hsupply : ∀ᵐ x ∂μ, (∑' i, f i x) ≤ 1) :
    Integrable (direction μ (density μ I f)) μ ∧
      (∫ x, direction μ (density μ I f) x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ direction μ (density μ I f) x := by
  have hq := integrable_density I hI f hf hf0 hzero hsum
  refine ⟨integrable_direction hq, integral_direction hq, ?_⟩
  apply direction_ge_neg_one (nonnegative_density I f hf0)
  filter_upwards [hasSum_supply I hI f hf hf0 hzero hsum, hsupply] with x hx hs
  rwa [← hx.tsum_eq]

end Erdos1017.MissingFlow.AtomicAssignment
