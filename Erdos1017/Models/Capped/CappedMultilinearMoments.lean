module

public import Erdos1017.Models.Capped.CappedConditionalCharge
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Multilinear moments of the sampled clique polynomial

Each charge coordinate occurs to first degree in the clique color polynomial, so
its expectation depends only on the adjacency and charge moment at each pair,
and matching these moments transfers the capped clique tests to deterministic
present-charge laws (`ae_colorViolation_zero_of_moments`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def colorPolynomial (c : ι → CappedColor) : ℝ :=
  ((∑ i, CappedColor.charge (c i)) - 1) * ∏ i, CappedColor.adjacency (c i)

def colorViolation (c : ι → CappedColor) : ℝ :=
  max ((∑ i, CappedColor.charge (c i)) - 1) 0 * ∏ i, CappedColor.adjacency (c i)

open scoped Classical in
def mixedProduct (i : ι) (c : ι → CappedColor) : ℝ :=
  ∏ j, if j = i then CappedColor.charge (c j) else CappedColor.adjacency (c j)

omit [DecidableEq ι] in
theorem continuous_colorPolynomial : Continuous (colorPolynomial : (ι → CappedColor) → ℝ) := by
  unfold colorPolynomial
  fun_prop

omit [DecidableEq ι] in
theorem continuous_colorViolation : Continuous (colorViolation : (ι → CappedColor) → ℝ) := by
  unfold colorViolation
  fun_prop

theorem continuous_mixedProduct (i : ι) : Continuous (mixedProduct i : (ι → CappedColor) → ℝ) := by
  classical
  unfold mixedProduct
  apply continuous_finsetProd
  intro j _
  by_cases hji : j = i <;> simp only [hji, ↓reduceIte] <;> fun_prop

theorem charge_mul_adjacency (c : CappedColor) :
    CappedColor.charge c * CappedColor.adjacency c = CappedColor.charge c := by
  by_cases hc : CappedColor.adjacency c = 1
  · simp [hc]
  · rw [color_eq_absent_of_not_present c hc]
    simp

theorem prod_replace_one (a b : ι → ℝ) (i : ι) :
    (∏ j, if j = i then b j else a j) = b i * ∏ j ∈ Finset.univ.erase i, a j := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then b j else a j) (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

/-- Each charge coordinate occurs to first degree: its own adjacency
factor is absorbed by the exact absent/present color relation. -/
theorem colorPolynomial_eq (c : ι → CappedColor) :
    colorPolynomial c = (∑ i, mixedProduct i c) - ∏ i, CappedColor.adjacency (c i) := by
  classical
  unfold colorPolynomial
  rw [sub_mul, Finset.sum_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedProduct, prod_replace_one]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => CappedColor.adjacency (c j)) (Finset.mem_univ i)]
  rw [← mul_assoc, charge_mul_adjacency]

theorem integral_mixedProduct (ρ : ι → Measure CappedColor) [∀ i, IsProbabilityMeasure (ρ i)] (i : ι) :
    (∫ c, mixedProduct i c ∂Measure.pi ρ) =
      (∫ c, CappedColor.charge c ∂ρ i) *
        ∏ j ∈ Finset.univ.erase i, ∫ c, CappedColor.adjacency c ∂ρ j := by
  classical
  unfold mixedProduct
  rw [integral_fintype_prod_eq_prod (fun j (c : CappedColor) =>
    if j = i then CappedColor.charge c else CappedColor.adjacency c)]
  have hpoint (j : ι) : (∫ c, (if j = i then CappedColor.charge c else CappedColor.adjacency c) ∂ρ j) =
      if j = i then (∫ c, CappedColor.charge c ∂ρ j) else ∫ c, CappedColor.adjacency c ∂ρ j := by
    by_cases hji : j = i <;> simp [hji]
  simp_rw [hpoint]
  exact prod_replace_one _ _ i

/-- The actual expectation of the sampled clique polynomial depends only
on the adjacency and charge moment at each pair. -/
theorem integral_colorPolynomial (ρ : ι → Measure CappedColor) [∀ i, IsProbabilityMeasure (ρ i)] :
    (∫ c, colorPolynomial c ∂Measure.pi ρ) =
      (∑ i, (∫ c, CappedColor.charge c ∂ρ i) *
        ∏ j ∈ Finset.univ.erase i, ∫ c, CappedColor.adjacency c ∂ρ j) -
      ∏ i, ∫ c, CappedColor.adjacency c ∂ρ i := by
  classical
  have hm (i : ι) : Integrable (mixedProduct i) (Measure.pi ρ) :=
    (continuous_mixedProduct i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha : Integrable (fun c : ι → CappedColor => ∏ i, CappedColor.adjacency (c i)) (Measure.pi ρ) := by
    have hcont : Continuous (fun c : ι → CappedColor => ∏ i, CappedColor.adjacency (c i)) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [colorPolynomial_eq]
  rw [integral_sub (integrable_finsetSum Finset.univ (fun i _ => hm i)) ha,
    integral_finsetSum _ (fun i _ => hm i)]
  simp_rw [integral_mixedProduct]
  rw [integral_fintype_prod_eq_prod]

omit [DecidableEq ι] in
theorem colorPolynomial_le_violation (c : ι → CappedColor) : colorPolynomial c ≤ colorViolation c :=
  mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Finset.prod_nonneg (fun i _ => (CappedColor.adjacency_mem (c i)).1))

omit [DecidableEq ι] in
theorem integral_colorPolynomial_nonpos (ρ : ι → Measure CappedColor)
    [∀ i, IsProbabilityMeasure (ρ i)] (hρ : ∀ᵐ c ∂Measure.pi ρ, colorViolation c = 0) :
    (∫ c, colorPolynomial c ∂Measure.pi ρ) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [hρ] with c hc
  exact (colorPolynomial_le_violation c).trans_eq hc

omit [DecidableEq ι] in
/-- A law with deterministic present charge has one fixed clique sum
whenever all its sampled pairs are present. -/
theorem deterministic_color_expressions (c : ι → CappedColor) (z : ι → ℝ)
    (hc : ∀ i, CappedColor.charge (c i) = z i * CappedColor.adjacency (c i)) :
    colorPolynomial c = ((∑ i, z i) - 1) * ∏ i, CappedColor.adjacency (c i) ∧
      colorViolation c = max ((∑ i, z i) - 1) 0 * ∏ i, CappedColor.adjacency (c i) := by
  classical
  by_cases hz : ∃ i, CappedColor.adjacency (c i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hp : (∏ j, CappedColor.adjacency (c j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp only [colorPolynomial, colorViolation, hp, mul_zero, and_self]
  · have ha (i : ι) : CappedColor.adjacency (c i) = 1 :=
      (CappedColor.adjacency_eq_zero_or_one (c i)).resolve_left (fun hi => hz ⟨i, hi⟩)
    have hy (i : ι) : CappedColor.charge (c i) = z i := by rw [hc i, ha i, mul_one]
    simp only [colorPolynomial, colorViolation, hy, and_self]

/-- Matching only adjacency and charge moments suffices to transfer the
capped clique tests to deterministic present-charge laws. The proof uses
the multilinear polynomial expectation, without conditional Jensen. -/
theorem ae_colorViolation_zero_of_moments
    (ρ σ : ι → Measure CappedColor) [∀ i, IsProbabilityMeasure (ρ i)]
    [∀ i, IsProbabilityMeasure (σ i)]
    (hρ : ∀ᵐ c ∂Measure.pi ρ, colorViolation c = 0)
    (hA : ∀ i, (∫ c, CappedColor.adjacency c ∂σ i) = ∫ c, CappedColor.adjacency c ∂ρ i)
    (hY : ∀ i, (∫ c, CappedColor.charge c ∂σ i) = ∫ c, CappedColor.charge c ∂ρ i)
    (z : ι → ℝ) (hdet : ∀ i, ∀ᵐ c ∂σ i, CappedColor.charge c = z i * CappedColor.adjacency c) :
    ∀ᵐ c ∂Measure.pi σ, colorViolation c = 0 := by
  have hae : ∀ᵐ c ∂Measure.pi σ,
      ∀ i, CappedColor.charge (c i) = z i * CappedColor.adjacency (c i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval σ i).quasiMeasurePreserving.ae (hdet i)
  have hpoly : (∫ c, colorPolynomial c ∂Measure.pi σ) =
      ((∑ i, z i) - 1) * ∏ i, ∫ c, CappedColor.adjacency c ∂σ i := by
    calc
      _ = ∫ c, ((∑ i, z i) - 1) * ∏ i, CappedColor.adjacency (c i) ∂Measure.pi σ :=
        integral_congr_ae (hae.mono (fun c hc => (deterministic_color_expressions c z hc).1))
      _ = _ := by rw [integral_const_mul, integral_fintype_prod_eq_prod]
  have hviol : (∫ c, colorViolation c ∂Measure.pi σ) =
      max ((∑ i, z i) - 1) 0 * ∏ i, ∫ c, CappedColor.adjacency c ∂σ i := by
    calc
      _ = ∫ c, max ((∑ i, z i) - 1) 0 * ∏ i, CappedColor.adjacency (c i) ∂Measure.pi σ :=
        integral_congr_ae (hae.mono (fun c hc => (deterministic_color_expressions c z hc).2))
      _ = _ := by rw [integral_const_mul, integral_fintype_prod_eq_prod]
  have hnonpos : (∫ c, colorPolynomial c ∂Measure.pi σ) ≤ 0 := by
    rw [integral_colorPolynomial]
    simp_rw [hA, hY]
    rw [← integral_colorPolynomial]
    exact integral_colorPolynomial_nonpos ρ hρ
  rw [hpoly] at hnonpos
  have hprod : 0 ≤ ∏ i, ∫ c, CappedColor.adjacency c ∂σ i :=
    Finset.prod_nonneg (fun i _ => integral_nonneg (fun c => (CappedColor.adjacency_mem c).1))
  have hzero : (∫ c, colorViolation c ∂Measure.pi σ) = 0 := by
    rw [hviol]
    by_cases hz : (∑ i, z i) - 1 ≤ 0
    · simp [max_eq_right hz]
    · have hpzero : (∏ i, ∫ c, CappedColor.adjacency c ∂σ i) = 0 := by
        have hzpos : 0 < (∑ i, z i) - 1 := lt_of_not_ge hz
        nlinarith
      simp [hpzero]
  apply (integral_eq_zero_iff_of_nonneg (fun c =>
    mul_nonneg (le_max_right _ _) (Finset.prod_nonneg (fun i _ => (CappedColor.adjacency_mem (c i)).1)))
    (continuous_colorViolation.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp
  exact hzero

end Erdos1017.CappedModel
