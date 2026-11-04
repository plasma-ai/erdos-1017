module

public import Erdos1017.Exclusions.Common.BoundedKernelSupportBound
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Support credit from rescaling an independent head

Rescaling one independent head to any nonnegative mass keeps all scalar clique
tests and pays the support bound on that law, and optimizing over the head mass
gives the positive-part square support credit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.FiniteCappedSamplingCost

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_rescaled_pair (I R : Set Ω) (t : ℝ≥0∞) (ht : t ≠ ⊤)
    (f : Ω × Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ p, ‖f p‖ ≤ B) :
    (∫ p, f p ∂(t • μ.restrict I + μ.restrict R).prod
      (t • μ.restrict I + μ.restrict R)) =
      t.toReal ^ 2 * (∫ p, f p ∂(μ.restrict I).prod (μ.restrict I)) +
        t.toReal * (∫ p, f p ∂(μ.restrict I).prod (μ.restrict R)) +
        t.toReal * (∫ p, f p ∂(μ.restrict R).prod (μ.restrict I)) +
        ∫ p, f p ∂(μ.restrict R).prod (μ.restrict R) := by
  let : IsFiniteMeasure (t • μ.restrict I) := (μ.restrict I).smul_finite ht
  have hi (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, smul_eq_mul]
  ring

private theorem restricted_pair_mass (I R : Set Ω) :
    ((μ.restrict I).prod (μ.restrict R)).real univ = μ.real I * μ.real R := by
  rw [← Set.univ_prod_univ, measureReal_prod_prod,
    measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]

/-- Rescaling one actual independent head to any nonnegative mass keeps
all original scalar clique tests and pays the support bound on that law. -/
theorem independent_head_support_at_mass
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (I R : Set Ω) (_hI : MeasurableSet I) (_hR : MeasurableSet R)
    (hIpos : 0 < μ I) (_hdisjoint : Disjoint I R)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), A p.1 p.2 = false)
    (hjoin : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict R), A p.1 p.2 = true)
    (z : ℝ) (hz : 0 ≤ z) :
    let r := μ.real R
    let HI := (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) / μ.real I
    let Q := ∫ p, (1 - if A p.1 p.2 = true then (1 : ℝ) else 0)
      ∂(μ.restrict R).prod (μ.restrict R)
    physicalObjective (μ.restrict R) Y ≤
      25 * z ^ 2 / 48 + (r / 24 - HI) * z + r ^ 2 / 48 + Q / 2 := by
  let a := μ.real I
  let r := μ.real R
  let HI := (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) / a
  let Q := ∫ p, (1 - if A p.1 p.2 = true then (1 : ℝ) else 0)
    ∂(μ.restrict R).prod (μ.restrict R)
  let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
  let F : Ω × Ω → ℝ := fun p => Y p.1 p.2 + G p
  have ha : 0 < a := ENNReal.toReal_pos hIpos.ne' (measure_ne_top μ I)
  have hG : Measurable G :=
    (measurable_of_countable (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp hA
  have hGb (p : Ω × Ω) : ‖G p‖ ≤ 1 := by dsimp [G]; split_ifs <;> norm_num
  have hF : Measurable F := hY.add hG
  have hFb (p : Ω × Ω) : ‖F p‖ ≤ B + 1 :=
    (norm_add_le _ _).trans (add_le_add (hB p) (hGb p))
  have hiY (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] :
      Integrable (fun p => Y p.1 p.2) ν :=
    Integrable.of_bound hY.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hiG (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable G ν :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (Filter.Eventually.of_forall hGb)
  have hFsym : ∀ᵐ p ∂μ.prod μ, F p = F p.swap := by
    filter_upwards [hYsym] with p hp
    dsimp [F, G]
    rw [hp, hsym p.1 p.2]
  have hII : (∫ p, F p ∂(μ.restrict I).prod (μ.restrict I)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hind, ae_mono (Measure.prod_mono Measure.restrict_le_self
      Measure.restrict_le_self) hzero] with p hp hz
    simp only [F, G, hp, Bool.false_eq_true, ite_false, hz hp, add_zero, Pi.zero_apply]
  have hIR : (∫ p, F p ∂(μ.restrict I).prod (μ.restrict R)) =
      (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) + a * r := by
    rw [integral_add (hiY _) (hiG _)]
    have he : (∫ p, G p ∂(μ.restrict I).prod (μ.restrict R)) = a * r := by
      have heq : G =ᵐ[(μ.restrict I).prod (μ.restrict R)] fun _ => 1 :=
        hjoin.mono (fun p hp => by simp only [G, hp, ite_true])
      rw [integral_congr_ae heq, integral_const, restricted_pair_mass,
        smul_eq_mul, mul_one]
    rw [he]
  have hRI : (∫ p, F p ∂(μ.restrict R).prod (μ.restrict I)) =
      ∫ p, F p ∂(μ.restrict I).prod (μ.restrict R) := by
    calc
      _ = ∫ p, F p.swap ∂(μ.restrict R).prod (μ.restrict I) :=
        integral_congr_ae (ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hFsym)
      _ = _ := integral_prod_swap F
  have hRR : (∫ p, F p ∂(μ.restrict R).prod (μ.restrict R)) =
      2 * physicalObjective (μ.restrict R) Y + r ^ 2 - Q := by
    have hQ : Q = r ^ 2 - ∫ p, G p ∂(μ.restrict R).prod (μ.restrict R) := by
      dsimp only [Q]
      rw [integral_sub (integrable_const 1) (hiG _), integral_const,
        restricted_pair_mass, smul_eq_mul, mul_one]
      change r * r - _ = r ^ 2 - _
      ring
    rw [integral_add (hiY _) (hiG _)]
    unfold physicalObjective
    linarith
  let t := ENNReal.ofReal (z / a)
  let ν := t • μ.restrict I + μ.restrict R
  have ht : t ≠ ⊤ := ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (t • μ.restrict I) := (μ.restrict I).smul_finite ht
  have htval : t.toReal = z / a := ENNReal.toReal_ofReal (div_nonneg hz ha.le)
  have hac : ν ≪ μ := Measure.AbsolutelyContinuous.add_left
    (Measure.absolutelyContinuous_restrict.smul_left t) Measure.absolutelyContinuous_restrict
  have hfullν : ∀ n, FiniteArity.FeasibleOrder ν A Y n :=
    fun n => (DecoratedKernel.pi_absolutelyContinuous hac n).ae_le (hfull n)
  have hsupport := physicalObjective_add_density_le_mass_sq (μ := ν)
    A hsym hA Y hY B hB ((hac.prod hac).ae_le hYsym) ((hac.prod hac).ae_le hzero) hfullν
  have hmass : ν.real univ = z + r := by
    dsimp only [ν]
    rw [measureReal_add_apply]
    simp only [measureReal_def, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, ENNReal.toReal_mul, htval]
    change z / a * a + r = z + r
    rw [div_mul_cancel₀ z ha.ne']
  have hsum := integral_rescaled_pair (μ := μ) I R t ht F hF (B + 1) hFb
  rw [htval, hII, hRI, hIR, hRR] at hsum
  have hcross : z / a *
      ((∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) + a * r) =
      z * HI + z * r := by
    dsimp only [HI]
    field_simp [ha.ne']
  rw [hcross] at hsum
  have hsumν : (∫ p, F p ∂ν.prod ν) =
      2 * physicalObjective ν Y + 2 * physicalDensity ν A := by
    rw [integral_add (hiY _) (hiG _)]
    unfold physicalObjective physicalDensity
    dsimp only [G]
    ring
  rw [hmass] at hsupport
  change (∫ p, F p ∂ν.prod ν) = _ at hsum
  rw [hsumν] at hsum
  change physicalObjective (μ.restrict R) Y ≤
    25 * z ^ 2 / 48 + (r / 24 - HI) * z + r ^ 2 / 48 + Q / 2
  nlinarith

/-- Optimizing the actual independent-head rescaling over nonnegative
head mass gives the positive-part square support credit. -/
theorem independent_head_support_optimized
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : ∀ p : Ω × Ω, ‖Y p.1 p.2‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (I R : Set Ω) (hI : MeasurableSet I) (hR : MeasurableSet R)
    (hIpos : 0 < μ I) (hdisjoint : Disjoint I R)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), A p.1 p.2 = false)
    (hjoin : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict R), A p.1 p.2 = true) :
    let r := μ.real R
    let HI := (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) / μ.real I
    let Q := ∫ p, (1 - if A p.1 p.2 = true then (1 : ℝ) else 0)
      ∂(μ.restrict R).prod (μ.restrict R)
    physicalObjective (μ.restrict R) Y ≤
      r ^ 2 / 48 + Q / 2 - (12 / 25) * (max (HI - r / 24) 0) ^ 2 := by
  let r := μ.real R
  let HI := (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod (μ.restrict R)) / μ.real I
  let Q := ∫ p, (1 - if A p.1 p.2 = true then (1 : ℝ) else 0)
    ∂(μ.restrict R).prod (μ.restrict R)
  let t := max (HI - r / 24) 0
  have ht : 0 ≤ t := le_max_right _ _
  have h := independent_head_support_at_mass A hsym hA Y hY B hB hYsym hzero hfull
    I R hI hR hIpos hdisjoint hind hjoin ((24 / 25) * t) (mul_nonneg (by norm_num) ht)
  change physicalObjective (μ.restrict R) Y ≤
    25 * ((24 / 25) * t) ^ 2 / 48 + (r / 24 - HI) * ((24 / 25) * t) +
      r ^ 2 / 48 + Q / 2 at h
  change physicalObjective (μ.restrict R) Y ≤ r ^ 2 / 48 + Q / 2 - (12 / 25) * t ^ 2
  by_cases hpos : 0 ≤ HI - r / 24
  · have he : t = HI - r / 24 := max_eq_left hpos
    rw [he] at h ⊢
    nlinarith
  · have he : t = 0 := max_eq_right (le_of_not_ge hpos)
    rw [he] at h ⊢
    nlinarith

end Erdos1017.FiniteCappedSamplingCost
