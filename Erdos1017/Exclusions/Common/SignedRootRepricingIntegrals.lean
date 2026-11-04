module

public import Erdos1017.Exclusions.Common.SignedRootRepricing
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison

/-!
# Integral gain of signed root repricing

This module computes the exact signed gain of the physical objective from
repricing a root row against its original neighbor square, assuming only a
bounded charge, and shows that at a full scalar optimum a feasible signed root
edit has no positive integral gain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.SignedRootRepricing

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The real indicator of a physical graph edge. -/
def edgeWeight (G : Ω → Ω → Bool) (x y : Ω) : ℝ :=
  if G x y = true then 1 else 0

private theorem measurable_edgeWeight (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) :
    Measurable (Function.uncurry (edgeWeight G)) := by
  exact Measurable.ite (hG (measurableSet_singleton true)) measurable_const measurable_const

private theorem integrable_h (h : Ω → ℝ) (hh : Measurable h) (H : ℝ)
    (hhbound : ∀ x, ‖h x‖ ≤ H) : Integrable h μ :=
  Integrable.of_bound hh.aestronglyMeasurable H (Eventually.of_forall hhbound)

private theorem integrable_root (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G))
    (I : Set Ω) (hI : MeasurableSet I) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) :
    Integrable (fun p : Ω × Ω =>
      edgeWeight G p.1 p.2 * (if p.1 ∈ I then h p.2 else 0)) (μ.prod μ) := by
  classical
  have hm : Measurable (fun p : Ω × Ω =>
      edgeWeight G p.1 p.2 * (if p.1 ∈ I then h p.2 else 0)) :=
    (measurable_edgeWeight G hG).mul
      (Measurable.ite (hI.preimage measurable_fst) (hh.comp measurable_snd) measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable H
  refine Eventually.of_forall (fun p => ?_)
  by_cases hp : p.1 ∈ I <;> by_cases he : G p.1 p.2 = true
  · simpa [edgeWeight, hp, he] using hhbound p.2
  · simp [edgeWeight, hp, he, hH]
  · simp [hp, hH]
  · simp [hp, hH]

private theorem integral_root (G : Ω → Ω → Bool)
    (I N : Set Ω) (hI : MeasurableSet I) (h : Ω → ℝ)
    (hsupport : ∀ x ∉ N, h x = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p.1 p.2 = true ↔ p.2 ∈ N)) :
    (∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
      (if p.1 ∈ I then h p.2 else 0) ∂μ.prod μ) = μ.real I * ∫ x, h x ∂μ := by
  classical
  have heq : (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ I then h p.2 else 0)) =ᵐ[μ.prod μ]
      (fun p => (if p.1 ∈ I then (1 : ℝ) else 0) * h p.2) := by
    filter_upwards [hrow] with p hp
    by_cases hi : p.1 ∈ I
    · by_cases hn : p.2 ∈ N
      · simp [edgeWeight, hi, (hp hi).mpr hn]
      · simp [edgeWeight, hi, hsupport p.2 hn]
    · simp [hi]
  rw [integral_congr_ae heq]
  calc
    _ = (∫ x, if x ∈ I then (1 : ℝ) else 0 ∂μ) * ∫ x, h x ∂μ := by
      simpa using (integral_prod_mul (μ := μ) (ν := μ)
        (fun x : Ω => if x ∈ I then (1 : ℝ) else 0) h)
    _ = _ := by
      change (∫ x, I.indicator (fun _ => (1 : ℝ)) x ∂μ) * _ = _
      rw [integral_indicator hI, setIntegral_const]
      simp

private theorem integrable_penalty (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) :
    Integrable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0)) (μ.prod μ) := by
  classical
  have hm : Measurable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0)) :=
    (measurable_edgeWeight G hG).mul
      (Measurable.ite ((hN.preimage measurable_fst).inter (hN.preimage measurable_snd))
        ((hh.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable (2 * H)
  refine Eventually.of_forall (fun p => ?_)
  by_cases hn : p.1 ∈ N ∧ p.2 ∈ N
  · by_cases he : G p.1 p.2 = true
    · simpa [edgeWeight, hn, he] using
        (norm_add_le (h p.1) (h p.2)).trans (by linarith [hhbound p.1, hhbound p.2])
    · simp [edgeWeight, hn, he, hH]
  · simp [hn, hH]

private theorem integrable_penalty_left (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) :
    Integrable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 else 0)) (μ.prod μ) := by
  classical
  have hm : Measurable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 else 0)) :=
    (measurable_edgeWeight G hG).mul
      (Measurable.ite ((hN.preimage measurable_fst).inter (hN.preimage measurable_snd))
        (hh.comp measurable_fst) measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable H
  refine Eventually.of_forall (fun p => ?_)
  by_cases hn : p.1 ∈ N ∧ p.2 ∈ N <;> by_cases he : G p.1 p.2 = true
  · simpa [edgeWeight, hn, he] using hhbound p.1
  · simp [edgeWeight, hn, he, hH]
  · simp [hn, hH]
  · simp [hn, hH]

private theorem integral_penalty_left (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) (hsupport : ∀ x ∉ N, h x = 0) :
    (∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 else 0) ∂μ.prod μ) =
      ∫ x, h x * (∫ y in N, edgeWeight G x y ∂μ) ∂μ := by
  classical
  rw [integral_prod _ (integrable_penalty_left G hG N hN h hh H hH hhbound)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (∫ y, edgeWeight G x y *
      (if x ∈ N ∧ y ∈ N then h x else 0) ∂μ) =
      h x * (∫ y in N, edgeWeight G x y ∂μ)
    by_cases hx : x ∈ N
    · have heq : (fun y => edgeWeight G x y *
          (if x ∈ N ∧ y ∈ N then h x else 0)) =
          (fun y => h x * N.indicator (edgeWeight G x) y) := by
        funext y
        by_cases hy : y ∈ N <;> simp [hx, hy, Set.indicator, mul_comm]
      rw [heq, integral_const_mul, integral_indicator hN]
    · simp [hx, hsupport x hx])

private theorem integral_root_right (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (I N : Set Ω) (hI : MeasurableSet I) (h : Ω → ℝ)
    (hsupport : ∀ x ∉ N, h x = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p.1 p.2 = true ↔ p.2 ∈ N)) :
    (∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
      (if p.2 ∈ I then h p.1 else 0) ∂μ.prod μ) = μ.real I * ∫ x, h x ∂μ := by
  classical
  calc
    _ = ∫ p : Ω × Ω, (fun q : Ω × Ω => edgeWeight G q.1 q.2 *
        (if q.1 ∈ I then h q.2 else 0)) p.swap ∂μ.prod μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by simp [edgeWeight, hGsym p.1 p.2])
    _ = ∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
        (if p.1 ∈ I then h p.2 else 0) ∂μ.prod μ := by
      simpa using (integral_prod_swap (μ := μ) (ν := μ)
        (fun q : Ω × Ω => edgeWeight G q.1 q.2 *
          (if q.1 ∈ I then h q.2 else 0)))
    _ = _ := integral_root G I N hI h hsupport hrow

private theorem integral_penalty_right (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) (hsupport : ∀ x ∉ N, h x = 0) :
    (∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.2 else 0) ∂μ.prod μ) =
      ∫ x, h x * (∫ y in N, edgeWeight G x y ∂μ) ∂μ := by
  classical
  calc
    _ = ∫ p : Ω × Ω, (fun q : Ω × Ω => edgeWeight G q.1 q.2 *
        (if q.1 ∈ N ∧ q.2 ∈ N then h q.1 else 0)) p.swap ∂μ.prod μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by simp [edgeWeight, hGsym p.1 p.2,
        and_comm])
    _ = ∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
        (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 else 0) ∂μ.prod μ := by
      simpa using (integral_prod_swap (μ := μ) (ν := μ)
        (fun q : Ω × Ω => edgeWeight G q.1 q.2 *
          (if q.1 ∈ N ∧ q.2 ∈ N then h q.1 else 0)))
    _ = _ := integral_penalty_left G hG N hN h hh H hH hhbound hsupport

private theorem integrable_penalty_right (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) :
    Integrable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.2 else 0)) (μ.prod μ) := by
  classical
  have hs := (integrable_penalty_left (μ := μ) G hG N hN h hh H hH hhbound).swap
  convert hs using 1
  funext p
  simp [edgeWeight, hGsym p.1 p.2, and_comm]

private theorem integral_penalty (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (hG : Measurable (Function.uncurry G))
    (N : Set Ω) (hN : MeasurableSet N) (h : Ω → ℝ)
    (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) (hsupport : ∀ x ∉ N, h x = 0) :
    (∫ p : Ω × Ω, edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0) ∂μ.prod μ) =
      2 * ∫ x, h x * (∫ y in N, edgeWeight G x y ∂μ) ∂μ := by
  classical
  have heq : (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0)) =
      (fun p => edgeWeight G p.1 p.2 *
        (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 else 0) +
        edgeWeight G p.1 p.2 *
        (if p.1 ∈ N ∧ p.2 ∈ N then h p.2 else 0)) := by
    funext p
    by_cases hn : p.1 ∈ N ∧ p.2 ∈ N <;> simp [hn, mul_add]
  rw [heq, integral_add (integrable_penalty_left G hG N hN h hh H hH hhbound)
    (integrable_penalty_right G hGsym hG N hN h hh H hH hhbound),
    integral_penalty_left G hG N hN h hh H hH hhbound hsupport,
    integral_penalty_right G hGsym hG N hN h hh H hH hhbound hsupport]
  ring

/-- The exact signed gain from repricing a root row against its original
neighbor square. The original charge is only required to be bounded. -/
theorem physicalObjective_charge_eq (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (hG : Measurable (Function.uncurry G))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hYbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hYzero : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = false → Y p.1 p.2 = 0)
    (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p.1 p.2 = true ↔ p.2 ∈ N))
    (h : Ω → ℝ) (hh : Measurable h) (H : ℝ) (hH : 0 ≤ H)
    (hhbound : ∀ x, ‖h x‖ ≤ H) (hsupport : ∀ x ∉ N, h x = 0) :
    FiniteCappedSamplingCost.physicalObjective μ (charge G Y I N h) =
      FiniteCappedSamplingCost.physicalObjective μ Y +
        ∫ x, h x * (μ.real I - ∫ z in N, edgeWeight G x z ∂μ) ∂μ := by
  classical
  have hYint : Integrable (Function.uncurry Y) (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable B
      (Eventually.of_forall (fun p => hYbound p.1 p.2))
  have hleft := integrable_root (μ := μ) G hG I hI h hh H hH hhbound
  have hright : Integrable (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
      (if p.2 ∈ I then h p.1 else 0)) (μ.prod μ) := by
    have hs := hleft.swap
    convert hs using 1
    funext p
    simp [edgeWeight, hGsym p.1 p.2]
  have hpen := integrable_penalty (μ := μ) G hG N hN h hh H hH hhbound
  have hpenleft := integrable_penalty_left (μ := μ) G hG N hN h hh H hH hhbound
  have hdegree : Integrable (fun x => h x * (∫ z in N, edgeWeight G x z ∂μ)) μ := by
    apply hpenleft.integral_prod_left.congr
    exact Eventually.of_forall (fun x => by
      change (∫ z, edgeWeight G x z *
        (if x ∈ N ∧ z ∈ N then h x else 0) ∂μ) =
        h x * (∫ z in N, edgeWeight G x z ∂μ)
      by_cases hx : x ∈ N
      · have heq : (fun z => edgeWeight G x z *
            (if x ∈ N ∧ z ∈ N then h x else 0)) =
            (fun z => h x * N.indicator (edgeWeight G x) z) := by
          funext z
          by_cases hz : z ∈ N <;> simp [hx, hz, Set.indicator, mul_comm]
        rw [heq, integral_const_mul, integral_indicator hN]
      · simp [hx, hsupport x hx])
  have hconst : Integrable (fun x => h x * μ.real I) μ :=
    (integrable_h h hh H hhbound).mul_const _
  have hgain : (∫ x, h x * (μ.real I - ∫ z in N, edgeWeight G x z ∂μ) ∂μ) =
      μ.real I * (∫ x, h x ∂μ) -
        ∫ x, h x * (∫ z in N, edgeWeight G x z ∂μ) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hconst hdegree, integral_mul_const, mul_comm]
  have heq : (Function.uncurry (charge G Y I N h)) =ᵐ[μ.prod μ]
      (fun p : Ω × Ω => Y p.1 p.2 +
        (edgeWeight G p.1 p.2 * (if p.1 ∈ I then h p.2 else 0) +
          edgeWeight G p.1 p.2 * (if p.2 ∈ I then h p.1 else 0) -
          edgeWeight G p.1 p.2 *
            (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0))) := by
    filter_upwards [hYzero] with p hp
    change charge G Y I N h p.1 p.2 = _
    cases hv : G p.1 p.2 with
    | false => simp [charge, edgeWeight, hv, hp hv]
    | true => simp [charge, edgeWeight, increment, hv]
  unfold FiniteCappedSamplingCost.physicalObjective
  change (∫ p : Ω × Ω, (Function.uncurry (charge G Y I N h)) p ∂μ.prod μ) / 2 = _
  rw [integral_congr_ae heq]
  change (∫ p : Ω × Ω,
      ((Function.uncurry Y) +
        ((fun p : Ω × Ω => edgeWeight G p.1 p.2 *
            (if p.1 ∈ I then h p.2 else 0)) +
          (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
            (if p.2 ∈ I then h p.1 else 0)) -
          (fun p : Ω × Ω => edgeWeight G p.1 p.2 *
            (if p.1 ∈ N ∧ p.2 ∈ N then h p.1 + h p.2 else 0)))) p ∂μ.prod μ) / 2 = _
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_add, integral_sub, integral_add,
    integral_root G I N hI h hsupport hrow,
    integral_root_right G hGsym I N hI h hsupport hrow,
    integral_penalty G hGsym hG N hN h hh H hH hhbound hsupport,
    hgain]
  all_goals first
    | exact hYint
    | exact hleft
    | exact hright
    | exact hpen
    | exact hleft.add hright
    | exact (hleft.add hright).sub hpen
    | (simp only [Function.uncurry]; ring)

/-- At a full scalar optimum, a feasible signed root edit cannot have
positive actual integral gain. The edited charge has no compact-box premise. -/
theorem integral_gain_le_zero_of_full_optimum (G : Ω → Ω → Bool)
    (hGsym : ∀ x y, G x y = G y x)
    (hG : Measurable (Function.uncurry G))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (B : ℝ) (hB : 0 ≤ B) (hYbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hYle : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 ≤ 1)
    (hYzero : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ G Y n)
    (hopt : FiniteCappedSamplingCost.physicalObjective μ Y =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ G))
    (I N : Set Ω) (hI : MeasurableSet I) (hN : MeasurableSet N)
    (hdisjoint : Disjoint I N)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p.1 p.2 = true ↔ p.2 ∈ N))
    (h : Ω → ℝ) (hh : Measurable h) (hpos : ∀ x, 0 ≤ h x)
    (hcap : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ I → G p.1 p.2 = true → Y p.1 p.2 + h p.2 ≤ 1)
    (H : ℝ) (hH : 0 ≤ H) (hhbound : ∀ x, ‖h x‖ ≤ H)
    (hsupport : ∀ x ∉ N, h x = 0) :
    (∫ x, h x * (μ.real I - ∫ z in N, edgeWeight G x z ∂μ) ∂μ) ≤ 0 := by
  have hnewSym : ∀ᵐ p ∂μ.prod μ,
      charge G Y I N h p.1 p.2 = charge G Y I N h p.2 p.1 := by
    filter_upwards [hYsym] with p hp
    simp [charge, hGsym p.1 p.2, hp, increment_symm]
  have hnewZero : ∀ᵐ p ∂μ.prod μ,
      G p.1 p.2 = false → charge G Y I N h p.1 p.2 = 0 :=
    Eventually.of_forall (fun p hp => charge_zero_of_nonedge G Y I N h hp)
  have hrowOne : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ I → G p.1 p.2 = true → p.2 ∈ N := by
    filter_upwards [hrow] with p hp hi he
    exact (hp hi).mp he
  have hnewFull : ∀ n, FiniteArity.FeasibleOrder μ G (charge G Y I N h) n := by
    intro n
    exact feasibleOrder G Y I N hdisjoint h hpos hsupport hYsym hYle hrowOne hcap n
      (hfull n)
  have hbound := FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    G hGsym hG (charge G Y I N h)
    (measurable_charge G hG Y hY I N hI hN h hh) (B + 4 * H)
    (fun p => norm_charge_le G Y I N h B H hB hH hYbound hhbound p.1 p.2)
    hnewSym hnewZero hnewFull
  rw [physicalObjective_charge_eq G hGsym hG Y hY B hYbound hYzero I N
    hI hN hrow h hh H hH hhbound hsupport, hopt] at hbound
  linarith

end Erdos1017.SignedRootRepricing
