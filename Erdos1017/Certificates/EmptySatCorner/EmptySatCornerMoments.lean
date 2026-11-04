module

public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerScalar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Moment bounds for the empty-source saturated corner

The rational deficit floor lies above its tangent at the original mean mass,
integrating it gives the two coupled moments, the deficit budget confines the
mean mass strictly below `E`, and the triangle bound is strengthened by the
retained own-square moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.EmptySatCorner

/-- The exact rational deficit floor lies above its tangent at the
original mean mass. Its remainder has the same positive denominator. -/
theorem deficit_floor_tangent {L E a q : ℝ}
    (hLE : E ≤ L) (ha : 2 * a < L + E) (hq : 2 * q < L + E) :
    (L - q) / (L + E - 2 * q) +
      (L - E) / (L + E - 2 * q) ^ 2 * (a - q) ≤
        (L - a) / (L + E - 2 * a) := by
  have hdena : 0 < L + E - 2 * a := by linarith only [ha]
  have hdenq : 0 < L + E - 2 * q := by linarith only [hq]
  have hid : ((L - a) / (L + E - 2 * a) - (L - q) / (L + E - 2 * q) -
      (L - E) / (L + E - 2 * q) ^ 2 * (a - q)) *
        ((L + E - 2 * a) * (L + E - 2 * q) ^ 2) =
          2 * (L - E) * (a - q) ^ 2 := by
    field_simp [hdena.ne', hdenq.ne',
      show L + E - a * 2 ≠ 0 by nlinarith only [ha],
      show L + E - q * 2 ≠ 0 by nlinarith only [hq]]
    ring
  have hr : 0 ≤ 2 * (L - E) * (a - q) ^ 2 :=
    mul_nonneg (by linarith only [hLE]) (sq_nonneg (a - q))
  have hnonneg : 0 ≤ (L - a) / (L + E - 2 * a) - (L - q) / (L + E - 2 * q) -
      (L - E) / (L + E - 2 * q) ^ 2 * (a - q) := by
    apply (mul_nonneg_iff_of_pos_right (mul_pos hdena (sq_pos_of_pos hdenq))).mp
    rw [hid]
    exact hr
  linarith only [hnonneg]

/-- A cubic with negative leading coefficient and nonnegative initial
slope cannot dip below both positive endpoint values. This pays the
entire small-atom support interval without a sampled sign check. -/
theorem cubic_pos_between {a b c d E L M : ℝ}
    (ha : 0 ≤ a) (hEL : E ≤ L) (hLM : L ≤ M)
    (hslope : 0 ≤ -3 * a * E ^ 2 + 2 * b * E + c)
    (hleft : 0 < -a * E ^ 3 + b * E ^ 2 + c * E + d)
    (hright : 0 < -a * M ^ 3 + b * M ^ 2 + c * M + d) :
    0 < -a * L ^ 3 + b * L ^ 2 + c * L + d := by
  by_cases heq : L = E
  · simpa only [heq] using hleft
  by_cases hmeq : L = M
  · simpa only [hmeq] using hright
  have hEL' : 0 < L - E := sub_pos.mpr (lt_of_le_of_ne hEL (Ne.symm heq))
  have hLM' : 0 < M - L := sub_pos.mpr (lt_of_le_of_ne hLM hmeq)
  let SL := -a * (L ^ 2 + L * E + E ^ 2) + b * (L + E) + c
  let SR := -a * (M ^ 2 + M * L + L ^ 2) + b * (M + L) + c
  have hleftId : (-a * L ^ 3 + b * L ^ 2 + c * L + d) -
      (-a * E ^ 3 + b * E ^ 2 + c * E + d) = (L - E) * SL := by
    dsimp only [SL]
    ring
  have hrightId : (-a * M ^ 3 + b * M ^ 2 + c * M + d) -
      (-a * L ^ 3 + b * L ^ 2 + c * L + d) = (M - L) * SR := by
    dsimp only [SR]
    ring
  by_contra hn
  have hSL : SL < 0 := by
    have hp : (L - E) * SL < 0 := by linarith only [hn, hleft, hleftId]
    by_contra hnot
    have hnonneg := mul_nonneg hEL'.le (le_of_not_gt hnot)
    linarith only [hp, hnonneg]
  have hSR : 0 < SR := by
    have hp : 0 < (M - L) * SR := by linarith only [hn, hright, hrightId]
    exact (mul_pos_iff_of_pos_left hLM').mp hp
  have hchange : SL - (-3 * a * E ^ 2 + 2 * b * E + c) =
      (L - E) * (b - a * (L + 2 * E)) := by
    dsimp only [SL]
    ring
  have hcoef : b - a * (L + 2 * E) < 0 := by
    have hp : (L - E) * (b - a * (L + 2 * E)) < 0 := by
      linarith only [hSL, hslope, hchange]
    by_contra hnot
    have hnonneg := mul_nonneg hEL'.le (le_of_not_gt hnot)
    linarith only [hp, hnonneg]
  have hcoef' : b - a * (M + L + E) < 0 := by
    have hp := mul_nonneg ha (show 0 ≤ M - E by linarith only [hEL, hLM])
    nlinarith only [hcoef, hp]
  have hdiff : SR - SL = (M - E) * (b - a * (M + L + E)) := by
    dsimp only [SL, SR]
    ring
  have hp := mul_neg_of_pos_of_neg (show 0 < M - E by linarith only [hEL', hLM']) hcoef'
  linarith only [hSL, hSR, hp, hdiff]

/-- Integrating the actual rational deficit floor gives both coupled
moments at the same original mean mass. No Jensen or covariance
certificate is supplied. The finite measure may be a restricted region. -/
theorem deficit_moment_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a d : Ω → ℝ) {L E delta : ℝ}
    (hj : 0 < μ.real univ) (ha : Integrable a μ) (hameas : Measurable a)
    (hd : Integrable d μ) (had : Integrable (fun x => a x * d x) μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hcap : ∀ᵐ x ∂μ, 2 * a x < L + E)
    (hLE : E < L) (hdelta : 0 < delta)
    (hrow : ∀ᵐ x ∂μ, delta * (L - a x) ≤ (L + E - 2 * a x) * d x) :
    let j := μ.real univ
    let q := (∫ x, a x ∂μ) / j
    0 ≤ q ∧ 2 * q < L + E ∧
      delta * j * ((L - q) / (L + E - 2 * q)) ≤ ∫ x, d x ∂μ ∧
      delta * j * q * ((L - q) / (L + E - 2 * q)) ≤ ∫ x, a x * d x ∂μ := by
  let j := μ.real univ
  let q := (∫ x, a x ∂μ) / j
  let C := L + E
  let f : Ω → ℝ := fun x => (L - a x) / (C - 2 * a x)
  let fq := (L - q) / (C - 2 * q)
  have hj' : 0 < j := hj
  have hq : 0 ≤ q := div_nonneg (integral_nonneg_of_ae ha0) hj'.le
  have hmean : j * q = ∫ x, a x ∂μ := by
    dsimp only [q]
    exact mul_div_cancel₀ _ hj'.ne'
  have hden : ∀ᵐ x ∂μ, 0 < C - 2 * a x := hcap.mono (fun _ hx => sub_pos.mpr hx)
  have hdenint : Integrable (fun x => C - 2 * a x) μ :=
    (integrable_const C).sub (ha.const_mul 2)
  have hsupport : Function.support (fun x => C - 2 * a x) =ᵐ[μ] univ :=
    hden.mono (fun x hx => by
      change (C - 2 * a x ≠ 0) = True
      exact propext (iff_true_intro hx.ne'))
  have hμpos : 0 < μ univ := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) zero_le
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hj
  have hdenpos : 0 < ∫ x, C - 2 * a x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae (hden.mono (fun _ hx => hx.le)) hdenint).mpr
    rwa [measure_congr hsupport]
  have hdeneq : (∫ x, C - 2 * a x ∂μ) = C * j - 2 * (∫ x, a x ∂μ) := by
    rw [integral_sub (integrable_const C) (ha.const_mul 2), integral_const_mul,
      integral_const, smul_eq_mul]
    dsimp only [j]
    ring
  have hqcap : 2 * q < C := by nlinarith only [hdenpos, hdeneq, hmean, hj']
  have hC : 0 < C := by linarith only [hqcap, hq]
  have hdenq : 0 < C - 2 * q := by linarith only [hqcap]
  have hf0 : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hcap, hden] with x hx hdx
    exact div_nonneg (by linarith only [hx, hLE]) hdx.le
  have hfd : ∀ᵐ x ∂μ, delta * f x ≤ d x := by
    filter_upwards [hden, hrow] with x hx hr
    dsimp only [f]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hx).mpr (by nlinarith only [hr])
  have hfmeas : Measurable f := (measurable_const.sub hameas).div
    (measurable_const.sub (hameas.const_mul 2))
  have hfi : Integrable f μ := (hd.div_const delta).mono_nonneg
    hfmeas.aestronglyMeasurable hf0 (by
      filter_upwards [hfd] with x hx
      exact (le_div_iff₀ hdelta).mpr (by nlinarith only [hx]))
  let slope := (L - E) / (C - 2 * q) ^ 2
  have hlinint : Integrable (fun x => fq + slope * (a x - q)) μ :=
    (integrable_const fq).add ((ha.sub (integrable_const q)).const_mul slope)
  have htangent : ∀ᵐ x ∂μ, fq + slope * (a x - q) ≤ f x := by
    filter_upwards [hcap] with x hx
    exact deficit_floor_tangent hLE.le hx hqcap
  have hJensen := integral_mono_ae hlinint hfi htangent
  have hlin : (∫ x, fq + slope * (a x - q) ∂μ) = j * fq := by
    have hsum := integral_add (integrable_const fq)
      ((ha.sub (integrable_const q)).const_mul slope)
    have hsub := integral_sub ha (integrable_const q)
    simp only [Pi.sub_apply] at hsum hsub
    rw [hsum, integral_const_mul, hsub, integral_const,
      integral_const, smul_eq_mul, smul_eq_mul]
    change j * fq + slope * ((∫ x, a x ∂μ) - j * q) = j * fq
    rw [hmean]
    ring
  rw [hlin] at hJensen
  have hfirst := integral_mono_ae (hfi.const_mul delta) hd hfd
  rw [integral_const_mul] at hfirst
  have hafEq : (fun x => a x * f x) =ᵐ[μ]
      fun x => (C * f x - L + a x) / 2 := by
    filter_upwards [hden] with x hx
    have hcancel : (C - 2 * a x) * f x = L - a x := by
      dsimp only [f]
      exact mul_div_cancel₀ _ hx.ne'
    nlinarith only [hcancel]
  have hafi : Integrable (fun x => a x * f x) μ :=
    ((((hfi.const_mul C).sub (integrable_const L)).add ha).div_const 2).congr hafEq.symm
  have hafint : 2 * (∫ x, a x * f x ∂μ) =
      C * (∫ x, f x ∂μ) - j * L + j * q := by
    have hint : (∫ x, a x * f x ∂μ) =
        (C * (∫ x, f x ∂μ) - j * L + ∫ x, a x ∂μ) / 2 := by
      have hsum := integral_add ((hfi.const_mul C).sub (integrable_const L)) ha
      have hsub := integral_sub (hfi.const_mul C) (integrable_const L)
      simp only [Pi.sub_apply] at hsum hsub
      rw [integral_congr_ae hafEq, integral_div, hsum, hsub,
        integral_const_mul, integral_const, smul_eq_mul]
    nlinarith only [hint, hmean]
  have hfqId : 2 * q * fq = C * fq - L + q := by
    have hcancel : (C - 2 * q) * fq = L - q := by
      dsimp only [fq]
      exact mul_div_cancel₀ _ hdenq.ne'
    nlinarith only [hcancel]
  have hweighted : j * q * fq ≤ ∫ x, a x * f x ∂μ := by
    have hp := mul_nonneg hC.le (sub_nonneg.mpr hJensen)
    have hscaled := congrArg (fun z => j * z) hfqId
    nlinarith only [hp, hscaled, hafint]
  have hlast := integral_mono_ae (hafi.const_mul delta) had (by
    filter_upwards [ha0, hfd] with x hax hdx
    have h := mul_le_mul_of_nonneg_left hdx hax
    nlinarith only [h])
  rw [integral_const_mul] at hlast
  refine ⟨hq, hqcap, ?_, ?_⟩
  · have hp := mul_le_mul_of_nonneg_left hJensen hdelta.le
    nlinarith only [hp, hfirst]
  · have hp := mul_le_mul_of_nonneg_left hweighted hdelta.le
    nlinarith only [hp, hlast]

/-- The same deficit budget confines its original mean mass strictly
below E and yields the exact coupled first-moment inequality. -/
theorem mean_mass_bounds_of_deficit_budget {j q L E delta D : ℝ}
    (hj : 0 < j) (hq : 0 ≤ q) (hcap : 2 * q < L + E) (hLE : E < L)
    (hdelta : 0 < delta)
    (hlower : delta * j * ((L - q) / (L + E - 2 * q)) ≤ D)
    (hupper : D ≤ delta * (j - L)) :
    2 * L < j ∧ 0 < E ∧ q < E ∧ (L + E) * L ≤ E * j ∧
      (j - 2 * L) * q ≤ E * j - (L + E) * L := by
  have hden : 0 < L + E - 2 * q := by linarith only [hcap]
  have hC : 0 < L + E := by linarith only [hcap, hq]
  have hL : 0 < L := by linarith only [hC, hLE]
  have hratio : 1 / 2 < (L - q) / (L + E - 2 * q) :=
    (lt_div_iff₀ hden).mpr (by linarith only [hLE])
  have hraw : j * ((L - q) / (L + E - 2 * q)) ≤ j - L := by
    apply (mul_le_mul_iff_right₀ hdelta).mp
    nlinarith only [hlower, hupper]
  have hjL : 2 * L < j := by
    have hp := mul_lt_mul_of_pos_left hratio hj
    nlinarith only [hp, hraw]
  have hscaled : j * (L - q) ≤ (j - L) * (L + E - 2 * q) := by
    have h := mul_le_mul_of_nonneg_right hraw hden.le
    have hid : j * ((L - q) / (L + E - 2 * q)) * (L + E - 2 * q) = j * (L - q) := by
      rw [mul_assoc, div_mul_cancel₀ _ hden.ne']
    rwa [hid] at h
  have hmoment : (j - 2 * L) * q ≤ E * j - (L + E) * L := by
    nlinarith only [hscaled]
  have hqnonneg := mul_nonneg (show 0 ≤ j - 2 * L by linarith only [hjL]) hq
  have hEL : (L + E) * L ≤ E * j := by linarith only [hmoment, hqnonneg]
  have hE : 0 < E := by
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hj.le
    have hpos := mul_pos hC hL
    linarith only [hEL, hp, hpos]
  have hqE : q < E := by
    by_contra hn
    have hp := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
      (show 0 ≤ j - 2 * L by linarith only [hjL])
    have hpos := mul_pos hL (sub_pos.mpr hLE)
    nlinarith only [hp, hmoment, hpos]
  exact ⟨hjL, hE, hqE, hEL, hmoment⟩

/-- Integrate the original triangle bound with its actual within-region
adjacency marginal. The marked own-square term is retained. -/
theorem triangle_deficit_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a d : Ω → ℝ) (G : Ω → Ω → ℝ)
    (M : Ω × Ω → ℝ) {delta : ℝ}
    (hd : Integrable d μ) (had : Integrable (fun x => a x * d x) μ)
    (hM : Integrable M (μ.prod μ)) (hG : Measurable (Function.uncurry G))
    (hGbox : ∀ x y, G x y ∈ Icc (0 : ℝ) 1)
    (hGsym : ∀ᵐ q ∂μ.prod μ, G q.1 q.2 = G q.2 q.1)
    (hmarginal : ∀ᵐ x ∂μ, (∫ y, G x y ∂μ) = μ.real univ - a x)
    (htriangle : ∀ᵐ q ∂μ.prod μ,
      M q + delta * G q.1 q.2 ≤ (d q.1 + d q.2) * G q.1 q.2) :
    (∫ q, M q ∂μ.prod μ) / 2 +
        delta * (∫ q : Ω × Ω, G q.1 q.2 ∂μ.prod μ) / 2 + (∫ x, a x * d x ∂μ) ≤
      μ.real univ * (∫ x, d x ∂μ) := by
  have hGb : ∀ q : Ω × Ω, ‖G q.1 q.2‖ ≤ 1 := fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hGbox q.1 q.2).1]
    exact (hGbox q.1 q.2).2
  have hGi : Integrable (fun q : Ω × Ω => G q.1 q.2) (μ.prod μ) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (Eventually.of_forall hGb)
  have hd1 : Integrable (fun q : Ω × Ω => d q.1) (μ.prod μ) := by
    simpa only [mul_one] using hd.mul_prod (integrable_const (1 : ℝ))
  have hd2 : Integrable (fun q : Ω × Ω => d q.2) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hd
  have hfirsti := hd1.mul_bdd hG.aestronglyMeasurable (Eventually.of_forall hGb)
  have hsecondi := hd2.mul_bdd hG.aestronglyMeasurable (Eventually.of_forall hGb)
  have hbound := integral_mono_ae (hM.add (hGi.const_mul delta))
    (hfirsti.add hsecondi) (by
      filter_upwards [htriangle] with q hq
      change M q + delta * G q.1 q.2 ≤ d q.1 * G q.1 q.2 + d q.2 * G q.1 q.2
      nlinarith only [hq])
  have hleft := integral_add hM (hGi.const_mul delta)
  have hright := integral_add hfirsti hsecondi
  change (∫ q, M q + delta * G q.1 q.2 ∂μ.prod μ) ≤
    ∫ q : Ω × Ω, d q.1 * G q.1 q.2 + d q.2 * G q.1 q.2 ∂μ.prod μ at hbound
  dsimp only [Function.uncurry] at hright
  rw [hleft, hright, integral_const_mul] at hbound
  have hfirst : (∫ q : Ω × Ω, d q.1 * G q.1 q.2 ∂μ.prod μ) =
      μ.real univ * (∫ x, d x ∂μ) - ∫ x, a x * d x ∂μ := by
    rw [integral_prod (fun q : Ω × Ω => d q.1 * G q.1 q.2) hfirsti]
    have hrows : (fun x => ∫ y, d x * G x y ∂μ) =ᵐ[μ]
        fun x => μ.real univ * d x - a x * d x := by
      filter_upwards [hmarginal] with x hx
      rw [integral_const_mul, hx]
      ring
    rw [integral_congr_ae hrows,
      integral_sub (hd.const_mul (μ.real univ)) had, integral_const_mul]
  have hsecond : (∫ q : Ω × Ω, d q.2 * G q.1 q.2 ∂μ.prod μ) =
      μ.real univ * (∫ x, d x ∂μ) - ∫ x, a x * d x ∂μ := by
    calc
      _ = ∫ q : Ω × Ω, d q.2 * G q.2 q.1 ∂μ.prod μ :=
        integral_congr_ae (hGsym.mono (fun q hq => by rw [hq]))
      _ = ∫ q : Ω × Ω, d q.1 * G q.1 q.2 ∂μ.prod μ :=
        integral_prod_swap (fun q : Ω × Ω => d q.1 * G q.1 q.2)
      _ = _ := hfirst
  rw [hfirst, hsecond] at hbound
  nlinarith only [hbound]

/-- Both retained own-square moments strengthen the original triangle
budget by the same rational correction and its weaker linear bound. -/
theorem square_moment_triangle_bound {j q L E delta F e D Q : ℝ}
    (hj : 0 ≤ j) (hq : 0 ≤ q) (hcap : 2 * q < L + E) (hLE : E ≤ L)
    (hdelta : 0 ≤ delta) (hsquare : 2 * e = j ^ 2 - j * q)
    (htriangle : F / 2 + delta * e + Q ≤ j * D)
    (hQ : delta * j * q * ((L - q) / (L + E - 2 * q)) ≤ Q) :
    F ≤ 2 * j * D - delta * j ^ 2 - delta * j * (L - E) * q / (L + E - 2 * q) ∧
      F ≤ 2 * j * D - delta * j ^ 2 - delta * j * (L - E) * q / (L + E) := by
  have hden : 0 < L + E - 2 * q := by linarith only [hcap]
  have hC : 0 < L + E := by linarith only [hcap, hq]
  have hid : 2 * delta * j * q * ((L - q) / (L + E - 2 * q)) - delta * j * q =
      delta * j * (L - E) * q / (L + E - 2 * q) := by
    field_simp [hden.ne', show L + E - q * 2 ≠ 0 by nlinarith only [hcap]]
    ring
  have hscaled := congrArg (fun z => delta * z) hsquare
  have hfirst : F ≤ 2 * j * D - delta * j ^ 2 -
      delta * j * (L - E) * q / (L + E - 2 * q) := by
    nlinarith only [htriangle, hQ, hscaled, hid]
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hnum : 0 ≤ delta * j * (L - E) * q := by positivity
  have hdiv : delta * j * (L - E) * q / (L + E) ≤
      delta * j * (L - E) * q / (L + E - 2 * q) := by
    apply (div_le_div_iff₀ hC hden).mpr
    have hp := mul_nonneg hnum hq
    nlinarith only [hp]
  linarith only [hdiv]

end Erdos1017.EmptySatCorner
