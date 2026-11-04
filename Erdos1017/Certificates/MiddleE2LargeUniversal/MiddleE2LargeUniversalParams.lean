module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Parameter functions of the large-atom certificate

This module defines the scalar functions of `q` and `A` used by the certificate,
among them the reciprocal-cusp denominator `rq`, the slope `ellq` and its defect
`deq`, the quantity `rpq` and the selector surplus `surq`, and proves their
monotonicity in `q` and `A`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal

/-- The reciprocal-cusp denominator `R(q)=1+7q+q^2`. -/
def rq (q : ℝ) : ℝ := 1 + 7 * q + q * q

/-- The slope `ell(q)=(2-q)/(2+q)`. -/
def ellq (q : ℝ) : ℝ := (2 - q) / (2 + q)

/-- The slope defect `delta(q)=1-ell(q)`. -/
def deq (q : ℝ) : ℝ := 1 - ellq q

/-- The lowered margin `g_q`. -/
def gq (q : ℝ) : ℝ := q * (1 + 2 * q) / (2 * rq q)

/-- The missing density `h_q`. -/
def hq (q : ℝ) : ℝ := (q + 2) * (q + 2) * (1 + 4 * q + 13 * q * q) / (8 * rq q * rq q)

/-- The ratio cap `r_q^*`. -/
def yq (q : ℝ) : ℝ := 9 * q / (2 * rq q)

/-- The forward-gap constant `K_q^*`. -/
def kq (q : ℝ) : ℝ := 9 * q * q * (1 - q * q) / (4 * rq q * rq q)

/-- The parameter window of the large-atom certificate. -/
def QWindow (q : ℝ) : Prop := 157 / 1000 ≤ q ∧ q ≤ 1 / 5

theorem rq_pos {q : ℝ} (hq : 0 ≤ q) : 0 < rq q := by
  unfold rq
  positivity

theorem ellq_anti {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) : ellq q ≤ ellq q₀ := by
  unfold ellq
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem deq_mono {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) : deq q₀ ≤ deq q := by
  unfold deq
  linarith [ellq_anti h₀ hq]

theorem gq_mono {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) : gq q₀ ≤ gq q := by
  have hR₀ := rq_pos h₀
  have hR := rq_pos (h₀.trans hq)
  unfold gq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  unfold rq at *
  -- The numerator of the derivative is `1+4q+13q^2`.
  nlinarith [mul_nonneg h₀ (sub_nonneg.mpr hq), mul_nonneg (mul_nonneg h₀ h₀) (sub_nonneg.mpr hq),
    mul_nonneg (mul_nonneg h₀ (h₀.trans hq)) (sub_nonneg.mpr hq),
    mul_nonneg (h₀.trans hq) (sub_nonneg.mpr hq), sub_nonneg.mpr hq]

theorem yq_mono {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) (h1 : q ≤ 1) : yq q₀ ≤ yq q := by
  have hR₀ := rq_pos h₀
  have hR := rq_pos (h₀.trans hq)
  unfold yq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  unfold rq at *
  -- The difference is `9(q-q₀)(1-q₀q)`.
  have hqq : q₀ * q ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hqq)]

/-- The decreasing factor `(q+2)/R(q)` of `h_q`. -/
def f1q (q : ℝ) : ℝ := (q + 2) / rq q

/-- The increasing factor `q/R(q)` of `K_q^*`. -/
def f2q (q : ℝ) : ℝ := q / rq q

/-- The increasing factor `1+4q+13q^2` of `h_q`. -/
def pq (q : ℝ) : ℝ := 1 + 4 * q + 13 * q * q

theorem hq_eq {q : ℝ} (h0 : 0 ≤ q) : hq q = f1q q * f1q q * pq q / 8 := by
  have hR := rq_pos h0
  unfold hq f1q pq
  field_simp

theorem kq_eq {q : ℝ} (h0 : 0 ≤ q) : kq q = 9 / 4 * f2q q * f2q q * (1 - q * q) := by
  have hR := rq_pos h0
  unfold kq f2q
  field_simp

theorem f1q_anti {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) : f1q q ≤ f1q q₀ := by
  have hR₀ := rq_pos h₀
  have hR := rq_pos (h₀.trans hq)
  unfold f1q
  rw [div_le_div_iff₀ hR hR₀]
  unfold rq
  -- The difference is `(q-q₀)(13+2(q+q₀)+q₀q)`.
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg h₀ (h₀.trans hq)),
    mul_nonneg (sub_nonneg.mpr hq) h₀, mul_nonneg (sub_nonneg.mpr hq) (h₀.trans hq)]

theorem f2q_mono {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) (h1 : q ≤ 1) : f2q q₀ ≤ f2q q := by
  have h := yq_mono h₀ hq h1
  have hR₀ := rq_pos h₀
  have hR := rq_pos (h₀.trans hq)
  unfold yq at h
  unfold f2q
  have e₀ : 9 * q₀ / (2 * rq q₀) = 9 / 2 * (q₀ / rq q₀) := by field_simp
  have e : 9 * q / (2 * rq q) = 9 / 2 * (q / rq q) := by field_simp
  rw [e₀, e] at h
  linarith

theorem pq_mono {q₀ q : ℝ} (h₀ : 0 ≤ q₀) (hq : q₀ ≤ q) : pq q₀ ≤ pq q := by
  unfold pq
  nlinarith

theorem ellq_sub {q q₁ : ℝ} (h : 0 ≤ q) (h₁ : 0 ≤ q₁) :
    ellq q - ellq q₁ = 4 * (q₁ - q) / ((2 + q) * (2 + q₁)) := by
  unfold ellq
  field_simp
  ring

theorem gq_sub {q q₁ : ℝ} (h : 0 ≤ q) (h₁ : 0 ≤ q₁) :
    gq q₁ - gq q = (q₁ - q) * (1 + 2 * (q + q₁) + 13 * q * q₁) / (2 * rq q * rq q₁) := by
  have hR := rq_pos h
  have hR₁ := rq_pos h₁
  unfold gq
  field_simp
  unfold rq
  ring

/-- `R_{P,0}` as a function of `(q,A)`. -/
def rpq (q A : ℝ) : ℝ := ellq q * (1 - A) - A + gq q

/-- `R_{P,0}` decreases in `q` throughout the window, since
`(1-A)(ell(q)-ell(q₁))` dominates the margin increment. -/
theorem rpq_anti_q {q q₁ A : ℝ} (hq : QWindow q) (hq₁ : QWindow q₁) (hle : q ≤ q₁)
    (hA : A ≤ 369 / 1000) : rpq q₁ A ≤ rpq q A := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hr0, hr1⟩ := hq₁
  have hl := ellq_sub (q := q) (q₁ := q₁) (by linarith) (by linarith)
  have hg := gq_sub (q := q) (q₁ := q₁) (by linarith) (by linarith)
  have hR := rq_pos (q := q) (by linarith)
  have hR₁ := rq_pos (q := q₁) (by linarith)
  have hX : 1 / 2 ≤ 4 * (1 - A) / ((2 + q) * (2 + q₁)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hY : (1 + 2 * (q + q₁) + 13 * q * q₁) / (2 * rq q * rq q₁) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    unfold rq
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ q₁)]
  have hd : 0 ≤ q₁ - q := by linarith
  have e : rpq q A - rpq q₁ A =
      (q₁ - q) * (4 * (1 - A) / ((2 + q) * (2 + q₁))) -
        (q₁ - q) * ((1 + 2 * (q + q₁) + 13 * q * q₁) / (2 * rq q * rq q₁)) := by
    have e₁ : rpq q A - rpq q₁ A = (1 - A) * (ellq q - ellq q₁) - (gq q₁ - gq q) := by
      unfold rpq
      ring
    rw [e₁, hl, hg]
    ring
  nlinarith [mul_le_mul_of_nonneg_left hX hd, mul_le_mul_of_nonneg_left hY hd]

theorem rpq_anti_A {q A A₂ : ℝ} (hq : QWindow q) (hle : A ≤ A₂) : rpq q A₂ ≤ rpq q A := by
  have hl : 0 ≤ ellq q := by
    unfold ellq
    exact div_nonneg (by linarith [hq.2]) (by linarith [hq.1])
  unfold rpq
  nlinarith

/-- The lower-count selector surplus `D_2(A)-g_q`. -/
def surq (A q : ℝ) : ℝ := (-1 + 6 * A - (8 - 3 * deq q) * A ^ 2) / 3 - gq q

theorem surq_mono_A {q A A₂ : ℝ} (hq : QWindow q) (h0 : 0 ≤ A) (hle : A ≤ A₂)
    (h2 : A₂ ≤ 369 / 1000) : surq A q ≤ surq A₂ q := by
  have hd : 0 ≤ deq q := by
    have := ellq_anti (q₀ := 0) (q := q) le_rfl (by linarith [hq.1])
    unfold deq
    unfold ellq at this ⊢
    norm_num at this
    linarith
  have hd1 : deq q ≤ 1 := by
    unfold deq ellq
    have : 0 ≤ (2 - q) / (2 + q) := div_nonneg (by linarith [hq.2]) (by linarith [hq.1])
    linarith
  unfold surq
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hd, mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) hd)
    (by linarith : (0 : ℝ) ≤ A + A₂)]

theorem surq_anti_q {q q₁ A : ℝ} (hq : QWindow q) (hq₁ : QWindow q₁) (hle : q ≤ q₁)
    (hA0 : 0 ≤ A) (hA : A ≤ 369 / 1000) : surq A q₁ ≤ surq A q := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hr0, hr1⟩ := hq₁
  have hl := ellq_sub (q := q) (q₁ := q₁) (by linarith) (by linarith)
  have hg := gq_sub (q := q) (q₁ := q₁) (by linarith) (by linarith)
  have hR := rq_pos (q := q) (by linarith)
  have hR₁ := rq_pos (q := q₁) (by linarith)
  have hX : 4 * A ^ 2 / ((2 + q) * (2 + q₁)) ≤ 7 / 50 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hY : 7 / 50 ≤ (1 + 2 * (q + q₁) + 13 * q * q₁) / (2 * rq q * rq q₁) := by
    rw [le_div_iff₀ (by positivity)]
    unfold rq
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ q₁),
      mul_le_mul hq1 hr1 (by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 5)]
  have hd : 0 ≤ q₁ - q := by linarith
  have e : surq A q - surq A q₁ =
      (q₁ - q) * ((1 + 2 * (q + q₁) + 13 * q * q₁) / (2 * rq q * rq q₁)) -
        (q₁ - q) * (4 * A ^ 2 / ((2 + q) * (2 + q₁))) := by
    have e₁ : surq A q - surq A q₁ = (gq q₁ - gq q) - A ^ 2 * (ellq q - ellq q₁) := by
      unfold surq deq
      ring
    rw [e₁, hl, hg]
    ring
  nlinarith [mul_le_mul_of_nonneg_left hX hd, mul_le_mul_of_nonneg_left hY hd]

end Erdos1017.MiddleE2LargeUniversal
