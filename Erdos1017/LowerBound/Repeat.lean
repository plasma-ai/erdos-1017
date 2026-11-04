module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Repeated-type penalties and all-count bounds

Real-valued pair counts (`pairs`) and rooted penalty expressions bound the
effect of repeating one vertex type while the other stays Boolean; the low-slope
and paid-self cases extend scalar bounds to all counts.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Repeat

/-- The real-valued number of unordered pairs in a natural count. -/
def pairs (r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) / 2

theorem pairs_nonneg (r : ℕ) : 0 ≤ pairs r := by
  rcases r with _ | r
  · norm_num [pairs]
  · simp only [pairs, Nat.cast_succ, add_sub_cancel_right]
    positivity

/-- Nonnegative penalties control every rootless repetition count. -/
theorem rootlessCharge_nonpos (c c₁ c₂ p D : ℝ)
    (hc : 0 ≤ c) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hp : 0 ≤ p) (hD : 0 ≤ D) (r b n : ℕ) :
    -(r : ℝ) * (b : ℝ) * c
      - (n : ℝ) * ((r : ℝ) * c₁ + (b : ℝ) * c₂)
      - p * pairs n - D * pairs r ≤ 0 := by
  have hn := pairs_nonneg n
  have hr := pairs_nonneg r
  have h : 0 ≤ (r : ℝ) * (b : ℝ) * c
      + (n : ℝ) * ((r : ℝ) * c₁ + (b : ℝ) * c₂)
      + p * pairs n + D * pairs r := by positivity
  linarith

/-- The integer gap is essential: the corresponding assertion fails for real `w`. -/
theorem discrete_quadratic_bound (j w : ℕ) :
    (w : ℝ) * (2 * (j : ℝ) + 1 - (w : ℝ)) ≤ (j : ℝ) * ((j : ℝ) + 1) := by
  rcases le_or_gt w j with h | h
  · have h' : (w : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
    have := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h')
      (show (w : ℝ) - (j : ℝ) - 1 ≤ 0 by linarith)
    nlinarith
  · have h' : (j : ℝ) + 1 ≤ (w : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have := mul_nonneg (show 0 ≤ (w : ℝ) - (j : ℝ) by linarith)
      (show 0 ≤ (w : ℝ) - (j : ℝ) - 1 by linarith)
    nlinarith

def denominator (j : ℕ) : ℝ := (j : ℝ) * ((j : ℝ) + 1)

def star (j d : ℕ) : ℝ :=
  (d : ℝ) * (2 * (j : ℝ) + 1 - (d : ℝ)) / denominator j

def crossPenalty (j d e : ℕ) : ℝ := 2 * (d : ℝ) * (e : ℝ) / denominator j

def selfPenalty (j d : ℕ) : ℝ := 2 * (d : ℝ) ^ 2 / denominator j

/-- The complete rooted charge in the four-double-tight parametrization. -/
def rootedCharge (j d e r s n : ℕ) : ℝ :=
  (r : ℝ) * star j d + (s : ℝ) * star j e
    - (r : ℝ) * (s : ℝ) * crossPenalty j d e
    + (n : ℝ) * (2 * (j : ℝ) / denominator j
      - (r : ℝ) * (2 * (d : ℝ) / denominator j)
      - (s : ℝ) * (2 * (e : ℝ) / denominator j))
    - (2 / denominator j) * pairs n
    - selfPenalty j d * pairs r - selfPenalty j e * pairs s

/-- The exact weighted-count identity for the rooted charge, before taking an
inequality. -/
theorem rootedCharge_identity (j d e r s n : ℕ) :
    rootedCharge j d e r s n =
      ((r * d + s * e + n : ℕ) : ℝ) *
        (2 * (j : ℝ) + 1 - ((r * d + s * e + n : ℕ) : ℝ)) / denominator j := by
  simp only [rootedCharge, star, crossPenalty, selfPenalty, pairs,
    Nat.cast_add, Nat.cast_mul]
  ring

/-- All three counts are arbitrary; no vertex-classification assertion is used here. -/
theorem rootedCharge_le_one (j d e r s n : ℕ) (hj : 0 < j) :
    rootedCharge j d e r s n ≤ 1 := by
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hJ : 0 < denominator j := by unfold denominator; positivity
  rw [rootedCharge_identity, div_le_one hJ]
  exact discrete_quadratic_bound j (r * d + s * e + n)

theorem selfPenalty_nonneg (j d : ℕ) : 0 ≤ selfPenalty j d := by
  unfold selfPenalty denominator
  positivity

/-- Choosing the smaller increment makes its full repeat penalty affordable. -/
theorem selfPenalty_le_crossPenalty (j d e : ℕ) (hde : d ≤ e) :
    selfPenalty j d ≤ crossPenalty j d e := by
  have hde' : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  apply div_le_div_of_nonneg_right _ (by unfold denominator; positivity)
  nlinarith

/-- Repeating the smaller-increment type and keeping the other type Boolean
requires a self penalty between zero and the original cross penalty. -/
theorem four_double_tight_repeat (j d e : ℕ) (hj : 0 < j) (hde : d ≤ e) :
    ∃ D : ℝ, 0 ≤ D ∧ D ≤ crossPenalty j d e ∧
      ∀ (r b n : ℕ), b ≤ 1 →
        (r : ℝ) * star j d + (b : ℝ) * star j e
          - (r : ℝ) * (b : ℝ) * crossPenalty j d e
          + (n : ℝ) * (2 * (j : ℝ) / denominator j
            - (r : ℝ) * (2 * (d : ℝ) / denominator j)
            - (b : ℝ) * (2 * (e : ℝ) / denominator j))
          - (2 / denominator j) * pairs n - D * pairs r ≤ 1 := by
  refine ⟨selfPenalty j d, selfPenalty_nonneg j d,
    selfPenalty_le_crossPenalty j d e hde, ?_⟩
  intro r b n hb
  have hb' : pairs b = 0 := by
    interval_cases b <;> norm_num [pairs]
  have h := rootedCharge_le_one j d e r b n hj
  simpa only [rootedCharge, hb', mul_zero, sub_zero] using h

/-- The dust-free repeated-star estimate used for low `k`. -/
theorem repeated_star_bound (t c : ℝ) (ht : (2 : ℝ) / 3 ≤ t)
    (hc : 2 * t - 1 ≤ c) (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * t - c * pairs r ≤ 1 := by
  by_cases hr₂ : r = 2
  · subst r
    norm_num [pairs]
    linarith
  · have hr₃ : 3 ≤ r := by omega
    have hr₃' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr₃
    have hrt := mul_le_mul_of_nonneg_left ht
      (show (0 : ℝ) ≤ (r : ℝ) by positivity)
    have hfactor : 0 ≤ (r : ℝ) * t - ((r : ℝ) + 1) / 2 := by linarith
    have hprod := mul_nonneg (show 0 ≤ (r : ℝ) - 2 by linarith) hfactor
    have hpen := mul_nonneg (sub_nonneg.mpr hc) (pairs_nonneg r)
    unfold pairs at hpen ⊢
    nlinarith

/-- The Boolean-present estimate, using its zero-count equality. -/
theorem repeated_boolean_bound (t₁ t₂ c : ℝ) (ht₂ : t₂ ≤ 1)
    (hc : c = t₁ + t₂ - 1) (hpay : 1 - t₂ ≤ c)
    (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * t₁ + t₂ - (r : ℝ) * c - c * pairs r ≤ 1 := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hc₀ : 0 ≤ c := by linarith
  have hmul := mul_nonneg hc₀ (show 0 ≤ (r : ℝ) - 2 by linarith)
  have hfactor : (1 - t₂) - c * (r : ℝ) / 2 ≤ 0 := by nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (r : ℝ) - 1 by linarith) hfactor
  unfold pairs
  nlinarith

/-- The rooted expression with the first type repeated. -/
def oneSidedCharge (t₁ t₂ v c c₁ c₂ p D : ℝ) (r b n : ℕ) : ℝ :=
  (r : ℝ) * t₁ + (b : ℝ) * t₂ - (r : ℝ) * (b : ℝ) * c
    + (n : ℝ) * (v - (r : ℝ) * c₁ - (b : ℝ) * c₂)
    - p * pairs n - D * pairs r

/-- The low-slope all-count conclusion from its scalar bounds and old tests.
The parameter inequalities themselves are explicit hypotheses here. -/
theorem low_slope_repeat (t₁ t₂ v c c₁ c₂ p : ℝ)
    (ht₁ : (2 : ℝ) / 3 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1)
    (hc : c = t₁ + t₂ - 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hp : 0 ≤ p) (hv : v ≤ 2 * c₁)
    (hold : ∀ (a b n : ℕ), a ≤ 1 → b ≤ 1 →
      oneSidedCharge t₁ t₂ v c c₁ c₂ p 0 a b n ≤ 1) :
    ∀ (r b n : ℕ), b ≤ 1 →
      oneSidedCharge t₁ t₂ v c c₁ c₂ p c r b n ≤ 1 := by
  intro r b n hb
  by_cases hr : r ≤ 1
  · have hr' : pairs r = 0 := by interval_cases r <;> norm_num [pairs]
    simpa only [oneSidedCharge, hr', mul_zero] using hold r b n hr hb
  · have hr₂ : 2 ≤ r := by omega
    have hr₂' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr₂
    have hrc := mul_nonneg hc₁ (show 0 ≤ (r : ℝ) - 2 by linarith)
    have hbc : 0 ≤ (b : ℝ) * c₂ := by positivity
    have hs : v - (r : ℝ) * c₁ - (b : ℝ) * c₂ ≤ 0 := by nlinarith
    have hdust := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℝ) ≤ (n : ℝ) by positivity) hs
    have hpairs := mul_nonneg hp (pairs_nonneg n)
    have hbase : (r : ℝ) * t₁ + (b : ℝ) * t₂
        - (r : ℝ) * (b : ℝ) * c - c * pairs r ≤ 1 := by
      interval_cases b
      · simpa using repeated_star_bound t₁ c ht₁ (by linarith) r hr₂
      · simpa using repeated_boolean_bound t₁ t₂ c ht₂ hc (by linarith) r hr₂
    unfold oneSidedCharge
    linarith

/-- The all-count extension once the cross penalty pays a feasible
one-type self penalty and the other Boolean type makes the dust slope negative. -/
theorem paid_self_repeat (t₁ t₂ v c c₁ c₂ p D : ℝ)
    (ht₂ : t₂ ≤ 1) (hc : c = t₁ + t₂ - 1) (hpay : 1 - t₂ ≤ c)
    (hc₁ : 0 ≤ c₁) (hp : 0 ≤ p) (hv : v - 2 * c₁ - c₂ ≤ 0)
    (hD : D ≤ c)
    (hone : ∀ (r n : ℕ), oneSidedCharge t₁ t₂ v c c₁ c₂ p D r 0 n ≤ 1)
    (hold : ∀ (a b n : ℕ), a ≤ 1 → b ≤ 1 →
      oneSidedCharge t₁ t₂ v c c₁ c₂ p 0 a b n ≤ 1) :
    ∀ (r b n : ℕ), b ≤ 1 →
      oneSidedCharge t₁ t₂ v c c₁ c₂ p c r b n ≤ 1 := by
  intro r b n hb
  interval_cases b
  · have h := hone r n
    have hpen := mul_nonneg (sub_nonneg.mpr hD) (pairs_nonneg r)
    unfold oneSidedCharge at h ⊢
    nlinarith
  · by_cases hr : r ≤ 1
    · have hr' : pairs r = 0 := by interval_cases r <;> norm_num [pairs]
      simpa only [oneSidedCharge, hr', mul_zero] using hold r 1 n hr (by omega)
    · have hr₂ : 2 ≤ r := by omega
      have hr₂' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr₂
      have hrc := mul_nonneg hc₁ (show 0 ≤ (r : ℝ) - 2 by linarith)
      have hs : v - (r : ℝ) * c₁ - c₂ ≤ 0 := by nlinarith
      have hdust := mul_nonpos_of_nonneg_of_nonpos
        (show (0 : ℝ) ≤ (n : ℝ) by positivity) hs
      have hpairs := mul_nonneg hp (pairs_nonneg n)
      have hbase := repeated_boolean_bound t₁ t₂ c ht₂ hc hpay r hr₂
      simp only [oneSidedCharge, Nat.cast_one, one_mul, mul_one]
      linarith

/-- The one-type formula supplies the feasible self penalty required above. -/
theorem one_type_repeat (j d : ℕ) (hj : 0 < j) (t₂ c c₂ : ℝ) (r n : ℕ) :
    oneSidedCharge (star j d) t₂ (2 * (j : ℝ) / denominator j) c
      (2 * (d : ℝ) / denominator j) c₂ (2 / denominator j)
      (selfPenalty j d) r 0 n ≤ 1 := by
  have h := rootedCharge_le_one j d 0 r 0 n hj
  simpa [oneSidedCharge, rootedCharge, pairs] using h

end Erdos1017.Repeat
