module

public import Erdos1017.LowerBound.Repeat
public import Mathlib.Tactic.FieldSimp

/-!
# Repeat conclusion for the zero-tight pattern

The star coefficient `zeroStar` and cross penalty `zeroCross` of a pattern with
state 11 tight at count zero satisfy the payment inequalities and give the
complete all-count repeat conclusion, with only the original Boolean feasibility
tests as hypotheses.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Repeat

/-- Star coefficient determined by a double-tight state with slope ratio `k`. -/
def zeroStar (j k : ℕ) : ℝ :=
  1 - (k : ℝ) * ((k : ℝ) + 1) / denominator j

/-- Cross penalty when state 11 is tight at count zero. -/
def zeroCross (j k l : ℕ) : ℝ := zeroStar j k + zeroStar j l - 1

theorem denominator_pos (j : ℕ) (hj : 0 < j) : 0 < denominator j := by
  have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  unfold denominator
  positivity

theorem zeroStar_le_one (j k : ℕ) : zeroStar j k ≤ 1 := by
  have h : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) / denominator j := by
    unfold denominator
    positivity
  unfold zeroStar
  linarith

theorem zeroStar_antitone (j k l : ℕ) (hlk : l ≤ k) :
    zeroStar j k ≤ zeroStar j l := by
  have hlk' : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hl : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have hprod : (l : ℝ) * ((l : ℝ) + 1) ≤ (k : ℝ) * ((k : ℝ) + 1) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hprod
    (show 0 ≤ denominator j by unfold denominator; positivity)
  unfold zeroStar
  linarith

/-- The integer boundary `k = 0` is included. -/
theorem zeroStar_ge_two_thirds (j k : ℕ) (hj : 0 < j) (hhalf : 2 * k ≤ j) :
    (2 : ℝ) / 3 ≤ zeroStar j k := by
  have hpoly : 3 * k * (k + 1) ≤ j * (j + 1) := by
    by_cases hk : k = 0
    · subst k
      omega
    · have hk' : 1 ≤ k := by omega
      nlinarith
  have hpoly' : 3 * (k : ℝ) * ((k : ℝ) + 1) ≤ denominator j := by
    unfold denominator
    exact_mod_cast hpoly
  have hdiv : (k : ℝ) * ((k : ℝ) + 1) / denominator j ≤ 1 / 3 := by
    apply (div_le_iff₀ (denominator_pos j hj)).2
    linarith
  unfold zeroStar
  linarith

theorem zeroStar_eq_star (j k : ℕ) (hj : 0 < j) (hk : k ≤ j) :
    zeroStar j k = star j (j - k) := by
  have hJ : denominator j ≠ 0 := ne_of_gt (denominator_pos j hj)
  unfold zeroStar star
  rw [Nat.cast_sub hk]
  field_simp
  unfold denominator
  ring

/-- Both payment inequalities of the high range, retaining non-strict conclusions. -/
theorem high_range_payments (j k l : ℕ) (hj : 0 < j) (hk : k < j)
    (hsum : k + l < j) (hhalf : j < 2 * k) :
    selfPenalty j (j - k) ≤ zeroCross j k l ∧
      1 - zeroStar j l ≤ zeroCross j k l := by
  let d := j - k
  have hd : 0 < d := by dsimp [d]; omega
  have hkd : k + d = j := by dsimp [d]; omega
  have hld : l + 1 ≤ d := by omega
  have hhigh : 2 * d < j := by omega
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hkd' : (k : ℝ) + (d : ℝ) = (j : ℝ) := by exact_mod_cast hkd
  have hld' : (l : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hld
  have hhigh' : 2 * (d : ℝ) < (j : ℝ) := by exact_mod_cast hhigh
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have hbound' : (l : ℝ) * ((l : ℝ) + 1) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    nlinarith
  have hJ := denominator_pos j hj
  have hfirst : 2 * (d : ℝ) ^ 2 ≤ denominator j
      - (k : ℝ) * ((k : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1) := by
    unfold denominator
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by linarith)
      (show 0 ≤ (j : ℝ) - 2 * (d : ℝ) + 1 by linarith)]
  have hsecond : 2 * (l : ℝ) * ((l : ℝ) + 1) ≤
      denominator j - (k : ℝ) * ((k : ℝ) + 1) := by
    unfold denominator
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by linarith)
      (show 0 ≤ 2 * (j : ℝ) - 3 * (d : ℝ) + 3 by linarith)]
  constructor
  · change 2 * (d : ℝ) ^ 2 / denominator j ≤ zeroCross j k l
    unfold zeroCross zeroStar
    apply (div_le_iff₀ hJ).2
    field_simp
    nlinarith
  · unfold zeroCross zeroStar
    have h := (div_le_div_iff_of_pos_right hJ).2 hsecond
    field_simp at h ⊢
    nlinarith

/-- The complete all-count repeat conclusion for the classified zero-count
pattern. Only the original Boolean feasibility tests remain as hypotheses. -/
theorem zero_pattern_repeat (j k l : ℕ) (hj : 0 < j) (hk : k < j)
    (hlk : l ≤ k) (hsum : k + l < j)
    (hold : ∀ (a b n : ℕ), a ≤ 1 → b ≤ 1 →
      oneSidedCharge (zeroStar j k) (zeroStar j l)
        (2 * (j : ℝ) / denominator j) (zeroCross j k l)
        (2 * ((j - k : ℕ) : ℝ) / denominator j)
        (2 * ((j - l : ℕ) : ℝ) / denominator j)
        (2 / denominator j) 0 a b n ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ D ≤ zeroCross j k l ∧
      ∀ (r b n : ℕ), b ≤ 1 →
        oneSidedCharge (zeroStar j k) (zeroStar j l)
          (2 * (j : ℝ) / denominator j) (zeroCross j k l)
          (2 * ((j - k : ℕ) : ℝ) / denominator j)
          (2 * ((j - l : ℕ) : ℝ) / denominator j)
          (2 / denominator j) D r b n ≤ 1 := by
  have hJ := denominator_pos j hj
  have ht := zeroStar_antitone j k l hlk
  have ht₂ := zeroStar_le_one j l
  have hc : zeroCross j k l = zeroStar j k + zeroStar j l - 1 := rfl
  have hc₁ : 0 ≤ 2 * ((j - k : ℕ) : ℝ) / denominator j := by positivity
  have hc₂ : 0 ≤ 2 * ((j - l : ℕ) : ℝ) / denominator j := by positivity
  have hp : 0 ≤ (2 : ℝ) / denominator j := by positivity
  by_cases hhalf : 2 * k ≤ j
  · have ht₁ := zeroStar_ge_two_thirds j k hj hhalf
    have hc₀ : 0 ≤ zeroCross j k l := by linarith
    have hnum : 2 * (j : ℝ) ≤ 4 * ((j - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk.le]
      have hhalf' : 2 * (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hhalf
      linarith
    have hv : 2 * (j : ℝ) / denominator j ≤
        2 * (2 * ((j - k : ℕ) : ℝ) / denominator j) := by
      convert div_le_div_of_nonneg_right hnum hJ.le using 1
      ring
    refine ⟨zeroCross j k l, hc₀, le_rfl, ?_⟩
    exact low_slope_repeat _ _ _ _ _ _ _ ht₁ ht ht₂ hc hc₁ hc₂ hp hv hold
  · have hhalf' : j < 2 * k := by omega
    obtain ⟨hself, hpay⟩ := high_range_payments j k l hj hk hsum hhalf'
    have hc₀ : 0 ≤ zeroCross j k l := le_trans (selfPenalty_nonneg j (j - k)) hself
    have hl : l ≤ j := by omega
    have hnum : 2 * (j : ℝ) - 4 * ((j - k : ℕ) : ℝ)
        - 2 * ((j - l : ℕ) : ℝ) ≤ 0 := by
      rw [Nat.cast_sub hk.le, Nat.cast_sub hl]
      have hsum' : (k : ℝ) + (l : ℝ) < (j : ℝ) := by exact_mod_cast hsum
      have hk' : (k : ℝ) < (j : ℝ) := by exact_mod_cast hk
      linarith
    have hv : 2 * (j : ℝ) / denominator j
        - 2 * (2 * ((j - k : ℕ) : ℝ) / denominator j)
        - 2 * ((j - l : ℕ) : ℝ) / denominator j ≤ 0 := by
      convert div_nonpos_of_nonpos_of_nonneg hnum hJ.le using 1
      ring
    have hone : ∀ (r n : ℕ),
        oneSidedCharge (zeroStar j k) (zeroStar j l)
          (2 * (j : ℝ) / denominator j) (zeroCross j k l)
          (2 * ((j - k : ℕ) : ℝ) / denominator j)
          (2 * ((j - l : ℕ) : ℝ) / denominator j)
          (2 / denominator j) (selfPenalty j (j - k)) r 0 n ≤ 1 := by
      intro r n
      rw [zeroStar_eq_star j k hj hk.le]
      exact one_type_repeat j (j - k) hj _ _ _ r n
    refine ⟨zeroCross j k l, hc₀, le_rfl, ?_⟩
    exact paid_self_repeat _ _ _ _ _ _ _ _ ht₂ hc hpay hc₁ hp hv hself hone hold

end Erdos1017.Repeat
