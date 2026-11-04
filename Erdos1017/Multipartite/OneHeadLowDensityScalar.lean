module

public import Erdos1017.Multipartite.MultipartiteLowDensityComparison

/-!
# One-head lower bound at low density

A one-head lower bound and its low-density scalar consequence. The dust penalty
is `2*r²`; its all-count tests are proved without assuming membership in the
bounded coefficient box.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

private def lowerCoefficients (r : ℝ) : MultipartiteDust.Coefficients 1
  | .inl _ => 1
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) => 2 * r - r ^ 2
  | .inr (.inr (.inr false)) => 2 * r - r ^ 2
  | .inr (.inr (.inr true)) => 2 * r ^ 2

private theorem lowerCoefficients_tests (r : ℝ) :
    ∀ X n, MultipartiteDust.charge (lowerCoefficients r) X n ≤ 1 := by
  intro X n
  have hp : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rcases n with _ | n
    · norm_num
    · push_cast
      have hn := Nat.cast_nonneg (α := ℝ) n
      exact mul_nonneg (by linarith) (by linarith)
  simp only [MultipartiteDust.charge, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
    lowerCoefficients, Fin.sum_univ_one]
  cases hX : X 0 <;> norm_num [Selector.bit, hX]
  · nlinarith [sq_nonneg (r * n - 1)]
  · nlinarith [mul_nonneg (sq_nonneg r) hp]

private theorem lowerCoefficients_objective (r x S : ℝ) :
    MultipartiteDust.objective (fun _ : Fin 1 => x) S (lowerCoefficients r) =
      x + (1 - x) * (2 * r - r ^ 2) * S - r ^ 2 * S ^ 2 := by
  simp [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.incident, MultipartiteDust.linear, MultipartiteDust.penalty,
    lowerCoefficients]
  ring

theorem oneHeadValue_lower_bound {x S : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (hS : 0 ≤ S) :
    x + (1 - x) ^ 2 * S / (1 - x + S) ≤ oneHeadValue (x + S) (x ^ 2) := by
  let r := (1 - x) / (1 - x + S)
  have hd : 0 < 1 - x + S := by linarith [hx.2]
  have h := MultipartiteDust.objective_le_value_of_tests (lowerCoefficients r)
    (lowerCoefficients_tests r) (by change 0 ≤ 2 * r ^ 2; positivity)
    (fun _ : Fin 1 => x) (fun _ => ⟨hx.1, hx.2.le⟩) S hS
  rw [lowerCoefficients_objective] at h
  have hobj : x + (1 - x) * (2 * r - r ^ 2) * S - r ^ 2 * S ^ 2 =
      x + (1 - x) ^ 2 * S / (1 - x + S) := by
    dsimp only [r]
    field_simp
    ring
  rw [hobj] at h
  rw [oneHeadValue_eq_finite, Real.sqrt_sq hx.1, add_sub_cancel_left]
  exact h

private def lowDensityCubic (x S : ℝ) : ℝ :=
  4 * x * (1 - x) + 4 * S * (1 - 2 * x + 2 * x ^ 2) - (3 + x) * S ^ 2 - S ^ 3

private theorem lowDensityCubic_nonneg {x S : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hS : 0 ≤ S) (hShi : S ≤ 2 * Real.sqrt (1 + x ^ 2) - 1 - x) :
    0 ≤ lowDensityCubic x S := by
  let q := Real.sqrt (1 + x ^ 2)
  let U := 2 * q - 1 - x
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq : q ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hq1 : 1 ≤ q := by nlinarith [sq_nonneg x]
  have hU : 0 < U := by dsimp only [U]; linarith [hx.2]
  have hSU : S ≤ U := hShi
  have hN0 : 0 ≤ lowDensityCubic x 0 := by
    dsimp only [lowDensityCubic]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2.le)]
  have hNU : lowDensityCubic x U = 6 * (1 - x) ^ 2 * (q - 1) := by
    calc
      lowDensityCubic x U = 6 * (1 - x) ^ 2 * (q - 1) +
          8 * (x - q) * (q ^ 2 - 1 - x ^ 2) := by
            dsimp only [lowDensityCubic, U]
            ring
      _ = 6 * (1 - x) ^ 2 * (q - 1) := by rw [hq]; ring
  have hNU0 : 0 ≤ lowDensityCubic x U := by
    rw [hNU]
    have hgap : 0 ≤ q - 1 := sub_nonneg.mpr hq1
    positivity
  have hchord : U * lowDensityCubic x S =
      (U - S) * lowDensityCubic x 0 + S * lowDensityCubic x U +
        U * S * (U - S) * (3 + x + U + S) := by
    dsimp only [lowDensityCubic]
    ring
  have hnonneg : 0 ≤ U * lowDensityCubic x S := by
    rw [hchord]
    have hUS : 0 ≤ U - S := sub_nonneg.mpr hSU
    have hx0 : 0 ≤ x := hx.1
    positivity
  nlinarith

private theorem lower_bound_ge_third {x S : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hS : 0 ≤ S)
    (hdensity : ((x + S) + ((x + S) ^ 2 - x ^ 2) / 2) / (1 + (x + S)) ^ 2 ≤ 3 / 8) :
    ((x + S) + ((x + S) ^ 2 - x ^ 2) / 2) / 3 ≤
      x + (1 - x) ^ 2 * S / (1 - x + S) := by
  have hden : 0 < 1 - x + S := by linarith [hx.2]
  have htotal : 0 < 1 + (x + S) := by linarith [hx.1]
  have hd := (div_le_iff₀ (sq_pos_of_pos htotal)).mp hdensity
  have hq := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hq0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hShi : S ≤ 2 * Real.sqrt (1 + x ^ 2) - 1 - x := by nlinarith
  have hN := lowDensityCubic_nonneg hx hS hShi
  have hid : 2 * (1 - x + S) *
      (3 * (x + (1 - x) ^ 2 * S / (1 - x + S)) -
        ((x + S) + ((x + S) ^ 2 - x ^ 2) / 2)) = lowDensityCubic x S := by
    dsimp only [lowDensityCubic]
    field_simp
    ring
  nlinarith

private theorem oneHeadValue_ge_head {T x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hT : x ≤ T) :
    x ≤ oneHeadValue T (x ^ 2) := by
  have h := MultipartiteDust.objective_le_value_of_tests (lowerCoefficients 0)
    (lowerCoefficients_tests 0) (by norm_num [MultipartiteDust.penalty, lowerCoefficients])
    (fun _ : Fin 1 => x) (fun _ => hx) (T - x) (sub_nonneg.mpr hT)
  rw [lowerCoefficients_objective] at h
  norm_num only [zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at h
  rw [oneHeadValue_eq_finite, Real.sqrt_sq hx.1]
  exact h

theorem oneHeadValue_ge_third_edge_mass {T x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hT : x ≤ T) (hdensity : (T + (T ^ 2 - x ^ 2) / 2) / (1 + T) ^ 2 ≤ 3 / 8) :
    (T + (T ^ 2 - x ^ 2) / 2) / 3 ≤ oneHeadValue T (x ^ 2) := by
  by_cases hx1 : x = 1
  · subst x
    have hden : 0 < 1 + T := by linarith
    have hd := (div_le_iff₀ (sq_pos_of_pos hden)).mp hdensity
    have hE : T + (T ^ 2 - 1 ^ 2) / 2 ≤ 3 := by nlinarith
    exact (by linarith : (T + (T ^ 2 - (1 : ℝ) ^ 2) / 2) / 3 ≤ 1).trans
      (oneHeadValue_ge_head (by norm_num) hT)
  · have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    have hS : 0 ≤ T - x := sub_nonneg.mpr hT
    have hscalar := lower_bound_ge_third hx' hS (by simpa only [add_sub_cancel] using hdensity)
    have hactual := oneHeadValue_lower_bound hx' hS
    simpa only [add_sub_cancel] using hscalar.trans hactual

end Erdos1017.MultipartiteProfiles
