module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleExceptionSchedule

/-!
# Limits of the degree and active envelopes of a schedule

This module defines the ideal normalized degree after `i` rounds at intensity
`θ` and explicit degree and active-vertex envelopes for a finite schedule, and
proves that as the tolerance vanishes and the degree scale grows the degree
envelopes converge to the ideal degree and the active fraction to its ideal
exponential decrease.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped Topology
open Filter

/-- Survival-factor convergence along a general degree-scale limit, including the joint
small-error and large-degree limit used to choose fixed matching parameters. -/
theorem survival_factor_limit_along {α : Type*} (F : Filter α) (θ z : ℝ)
    (D f : α → ℝ) (hD : Tendsto D F atTop) (hf : Tendsto f F (𝓝 z)) :
    Tendsto (fun x => (1 - θ / D x) ^ (D x * f x)) F (𝓝 (Real.exp (-θ * z))) := by
  have hlog := (Real.tendsto_mul_log_one_add_div_atTop (-θ)).comp hD
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hlog.mul hf)
  apply hexp.congr'
  filter_upwards [hD.eventually (eventually_gt_atTop (max θ 0))] with x hx
  have hDpos : 0 < D x := lt_of_le_of_lt (le_max_right _ _) hx
  have hθ : θ < D x := lt_of_le_of_lt (le_max_left _ _) hx
  have hbase : 0 < 1 - θ / D x := by
    have hdiv := (div_lt_one hDpos).mpr hθ
    linarith
  change Real.exp (D x * Real.log (1 + -θ / D x) * f x) = (1 - θ / D x) ^ (D x * f x)
  rw [Real.rpow_def_of_pos hbase]
  apply congrArg Real.exp
  simp only [neg_div, sub_eq_add_neg]
  ring

/-- The ideal normalized degree after `i` rounds with sampling intensity `θ`. -/
def idealDegree (r : ℕ) (θ : ℝ) (i : ℕ) : ℝ := Real.exp (-((r - 1 : ℕ) : ℝ) * θ * i)

/-- Explicit normalized degree envelopes, including the exposure and exceptional-neighbor
loss in each round. No regularity assertion is built into this scalar definition. -/
def degreeEnvelopes (r T : ℕ) (θ ε D : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1 - ε ^ (2 * T + 6), 1 + ε ^ (2 * T + 6))
  | i + 1 =>
    let z := degreeEnvelopes r T θ ε D i
    let q := 1 - (θ / idealDegree r θ i) / D
    let k : ℝ := (r - 1 : ℕ)
    ((z.1 - ε) * q ^ (D * (k * z.2)) - ε,
      z.2 * q ^ (D * (k * (z.1 - ε ^ (2 * T + 6)) - k ^ 2 * ε ^ (2 * T + 6))) + 2 * ε)

/-- For each fixed finite round count, the two degree envelopes converge to the same
positive ideal degree as tolerance vanishes and the degree scale grows. -/
theorem degreeEnvelopes_limit (r T : ℕ) (θ : ℝ) (i : ℕ) :
    Tendsto (fun x : ℝ × ℝ => (degreeEnvelopes r T θ x.1 x.2 i).1)
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (idealDegree r θ i)) ∧
    Tendsto (fun x : ℝ × ℝ => (degreeEnvelopes r T θ x.1 x.2 i).2)
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (idealDegree r θ i)) := by
  have hε : Tendsto (fun x : ℝ × ℝ => x.1) ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (0 : ℝ)) := tendsto_fst
  have hD : Tendsto (fun x : ℝ × ℝ => x.2) ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) atTop := tendsto_snd
  have hγ : Tendsto (fun x : ℝ × ℝ => x.1 ^ (2 * T + 6))
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hε.pow (2 * T + 6)
  induction i with
  | zero =>
    constructor
    · simpa [degreeEnvelopes, idealDegree] using tendsto_const_nhds.sub hγ
    · simpa [degreeEnvelopes, idealDegree] using tendsto_const_nhds.add hγ
  | succ i ih =>
    let d := idealDegree r θ i
    let k : ℝ := (r - 1 : ℕ)
    have hd : d ≠ 0 := (Real.exp_pos _).ne'
    have hloexp := survival_factor_limit_along ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (θ / d) (k * d)
      (fun x : ℝ × ℝ => x.2) (fun x => k * (degreeEnvelopes r T θ x.1 x.2 i).2)
      hD (ih.2.const_mul k)
    have hhiexp := survival_factor_limit_along ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (θ / d) (k * d)
      (fun x : ℝ × ℝ => x.2)
      (fun x => k * ((degreeEnvelopes r T θ x.1 x.2 i).1 - x.1 ^ (2 * T + 6)) -
        k ^ 2 * x.1 ^ (2 * T + 6)) hD
      (by simpa using ((ih.1.sub hγ).const_mul k).sub (hγ.const_mul (k ^ 2)))
    have hid : d * Real.exp (-(θ / d) * (k * d)) = idealDegree r θ (i + 1) := by
      have hexponent : -(θ / d) * (k * d) = -k * θ := by field_simp
      rw [hexponent]
      dsimp [d, k, idealDegree]
      rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    constructor
    · have h := ((ih.1.sub hε).mul hloexp).sub hε
      simpa only [degreeEnvelopes, sub_zero, d, k, hid] using h
    · have h := (ih.2.mul hhiexp).add (hε.const_mul 2)
      simpa only [degreeEnvelopes, mul_zero, add_zero, d, k, hid] using h

/-- The normalized active-vertex upper envelope for the same finite schedule. -/
def activeEnvelope (r T : ℕ) (θ R ε D : ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 =>
    activeEnvelope r T θ R ε D i *
      (1 - (θ / idealDegree r θ i) / D) ^ (D * (degreeEnvelopes r T θ ε D i).1) +
      (R + 2) ^ i * ε ^ (T + 2 - i) + ε

/-- The explicit exception envelopes vanish, so the active fraction converges to the
ideal exponential decrease at every round of the fixed schedule. -/
theorem activeEnvelope_limit (r T : ℕ) (θ R : ℝ) (i : ℕ) (hi : i ≤ T) :
    Tendsto (fun x : ℝ × ℝ => activeEnvelope r T θ R x.1 x.2 i)
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (Real.exp (-θ * i))) := by
  have hε : Tendsto (fun x : ℝ × ℝ => x.1)
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 (0 : ℝ)) := tendsto_fst
  have hD : Tendsto (fun x : ℝ × ℝ => x.2)
      ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) atTop := tendsto_snd
  induction i with
  | zero => simp [activeEnvelope]
  | succ i ih =>
    have hi' : i ≤ T := by omega
    have hprior := ih hi'
    have hdegree := (degreeEnvelopes_limit r T θ i).1
    have hsurvive := survival_factor_limit_along ((𝓝 (0 : ℝ)) ×ˢ (atTop : Filter ℝ))
      (θ / idealDegree r θ i) (idealDegree r θ i) (fun x : ℝ × ℝ => x.2)
      (fun x => (degreeEnvelopes r T θ x.1 x.2 i).1) hD hdegree
    have hd : idealDegree r θ i ≠ 0 := (Real.exp_pos _).ne'
    have hθ : -(θ / idealDegree r θ i) * idealDegree r θ i = -θ := by field_simp
    rw [hθ] at hsurvive
    have hexceptions := (exception_envelope_limit R T i hi').comp hε
    have h := ((hprior.mul hsurvive).add hexceptions).add hε
    have hexp : Real.exp (-θ * i) * Real.exp (-θ) = Real.exp (-θ * (i + 1 : ℕ)) := by
      rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    simpa only [activeEnvelope, Function.comp_apply, add_zero, hexp] using h

end Erdos1017.HypergraphNibble
