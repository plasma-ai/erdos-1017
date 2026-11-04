module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleScheduleLimit

/-!
# Fixed thresholds for the nibble schedule

This module defines the normalized small-error budget of a simultaneous round
and shows that a fixed positive tolerance and fixed order and degree thresholds
work for every later degree scale and order, preserving the quantifier order
required by the matching theorem (`exists_schedule_thresholds`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped Topology
open Filter

/-- The error terms in the simultaneous-round probability budget after normalization. -/
def smallErrorBudget (r T : ℕ) (θ C ε : ℝ) (i : ℕ) : ℝ :=
  (θ / idealDegree r θ i) * ε ^ (2 * T + 4) +
    (θ / idealDegree r θ i) * (r : ℝ) ^ 2 * C ^ 2 * ε ^ (T + 2)

/-- Fixed positive tolerance and fixed order/degree thresholds work for every later degree
scale and order. This preserves the matching theorem's required quantifier order. -/
theorem exists_schedule_thresholds (r T : ℕ) (θ C β : ℝ) (hθ : 0 < θ)
    (hβ : Real.exp (-θ * T) < β) :
    ∃ ε D₀ N₀ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < D₀ ∧ 0 < N₀ ∧
      ∀ D ≥ D₀, ∀ N ≥ N₀,
        (∀ i : Fin (T + 1), 0 < (degreeEnvelopes r T θ ε D i).1 ∧
          0 < (degreeEnvelopes r T θ ε D i).2) ∧
        (∀ i : Fin T, 0 < (θ / idealDegree r θ i) / D ∧
          (θ / idealDegree r θ i) / D < 1 ∧
          smallErrorBudget r T θ C ε i < 1 / 4 ∧
          (θ / idealDegree r θ i) * C / (ε ^ 2 * N) < 1 / 4) ∧
        activeEnvelope r T θ (r * C) ε D T < β := by
  let F : Filter (ℝ × ℝ) := (𝓝 (0 : ℝ)) ×ˢ atTop
  have hε : Tendsto (fun x : ℝ × ℝ => x.1) F (𝓝 (0 : ℝ)) := tendsto_fst
  have hD : Tendsto (fun x : ℝ × ℝ => x.2) F atTop := tendsto_snd
  have hdeg : ∀ᶠ x : ℝ × ℝ in F, ∀ i : Fin (T + 1),
      0 < (degreeEnvelopes r T θ x.1 x.2 i).1 ∧ 0 < (degreeEnvelopes r T θ x.1 x.2 i).2 := by
    apply eventually_all.mpr
    intro i
    have hd : 0 < idealDegree r θ i := Real.exp_pos _
    exact ((degreeEnvelopes_limit r T θ i).1.eventually (lt_mem_nhds hd)).and
      ((degreeEnvelopes_limit r T θ i).2.eventually (lt_mem_nhds hd))
  have hprob : ∀ᶠ x : ℝ × ℝ in F, ∀ i : Fin T, (θ / idealDegree r θ i) / x.2 < 1 := by
    apply eventually_all.mpr
    intro i
    have hlim : Tendsto (fun x : ℝ × ℝ => (θ / idealDegree r θ i) / x.2) F (𝓝 0) :=
      tendsto_const_nhds.div_atTop hD
    exact hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbudget : ∀ᶠ x : ℝ × ℝ in F, ∀ i : Fin T, smallErrorBudget r T θ C x.1 i < 1 / 4 := by
    apply eventually_all.mpr
    intro i
    have hcont : Continuous (fun ε : ℝ => smallErrorBudget r T θ C ε i) := by
      unfold smallErrorBudget
      fun_prop
    have hlim : Tendsto (fun x : ℝ × ℝ => smallErrorBudget r T θ C x.1 i) F (𝓝 0) := by
      simpa [smallErrorBudget, Function.comp_def] using (hcont.tendsto 0).comp hε
    exact hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hactive : ∀ᶠ x : ℝ × ℝ in F, activeEnvelope r T θ (r * C) x.1 x.2 T < β :=
    (activeEnvelope_limit r T θ (r * C) T le_rfl).eventually (gt_mem_nhds hβ)
  have hsmall : ∀ᶠ x : ℝ × ℝ in F, x.1 < 1 := hε.eventually (gt_mem_nhds (by norm_num))
  have hall := hdeg.and (hprob.and (hbudget.and (hactive.and hsmall)))
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.mp hall
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hpa
  let ε := ρ / 2
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hpaε : pa ε := hball (by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hεpos]
    dsimp [ε]
    linarith)
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.mp hpb
  let D₀ := max D₁ 1
  have hD₀ : 0 < D₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have horder : ∀ᶠ N : ℝ in atTop, ∀ i : Fin T,
      (θ / idealDegree r θ i) * C / (ε ^ 2 * N) < 1 / 4 := by
    apply eventually_all.mpr
    intro i
    have hlim : Tendsto (fun N : ℝ => ((θ / idealDegree r θ i) * C / ε ^ 2) / N)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hlim' : Tendsto (fun N : ℝ => (θ / idealDegree r θ i) * C / (ε ^ 2 * N))
        atTop (𝓝 0) := by simpa only [div_div] using hlim
    exact hlim'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp horder
  let N₀ := max N₁ 1
  have hN₀ : 0 < N₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hεlt : ε < 1 := (hpab hpaε (hD₁ D₀ (le_max_left _ _))).2.2.2.2
  refine ⟨ε, D₀, N₀, hεpos, hεlt, hD₀, hN₀, ?_⟩
  intro D hDmin N hNmin
  have hresult := hpab hpaε (hD₁ D ((le_max_left _ _).trans hDmin))
  refine ⟨hresult.1, ?_, hresult.2.2.2.1⟩
  intro i
  exact ⟨div_pos (div_pos hθ (Real.exp_pos _)) (hD₀.trans_le hDmin),
    hresult.2.1 i, hresult.2.2.1 i, hN₁ N ((le_max_left _ _).trans hNmin) i⟩

end Erdos1017.HypergraphNibble
