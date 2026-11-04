module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassInternalTuran

/-!
# Clique orders inside a positive class

On a positive class the restricted clique presence is nonnegative, vanishes
exactly when the normalized-class sampled test does, is positive at every order
below a positive one, and the positive orders are either unbounded or end at a
last positive order followed by a zero test.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem restrictedCliquePresence_nonneg (W : Model Ω μ) (s : Set Ω) (n : ℕ) :
    0 ≤ restrictedCliquePresence W s n := by
  exact integral_nonneg (fun _ => integral_nonneg cliquePresence_nonneg)

/-- On a positive class, a raw zero clique integral is equivalent to the
zero test under the actual normalized-class sampled color law. -/
theorem restrictedCliquePresence_eq_zero_iff (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ s)] (n : ℕ) :
    restrictedCliquePresence W s n = 0 ↔
      (∫ c, cliquePresence c ∂(sampledColorLaw (conditionOn W s hpos) n :
        Measure (CliquePair n → CappedColor))) = 0 := by
  refine ⟨integral_conditionOn_cliquePresence_eq_zero W s hpos n, ?_⟩
  intro hzero
  let F : C(CliquePair n → CappedColor, ℝ) :=
    ⟨cliquePresence, continuous_cliquePresence n⟩
  let inner : (Fin n → Ω) → ℝ := fun x => ∫ c, F c ∂cliqueLaw W x
  have hsm : StronglyMeasurable inner := by
    change StronglyMeasurable (fun x => ∫ c, F c ∂cliqueKernel W n x)
    exact F.continuous.stronglyMeasurable.integral_kernel
  have hbound : ∀ x, ‖inner x‖ ≤ ‖F‖ := by
    intro x
    have h := norm_integral_le_of_norm_le_const
      (μ := cliqueLaw W x) (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
    simpa using h
  have hint : Integrable inner
      (Measure.pi (fun _ : Fin n => ProbabilityTheory.cond μ s)) :=
    Integrable.of_bound hsm.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall hbound)
  have hnonneg : ∀ x, 0 ≤ inner x :=
    fun _ => integral_nonneg cliquePresence_nonneg
  have hnorm : (∫ x, inner x
      ∂Measure.pi (fun _ : Fin n => ProbabilityTheory.cond μ s)) = 0 := by
    change (∫ c, F c ∂(sampledColorLaw (conditionOn W s hpos) n :
      Measure (CliquePair n → CappedColor))) = 0 at hzero
    rw [integral_sampledColorLaw] at hzero
    exact hzero
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hnorm
  have hac : μ.restrict s ≪ ProbabilityTheory.cond μ s := by
    rw [ProbabilityTheory.cond]
    exact Measure.absolutelyContinuous_smul (by simp [measure_ne_top])
  have hraw := (DecoratedKernel.pi_absolutelyContinuous hac n).ae_le hae
  unfold restrictedCliquePresence
  rw [Measure.restrict_pi_pi]
  exact integral_eq_zero_of_ae hraw

/-- A zero lower-order clique test forces every larger sampled clique
test to vanish, using the exact subtuple law. -/
theorem integral_cliquePresence_eq_zero_of_lower (W : Model Ω μ)
    (j n : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hzero : (∫ c, cliquePresence c ∂(sampledColorLaw W j :
      Measure (CliquePair j → CappedColor))) = 0) :
    (∫ c, cliquePresence c ∂(sampledColorLaw W n :
      Measure (CliquePair n → CappedColor))) = 0 := by
  classical
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hae := ae_sampled_zero_subcliques W i n hzero
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with c hc
  let e : Fin (i + 1) ↪o Fin n := Fin.castLEOrderEmb hjn
  have hsub := hc e
  unfold cliquePresence at hsub ⊢
  obtain ⟨p, _, hp⟩ := Finset.prod_eq_zero_iff.mp hsub
  exact Finset.prod_eq_zero (Finset.mem_univ (pairEmbedding e p)) hp

/-- Positive old clique density supplies every smaller positive order;
there is no supplied successful tuple or finite maximal-order premise. -/
theorem restrictedCliquePresence_pos_of_le (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s) (j n : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hn : 0 < restrictedCliquePresence W s n) :
    0 < restrictedCliquePresence W s j := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
    conditioned_probability s hpos
  by_contra hjpos
  have hjzero : restrictedCliquePresence W s j = 0 :=
    le_antisymm (le_of_not_gt hjpos) (restrictedCliquePresence_nonneg W s j)
  have hzero := integral_cliquePresence_eq_zero_of_lower
    (conditionOn W s hpos) j n hj hjn
    ((restrictedCliquePresence_eq_zero_iff W s hpos j).mp hjzero)
  have hnzero := (restrictedCliquePresence_eq_zero_iff W s hpos n).mpr hzero
  linarith

/-- A positive class always supports one old vertex. -/
theorem restrictedCliquePresence_one_pos (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s) : 0 < restrictedCliquePresence W s 1 := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
    conditioned_probability s hpos
  have : IsEmpty (CliquePair 1) := ⟨fun p => by
    have hi := p.val.1.isLt
    have hj := p.val.2.isLt
    have hij := p.property
    omega⟩
  by_contra hnot
  have hzero : restrictedCliquePresence W s 1 = 0 :=
    le_antisymm (le_of_not_gt hnot) (restrictedCliquePresence_nonneg W s 1)
  have hnorm := (restrictedCliquePresence_eq_zero_iff W s hpos 1).mp hzero
  simp [cliquePresence] at hnorm

/-- The old positive clique orders are either unbounded or have a genuine
last positive order followed by a zero test. -/
theorem restrictedCliquePresence_order_dichotomy (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s) :
    (∀ n, 1 ≤ n → 0 < restrictedCliquePresence W s n) ∨
      ∃ k, 1 ≤ k ∧ 0 < restrictedCliquePresence W s k ∧
        restrictedCliquePresence W s (k + 1) = 0 := by
  classical
  by_cases hzero : ∃ n, 1 ≤ n ∧ restrictedCliquePresence W s n = 0
  · let N := Nat.find hzero
    have hN : 1 ≤ N ∧ restrictedCliquePresence W s N = 0 := Nat.find_spec hzero
    have hNtwo : 2 ≤ N := by
      have hone := restrictedCliquePresence_one_pos W s hpos
      by_contra hnot
      have heq : N = 1 := by omega
      rw [heq] at hN
      linarith [hN.2]
    let k := N - 1
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hkpos : 0 < restrictedCliquePresence W s k := by
      by_contra hnot
      have hkzero : restrictedCliquePresence W s k = 0 :=
        le_antisymm (le_of_not_gt hnot) (restrictedCliquePresence_nonneg W s k)
      have hmin : N ≤ k := Nat.find_min' hzero ⟨hk, hkzero⟩
      dsimp [k] at hmin
      omega
    refine Or.inr ⟨k, hk, hkpos, ?_⟩
    have hnext : k + 1 = N := by dsimp [k]; omega
    rw [hnext]
    exact hN.2
  · refine Or.inl ?_
    intro n hn
    by_contra hnot
    exact hzero ⟨n, hn,
      le_antisymm (le_of_not_gt hnot) (restrictedCliquePresence_nonneg W s n)⟩

end Erdos1017.CappedModel
