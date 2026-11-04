module

public import Erdos1017.Exclusions.Common.Covered.CoveredCBlockPerturbation
public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison
public import Erdos1017.Models.Selection.FullStationaryCompactness
public import Erdos1017.Exclusions.Common.CappedBinaryRepresentative
public import Erdos1017.Exclusions.Common.ConditionalCliqueAverages

/-!
# Exclusion of a positive C part in the five-region optimum

A five-region optimum in `FullStationaryClass` with the current count
constraints and a strict penalty gap cannot retain a positive `C` part:
two-sided scalar competitors force the mass balance, and the `C`-count tests are
derived from full feasibility by conditioning on positive fibers.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredC

open CappedModel TwoAtomCountGate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_five_label_row (label : Ω → Fin 5) (hlabel : Measurable label)
    (f : Fin 5 → ℝ) :
    (∫ w, f (label w) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have heq : (fun w => f (label w)) =
      fun w => ∑ i : Fin 5, (label ⁻¹' {i}).indicator (fun _ => f i) w := by
    funext w
    simp [Set.indicator_apply]
  rw [heq, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

/-- Each finite shifted row is derived from the own stationary event
on its genuine positive original fiber. -/
theorem finite_rows_of_fullStationaryClass {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (t z dc : ℝ)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x t z dc (label p.1) (label p.2)) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) *
      (blockCharge x t z dc i j - m * (if blockAdjacency i j = true then 1 else 0))) =
        2 * (c - m * d) := by
  have hrow : ∀ᵐ v ∂μ, (∫ w,
      blockCharge x t z dc (label v) (label w) - m *
        (if blockAdjacency (label v) (label w) = true then 1 else 0) ∂μ) =
      2 * (c - m * d) := by
    filter_upwards [hV.stationary] with v hv
    convert hv using 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      change blockCharge x t z dc (label v) (label w) - m *
        (if blockAdjacency (label v) (label w) = true then 1 else 0) =
          shiftedMoment V m (v, w)
      rw [shiftedMoment_eq, (hmom (v, w)).1, (hmom (v, w)).2])
  intro i
  obtain ⟨v, hv, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae hrow)
  change label v = i at hv
  rw [hv] at hgood
  exact (integral_five_label_row label hlabel (fun j =>
    blockCharge x t z dc i j - m * (if blockAdjacency i j = true then 1 else 0))).symm.trans hgood

/-- A bounded signed table with genuine full scalar tests obeys the
original own optimum on its same graph and probability law. -/
theorem scalar_objective_le_own_optimum {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hgraph : ∀ p : Ω × Ω, V.moment CappedColor.adjacency p =
      if blockAdjacency (label p.1) (label p.2) = true then 1 else 0)
    (x : Coefficients) (t z dc : ℝ)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge x t z dc (label a) (label b)) n) :
    FiniteCappedSamplingCost.physicalObjective μ
      (fun a b => blockCharge x t z dc (label a) (label b)) ≤ c := by
  have hpair : Measurable (fun p : Ω × Ω => (label p.1, label p.2)) :=
    (hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd)
  have hG := (measurable_of_countable (Function.uncurry blockAdjacency)).comp hpair
  have hY := (measurable_of_countable (Function.uncurry (blockCharge x t z dc))).comp hpair
  obtain ⟨hGsym, hYsym, hzero⟩ := block_properties x t z dc
  obtain ⟨B, hB⟩ := (Set.finite_range
    (fun ij : Fin 5 × Fin 5 => ‖blockCharge x t z dc ij.1 ij.2‖)).bddAbove
  have hbound :=
    FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
      (fun a b => blockAdjacency (label a) (label b)) (fun a b => hGsym _ _) hG
      (fun a b => blockCharge x t z dc (label a) (label b)) hY B
      (fun p => hB ⟨(label p.1, label p.2), rfl⟩)
      (Eventually.of_forall (fun p => hYsym (label p.1) (label p.2)))
      (Eventually.of_forall (fun p hp => hzero (label p.1) (label p.2) hp)) hfull
  have hd : FiniteCappedSamplingCost.physicalDensity μ
      (fun a b => blockAdjacency (label a) (label b)) = d := by
    rw [← hV.density_eq]
    unfold density FiniteCappedSamplingCost.physicalDensity
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hgraph p).symm))
  simpa only [hd, ← hV.optimal] using hbound

/-- Genuine two-sided full scalar competitors force the original mass
balance. No new capped model or competitor stationarity is required. -/
theorem mass_balance_of_fullStationaryClass {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hC : 0 < μ (label ⁻¹' {2})) (x : Coefficients) (hx : x ∈ feasible)
    (t z dc s0 m0 : ℝ) (ht : t = 1 - s0) (hs0 : 0 < s0) (hm0 : s0 < m0)
    (hz : 0 < z) (hdc : 0 < dc) (ha : x 0 - z ≤ s0) (hb : x 1 - dc ≤ s0)
    (hp : m0 ≤ x 2) (hq : m0 ≤ x 3) (hr : m0 ≤ x 4)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x t z dc (label p.1) (label p.2)) :
    μ.real (label ⁻¹' {1}) = μ.real (label ⁻¹' {3}) + μ.real (label ⁻¹' {4}) := by
  have hc : 0 < μ.real (label ⁻¹' {2}) := ENNReal.toReal_pos hC.ne' (measure_ne_top _ _)
  apply mass_balance_of_perturb_optimal _ _ _ _ _ hc
    (perturbRadius_pos s0 m0 z dc hs0 hm0 hz hdc)
  intro eps heps
  have hcomp := scalar_objective_le_own_optimum hV label hlabel (fun p => (hmom p).1)
    x (t + eps) (z + eps) (dc + eps)
    (perturb_full_scalar_tests x hx t z dc s0 m0 ht hs0 hm0 ha hb hp hq hr eps heps μ label)
  have hobj : FiniteCappedSamplingCost.physicalObjective μ
      (fun a b => blockCharge x t z dc (label a) (label b)) = c := by
    rw [← hV.objective_eq]
    unfold CappedModel.objective FiniteCappedSamplingCost.physicalObjective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
  rw [perturb_physicalObjective label hlabel, hobj] at hcomp
  linarith only [hcomp]

/-- An actual own five-region optimum with the stated current count
constraints and strict penalty gap cannot retain a positive C part. -/
theorem not_fullStationaryClass {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (t z dc : ℝ) (ht1 : t < 1) (hz : 0 < z) (hdc : 0 < dc)
    (hp : 1 - t < x 2) (hq : 1 - t < x 3) (hr : 1 - t < x 4) (hv : -m < x 1)
    (hcount : ∀ k l, countCharge t (x 0 - z) (x 1 - dc) (x 2) (x 3) (x 4) k l ≤ 1)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x t z dc (label p.1) (label p.2)) :
    False := by
  have hR := hcount 1 0
  have hE := hcount 0 1
  norm_num [countCharge] at hR hE
  have hmin : 1 - t < min (x 2) (min (x 3) (x 4)) := lt_min hp (lt_min hq hr)
  have hmass := mass_balance_of_fullStationaryClass hV label hlabel (hpositive 2) x hx
    t z dc (1 - t) (min (x 2) (min (x 3) (x 4))) (by ring) (by linarith) hmin hz hdc
    (by linarith) (by linarith) (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hmom
  have hrows := finite_rows_of_fullStationaryClass hV label hlabel hpositive x t z dc hmom
  have hA := hrows 0
  have hC := hrows 2
  norm_num [blockAdjacency, blockCharge, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
    at hA hC
  have hrow : μ.real (label ⁻¹' {1}) * (1 - t) =
      μ.real (label ⁻¹' {3}) * (x 0 - z) + μ.real (label ⁻¹' {4}) * (-m - dc) := by
    nlinarith only [hA, hC]
  exact not_balanced_rows _ _ _ _ _ _ _ _ _ measureReal_nonneg
    (ENNReal.toReal_pos (hpositive 4).ne' (measure_ne_top _ _)) hmass hrow
    (by linarith) (by linarith) hv

/-- The current C-count system is derived from the actual fully feasible
model by independently conditioning on its positive original fibers. -/
theorem count_tests_of_fullStationaryClass {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (t z dc : ℝ)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x t z dc (label p.1) (label p.2)) :
    ∀ k l, countCharge t (x 0 - z) (x 1 - dc) (x 2) (x 3) (x 4) k l ≤ 1 := by
  let G : Ω × Ω → Bool := fun p => blockAdjacency (label p.1) (label p.2)
  have hG : Measurable G :=
    (measurable_of_countable (Function.uncurry blockAdjacency)).comp
      ((hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd))
  obtain ⟨Y, hY, _, hbox, _, hyeq, hfull⟩ :=
    BinaryRepresentative.exists_scalar_representative V hV.full G hG
      (fun a b => (block_properties x t z dc).1 _ _)
      (Eventually.of_forall (fun p => (hmom p).1))
  have hbound (a b : Ω) : ‖Y (a, b)‖ ≤ 3 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(hbox (a, b)).1, (hbox (a, b)).2.trans (by norm_num)⟩
  have hcoeff (i j : Fin 5) :
      (∫ p, Y p ∂(cond μ (label ⁻¹' {i})).prod (cond μ (label ⁻¹' {j}))) =
        blockCharge x t z dc i j := by
    let : IsProbabilityMeasure (cond μ (label ⁻¹' {i})) :=
      cond_isProbabilityMeasure (hpositive i).ne'
    let : IsProbabilityMeasure (cond μ (label ⁻¹' {j})) :=
      cond_isProbabilityMeasure (hpositive j).ne'
    have heq : ∀ᵐ p ∂(cond μ (label ⁻¹' {i})).prod (cond μ (label ⁻¹' {j})),
        Y p = blockCharge x t z dc i j := by
      filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hyeq,
        Measure.quasiMeasurePreserving_fst.ae
          (ae_cond_mem (hlabel (measurableSet_singleton i))),
        Measure.quasiMeasurePreserving_snd.ae
          (ae_cond_mem (hlabel (measurableSet_singleton j)))] with p hp hi hj
      change label p.1 = i at hi
      change label p.2 = j at hj
      rw [hp]
      change V.moment CappedColor.charge p = _
      rw [(hmom p).2, hi, hj]
    rw [integral_congr_ae heq, integral_const, probReal_univ, smul_eq_mul, one_mul]
  intro k l
  have htest := FiniteArity.conditional_multiplicity_average_le_one
    (fun i : Fin 5 => label ⁻¹' {i}) (fun i => hlabel (measurableSet_singleton i))
    hpositive (fun a b => G (a, b)) (fun a b => Y (a, b)) hY 3 hbound
    (![0, 1, 1, k, l] : Fin 5 → ℕ) (hfull _)
    (by
      intro i hi
      fin_cases i <;> first
      | (norm_num at hi; done)
      | exact Eventually.of_forall (fun p hp hq => by
          change label p.1 = _ at hp
          change label p.2 = _ at hq
          simp [G, hp, hq, blockAdjacency]))
    (by
      intro i j hij hi hj
      fin_cases i <;> fin_cases j <;> first
      | (norm_num at hi; done)
      | (norm_num at hj; done)
      | (norm_num at hij; done)
      | exact Eventually.of_forall (fun p hp hq => by
          change label p.1 = _ at hp
          change label p.2 = _ at hq
          simp [G, hp, hq, blockAdjacency]))
  change FiniteArity.multiplicityCharge
    (fun i j => ∫ p, Y p ∂(cond μ (label ⁻¹' {i})).prod (cond μ (label ⁻¹' {j})))
      (![0, 1, 1, k, l] : Fin 5 → ℕ) ≤ 1 at htest
  simp_rw [hcoeff] at htest
  have heq : FiniteArity.multiplicityCharge (blockCharge x t z dc)
      (![0, 1, 1, k, l] : Fin 5 → ℕ) =
      countCharge t (x 0 - z) (x 1 - dc) (x 2) (x 3) (x 4) k l := by
    simp [FiniteArity.multiplicityCharge, blockCharge, countCharge, Fin.sum_univ_succ]
    ring
  rwa [heq] at htest

/-- The actual own-model exclusion derives its current C-count tests from
full feasibility. The signed C-free count system remains explicit; no C-count,
perturbation or stationary-row hypothesis is used. -/
theorem not_fullStationaryClass_of_moments {V : Model Ω μ} {m d c : ℝ}
    (hV : FullStationaryClass d c V m) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (t z dc : ℝ) (ht1 : t < 1) (hz : 0 < z) (hdc : 0 < dc)
    (hp : 1 - t < x 2) (hq : 1 - t < x 3) (hr : 1 - t < x 4) (hv : -m < x 1)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x t z dc (label p.1) (label p.2)) :
    False :=
  not_fullStationaryClass hV label hlabel hpositive x hx t z dc ht1 hz hdc hp hq hr hv
    (count_tests_of_fullStationaryClass hV label hlabel hpositive x t z dc hmom) hmom

end Erdos1017.CoveredC
