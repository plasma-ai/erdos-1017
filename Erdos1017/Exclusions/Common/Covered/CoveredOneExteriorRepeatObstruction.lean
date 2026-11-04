module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlocks
public import Erdos1017.SelectedModel.FullDiffuseCompletion

/-!
# Repeat obstruction for the one-exterior part

Every full `C`-repeat penalty exceeds the model's own multiplier penalty, by
constructing the neutral completion and its positive exact-density improvement,
and the two Boolean-state tests license penalty `t` for every natural repeat
count, so the own penalty is below `t`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredOneExterior

private theorem repeat_at_star_le_one (y : Coefficients) (hy : y ∈ feasible) (r n : ℕ) :
    repeatCharge (y 0) (y 1) (y 2) (y 3) (y 0) r n ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    have h := hy.2 false n
    simpa [repeatCharge, test_eq_value, constant, slope, TightCounts.value] using h
  · have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have ht := mul_nonneg (hy.1 0) (TightCounts.gap_nonneg 1 r)
    norm_num only [Nat.cast_one] at ht
    have hd := mul_nonneg (hy.1 2)
      (mul_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ (r : ℝ) - 1))
    have h := hy.2 true n
    simp only [test_eq_value, constant, slope, TightCounts.value, ite_true,
      LinearMap.sub_apply, LinearMap.proj_apply] at h
    unfold repeatCharge
    nlinarith only [h, ht, hd]

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every full C-repeat penalty exceeds the actual model's own multiplier
penalty. The neutral completion and its positive exact-density improvement
are constructed; neither a completed model nor a repeat obstruction is supplied. -/
theorem repeat_penalty_gt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label) (hC : 0 < μ (label ⁻¹' {2}))
    (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∀ D : ℝ, (∀ r n, repeatCharge (y 0) (y 1) (y 2) (y 3) D r n ≤ 1) → -m < D := by
  intro D hfull
  by_contra hnot
  have hD : D ≤ -m := le_of_not_gt hnot
  have hs := hW.strict_gap_structure hd hgap
  have hell : 0 ≤ -m := (neg_pos.mpr hs.multiplier_neg).le
  have hneutral (r n : ℕ) : repeatCharge (y 0) (y 1) (y 2) (y 3) (-m) r n ≤ 1 := by
    have hgap := mul_nonneg (sub_nonneg.mpr hD) (TightCounts.gap_nonneg 0 r)
    have h := hfull r n
    unfold repeatCharge at h ⊢
    norm_num only [Nat.cast_zero, sub_zero] at hgap
    nlinarith only [h, hgap]
  let C := label ⁻¹' {2}
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hCmeas : MeasurableSet C := hlabel (measurableSet_singleton 2)
  have hrep : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = blockAdjacency (label p.1) (label p.2) ∧
      Y p.1 p.2 = blockCharge y (label p.1) (label p.2) := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p ha hy
    have he := ha.symm.trans (hmom p).1
    change (if A p.1 p.2 = true then (1 : ℝ) else 0) =
      (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) at he
    constructor
    · cases hA : A p.1 p.2 <;>
        cases hG : blockAdjacency (label p.1) (label p.2) <;> simp_all
    · exact hy.trans (hmom p).2
  have hcompleted : ∀ᵐ p ∂μ.prod μ,
      FiniteArity.completeAdjacency A C p.1 p.2 =
        repeatedAdjacency (label p.1) (label p.2) ∧
      FiniteArity.completeCharge A Y C (-m) p.1 p.2 =
        repeatedCharge y (-m) (label p.1) (label p.2) := by
    filter_upwards [hrep] with p hp
    by_cases hCC : label p.1 = 2 ∧ label p.2 = 2
    · obtain ⟨hx, hz⟩ := hCC
      simp [FiniteArity.completeAdjacency, FiniteArity.completeCharge, C,
        repeatedAdjacency, repeatedCharge, hp.1, hx, hz, blockAdjacency]
    · have hmissing : ¬(label p.1 = 2 ∧ label p.2 = 2 ∧
          blockAdjacency (label p.1) (label p.2) = false) :=
        fun h => hCC ⟨h.1, h.2.1⟩
      simp [FiniteArity.completeAdjacency, FiniteArity.completeCharge, C,
        repeatedAdjacency, repeatedCharge, hp.1, hp.2, hCC, hmissing]
  have hcap (n : ℕ) : FiniteArity.FeasibleOrder μ
      (FiniteArity.completeAdjacency A C) (FiniteArity.completeCharge A Y C (-m)) n := by
    have hpairs := FiniteArity.ae_all_pairs μ n _ hcompleted
    filter_upwards [hpairs] with v hp hc
    have hc' : FiniteArity.TupleClique repeatedAdjacency (fun i => label (v i)) := by
      intro i j hij
      rw [← (hp i j hij).1]
      exact hc i j hij
    have ht := repeated_tupleCharge_le_one y hy (-m) hell hneutral (fun i => label (v i)) hc'
    have heq : FiniteArity.tupleCharge (FiniteArity.completeCharge A Y C (-m)) v =
        FiniteArity.tupleCharge (repeatedCharge y (-m)) (fun i => label (v i)) := by
      unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp only [hij, ite_true]
      · simp only [hij, ite_false, (hp i j hij).2]
    rw [heq]
    exact ht
  obtain ⟨u, hL, hQ⟩ := hW.exists_transverse_positive_direction hd hgap
  have hopt : CappedModel.objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hzero := ZeroCompletion.missingMass_eq_zero_of_full_optimum W hopt m
    (2 * (c - m * d)) hW.multiplier_mem hs.strict_support hW.stationary u hL hQ C hCmeas
    (fun n _ => hcap n)
  have hfill := ZeroCompletion.ae_complete_of_missingMass_eq_zero W m C hCmeas
    hs.strict_support hzero
  obtain ⟨z, hz, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hC.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hfill))
  obtain ⟨w, hw, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hC.ne'
    (ae_restrict_of_ae hrow)
  have h₁ := hp hz hw
  have h₀ : W.moment CappedColor.adjacency (z, w) = 0 := by
    have hz' : label z = 2 := hz
    have hw' : label w = 2 := hw
    simpa [hz', hw', blockAdjacency] using (hmom (z, w)).1
  change W.moment CappedColor.adjacency (z, w) = 1 at h₁
  linarith

/-- The original two Boolean-state tests already license penalty t for
every natural C-repeat count. Hence the actual own penalty is below t. -/
theorem star_gt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label) (hC : 0 < μ (label ⁻¹' {2}))
    (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    -m < y 0 :=
  repeat_penalty_gt_own_multiplier hW hd hgap label hlabel hC y hy hmom (y 0)
    (repeat_at_star_le_one y hy)

end Erdos1017.CoveredOneExterior
