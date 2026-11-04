module

public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorBlocks
public import Erdos1017.SelectedModel.FullDiffuseCompletion

/-!
# Repeat obstruction for the two-exterior parts

Both secondary parts obey the full-repeat obstruction with the model's own
multiplier, the Boolean tests make each star exceed the own multiplier penalty,
and strict support on the positive `C1`-`C2` block puts the cross penalty below
it, so neither affordable repeat can occur.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredTwoExterior

open VertexClassification

private theorem repeat_at_star_le_one (y : Coefficients) (hy : y ∈ feasible)
    (r b n : ℕ) (hb : b ≤ 1) :
    Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
      (y 0) r b n ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    simpa [Repeat.oneSidedCharge, Repeat.pairs] using
      VertexRepeat.original_boolean_feasibility y hy 0 b n (by norm_num) hb
  · have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have ht := mul_nonneg (hy.1 0) (TightCounts.gap_nonneg 1 r)
    norm_num only [Nat.cast_one] at ht
    have hc := mul_nonneg (mul_nonneg (hy.1 3) (Nat.cast_nonneg b))
      (by linarith : 0 ≤ (r : ℝ) - 1)
    have hd := mul_nonneg (mul_nonneg (hy.1 4) (Nat.cast_nonneg n))
      (by linarith : 0 ≤ (r : ℝ) - 1)
    have h := VertexRepeat.original_boolean_feasibility y hy 1 b n (by norm_num) hb
    unfold Repeat.oneSidedCharge Repeat.pairs at h ⊢
    norm_num only [Nat.cast_one, one_mul, mul_one, sub_self, mul_zero, zero_div,
      sub_zero] at h
    nlinarith only [h, ht, hc, hd]

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every full C-repeat penalty exceeds the actual model's own multiplier
penalty. The neutral completion and its positive exact-density improvement
are constructed; neither a completed model nor a repeat obstruction is supplied. -/
private theorem first_repeat_penalty_gt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label) (hC : 0 < μ (label ⁻¹' {2}))
    (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∀ D : ℝ, (∀ r b n : ℕ, b ≤ 1 →
      Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) D r b n ≤ 1) →
        -m < D := by
  intro D hfull
  by_contra hnot
  have hD : D ≤ -m := le_of_not_gt hnot
  have hs := hW.strict_gap_structure hd hgap
  have hell : 0 ≤ -m := (neg_pos.mpr hs.multiplier_neg).le
  have hneutral (r b n : ℕ) (hb : b ≤ 1) :
      Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
        (-m) r b n ≤ 1 := by
    have hgap := mul_nonneg (sub_nonneg.mpr hD) (TightCounts.gap_nonneg 0 r)
    have h := hfull r b n hb
    unfold Repeat.oneSidedCharge Repeat.pairs at h ⊢
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
        repeatedAdjacency 2 (label p.1) (label p.2) ∧
      FiniteArity.completeCharge A Y C (-m) p.1 p.2 =
        repeatedCharge y 2 (-m) (label p.1) (label p.2) := by
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
    have hc' : FiniteArity.TupleClique (repeatedAdjacency 2) (fun i => label (v i)) := by
      intro i j hij
      rw [← (hp i j hij).1]
      exact hc i j hij
    have ht := repeated_tupleCharge_le_one y hy (-m) hell hneutral (fun i => label (v i)) hc'
    have heq : FiniteArity.tupleCharge (FiniteArity.completeCharge A Y C (-m)) v =
        FiniteArity.tupleCharge (repeatedCharge y 2 (-m)) (fun i => label (v i)) := by
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

/-- Both secondary types obey the full-repeat obstruction for this same
actual model and its own multiplier. Coefficient and label swaps are explicit;
no sign restriction on the repeat penalty is required. -/
theorem repeat_penalties_gt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    ∀ y : Coefficients, (y = x ∨ y = VertexRepeat.swap x) → ∀ D : ℝ,
      (∀ r b n : ℕ, b ≤ 1 →
        Repeat.oneSidedCharge (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) D r b n ≤ 1) →
          -m < D := by
  intro y hy
  rcases hy with hy | hy
  · subst y
    exact first_repeat_penalty_gt_own_multiplier hW hd hgap label hlabel
      (hpositive 2) x hx hmom
  · subst y
    let label' := fun z => swapLabel (label z)
    have hlabel' : Measurable label' := (measurable_of_countable swapLabel).comp hlabel
    have hCeq : label' ⁻¹' {2} = label ⁻¹' {3} := by
      ext z
      change swapLabel (label z) = 2 ↔ label z = 3
      generalize label z = i
      fin_cases i <;> decide
    have hC : 0 < μ (label' ⁻¹' {2}) := hCeq ▸ hpositive 3
    have hmom' : ∀ p : Ω × Ω,
        W.moment CappedColor.adjacency p =
          (if blockAdjacency (label' p.1) (label' p.2) = true then 1 else 0) ∧
        W.moment CappedColor.charge p =
          blockCharge (VertexRepeat.swap x) (label' p.1) (label' p.2) := by
      intro p
      constructor
      · simpa only [label', (block_swap x (label p.1) (label p.2)).1] using (hmom p).1
      · exact (hmom p).2.trans (block_swap x (label p.1) (label p.2)).2.symm
    exact first_repeat_penalty_gt_own_multiplier hW hd hgap label' hlabel' hC
      (VertexRepeat.swap x) (VertexRepeat.swap_feasible x hx) hmom'

/-- The old Boolean tests internally license each own star as its repeat
penalty, so both actual star coefficients exceed the own multiplier penalty. -/
theorem stars_gt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    -m < x 0 ∧ -m < x 1 := by
  have h := repeat_penalties_gt_own_multiplier hW hd hgap label hlabel hpositive x hx hmom
  refine ⟨h x (Or.inl rfl) (x 0) (repeat_at_star_le_one x hx), ?_⟩
  have hs := h (VertexRepeat.swap x) (Or.inr rfl) ((VertexRepeat.swap x) 0)
    (repeat_at_star_le_one (VertexRepeat.swap x) (VertexRepeat.swap_feasible x hx))
  simpa [VertexRepeat.swap] using hs

/-- Strict support on the positive original C1-C2 block puts its cross
penalty below the own penalty. Thus neither affordable repeat can occur. -/
theorem no_affordable_repeat {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    ¬(VertexRepeat.HasRepeat x ∨ VertexRepeat.HasRepeat (VertexRepeat.swap x)) := by
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  obtain ⟨z, hz, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpositive 2).ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hs))
  obtain ⟨w, hw, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpositive 3).ne'
    (ae_restrict_of_ae hrow)
  have hz' : label z = 2 := hz
  have hw' : label w = 3 := hw
  have hadj : W.moment CappedColor.adjacency (z, w) = 1 := by
    simpa [hz', hw', blockAdjacency] using (hmom (z, w)).1
  have hcharge : W.moment CappedColor.charge (z, w) = -x 3 := by
    simpa [hz', hw', blockCharge] using (hmom (z, w)).2
  have hshift : 0 < shiftedMoment W m (z, w) := by
    by_contra h
    simp [hadj, h] at hp
  have hcross : x 3 < -m := by
    rw [shiftedMoment_eq, hadj, hcharge] at hshift
    linarith
  have hbound := repeat_penalties_gt_own_multiplier hW hd hgap label hlabel hpositive x hx hmom
  rintro (⟨D, _, hD, hfull⟩ | ⟨D, _, hD, hfull⟩)
  · have hlt := hbound x (Or.inl rfl) D hfull
    linarith
  · have hlt := hbound (VertexRepeat.swap x) (Or.inr rfl) D hfull
    have hD' : D ≤ x 3 := by simpa [VertexRepeat.swap] using hD
    linarith

end Erdos1017.CoveredTwoExterior
