module

public import Erdos1017.Exclusions.Common.FiniteBlockScalarModel
public import Erdos1017.Exclusions.Common.FiniteChargeBoundary
public import Erdos1017.Exclusions.Common.DeterministicFullStationarity
public import Erdos1017.Exclusions.Common.CappedBinaryRepresentative

/-!
# Charge box for finite block optima

Every full scalar optimum on the same finite positive-block graph as a
deterministic strict-gap optimum has charge strictly above minus three on each
present block.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

private theorem block_property_of_ae {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (q : Ω → ι)
    (hpositive : ∀ i, 0 < μ (q ⁻¹' {i})) (P : ι → ι → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (q p.1) (q p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨x, hx, hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpx)
  exact hx ▸ hz ▸ hpz

private theorem full_scalar_tests_congr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : Ω → Ω → Bool) (Y Z : Ω → Ω → ℝ)
    (hYZ : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Z p.1 p.2)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ n, FiniteArity.FeasibleOrder μ A Z n := by
  intro n
  have hpairs := FiniteArity.ae_all_pairs μ n _ hYZ
  filter_upwards [hfull n, hpairs] with v hv hp hc
  have heq : FiniteArity.tupleCharge Z v = FiniteArity.tupleCharge Y v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp only [hij, ite_true]
    · simp only [hij, ite_false, hp i j hij]
  rw [heq]
  exact hv hc

private theorem full_scalar_tests_convex {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : Ω → Ω → Bool) (Y Z : Ω → Ω → ℝ)
    (hY : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (hZ : ∀ n, FiniteArity.FeasibleOrder μ A Z n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ n, FiniteArity.FeasibleOrder μ A (fun x z => (1 - t) * Y x z + t * Z x z) n := by
  intro n
  filter_upwards [hY n, hZ n] with v hvY hvZ hc
  have hline : FiniteArity.tupleCharge (fun x z => (1 - t) * Y x z + t * Z x z) v =
      (1 - t) * FiniteArity.tupleCharge Y v + t * FiniteArity.tupleCharge Z v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    have hpoint (i j : Fin n) :
        (if i = j then 0 else (1 - t) * Y (v i) (v j) + t * Z (v i) (v j)) =
        (1 - t) * (if i = j then 0 else Y (v i) (v j)) +
          t * (if i = j then 0 else Z (v i) (v j)) := by
      by_cases hij : i = j <;> simp [hij]
    simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hline]
  have hle := add_le_add
    (mul_le_mul_of_nonneg_left (hvY hc) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hvZ hc) ht.1)
  nlinarith only [hle]

private theorem ae_charge_le_one_of_order_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x z, A x z = A z x) (hYsym : ∀ x z, Y x z = Y z x)
    (hfull : FiniteArity.FeasibleOrder μ A Y 2) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = true → Y p.1 p.2 ≤ 1 := by
  have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
    (measurePreserving_finTwoArrow μ)
  filter_upwards [hmp.quasiMeasurePreserving.ae hfull] with p hp hA
  have hc : FiniteArity.TupleClique A ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have ht := hp hc
  change FiniteArity.tupleCharge Y ![p.1, p.2] ≤ 1 at ht
  simpa [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
    Fin.sum_univ_two, hYsym p.2 p.1] using ht

variable {Ω ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every full scalar optimum on the same finite positive-block graph as
an actual deterministic strict-gap optimum lies strictly above minus three
on each present block. A first boundary model constructs its own stationary
record; no original multiplier is assigned to that edited model. -/
theorem finite_block_charges_mem_Ioc_of_full_scalar_optimum (W₀ : Model Ω μ)
    (hW₀ : FullFeasible W₀)
    (hopt₀ : objective W₀ = FractionalGraph.densityLimit (density W₀))
    (hphysical₀ : ∀ p, ∀ᵐ z ∂W₀.kernel p,
      CappedColor.charge z = conditionalCharge W₀ p * CappedColor.adjacency z)
    (hd : density W₀ ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W₀) < objective W₀)
    (q : Ω → ι) (hq : Measurable q) (hpositive : ∀ i, 0 < μ (q ⁻¹' {i}))
    (G : ι → ι → Bool) (hGsym : ∀ i j, G i j = G j i) (y₀ y₁ : ι → ι → ℝ)
    (hentry : ∀ᵐ p ∂μ.prod μ,
      W₀.moment CappedColor.adjacency p = (if G (q p.1) (q p.2) = true then 1 else 0) ∧
      W₀.moment CappedColor.charge p = y₀ (q p.1) (q p.2))
    (h₁sym : ∀ i j, y₁ i j = y₁ j i)
    (h₁zero : ∀ i j, G i j = false → y₁ i j = 0)
    (h₁full : ∀ n, FiniteArity.FeasibleOrder μ
      (fun x z => G (q x) (q z)) (fun x z => y₁ (q x) (q z)) n)
    (h₁cost : FiniteCappedSamplingCost.physicalObjective μ (fun x z => y₁ (q x) (q z)) =
      objective W₀) : ∀ i j, G i j = true → y₁ i j ∈ Ioc (-3 : ℝ) 1 := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hentry
  have h₀sym : ∀ i j, y₀ i j = y₀ j i := by
    apply block_property_of_ae q hpositive
    filter_upwards [hentry, hswap, chargeKernel_symm W₀] with p hp hs he
    exact hp.2.symm.trans (he.trans hs.2)
  have h₀zero : ∀ i j, G i j = false → y₀ i j = 0 := by
    apply block_property_of_ae q hpositive
    filter_upwards [hentry] with p hp hG
    have hA : W₀.moment CappedColor.adjacency p = 0 := by simpa [hG] using hp.1
    have hlo := neg_three_adjacency_moment_le_charge W₀ p
    have hhi := charge_moment_le_adjacency W₀ p
    rw [hA] at hlo hhi
    linarith [hp.2]
  have h₀upper : ∀ i j, y₀ i j ≤ 1 := by
    apply block_property_of_ae q hpositive
    filter_upwards [hentry] with p hp
    have hhi := (charge_moment_le_adjacency W₀ p).trans (adjacency_moment_mem W₀ p).2
    linarith [hp.2]
  have h₀lower : ∀ i j, G i j = true → -3 < y₀ i j := by
    apply block_property_of_ae q hpositive
    filter_upwards [hentry, ae_present_charge_gt_neg_three_of_full_optimum W₀ hW₀ hopt₀
      hphysical₀ hd hgap] with p hp hs hG
    have hA : W₀.moment CappedColor.adjacency p = 1 := by simpa [hG] using hp.1
    rw [← hp.2]
    exact hs hA
  have h₁upper : ∀ i j, G i j = true → y₁ i j ≤ 1 := by
    apply block_property_of_ae q hpositive
    exact ae_charge_le_one_of_order_two (fun x z => G (q x) (q z))
      (fun x z => y₁ (q x) (q z)) (fun x z => hGsym _ _) (fun x z => h₁sym _ _) (h₁full 2)
  have hfull₀ : ∀ n, FiniteArity.FeasibleOrder μ
      (fun x z => G (q x) (q z)) (fun x z => y₀ (q x) (q z)) n := by
    apply full_scalar_tests_congr _ (fun x z => BinaryRepresentative.charge W₀
      (fun p => G (q p.1) (q p.2)) (x, z)) _
    · filter_upwards [BinaryRepresentative.charge_ae_eq W₀
        (fun p => G (q p.1) (q p.2)) (hentry.mono (fun _ h => h.1)), hentry] with p hp he
      exact hp.trans he.2
    · exact BinaryRepresentative.full_feasible W₀ hW₀ (fun p => G (q p.1) (q p.2))
        (hentry.mono (fun _ h => h.1))
  have hpair : Measurable (fun p : Ω × Ω => (q p.1, q p.2)) :=
    (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  have hi₀ : Integrable (fun p : Ω × Ω => y₀ (q p.1) (q p.2)) (μ.prod μ) := by
    have hi := integrable_bounded_moment W₀ CappedColor.charge
      CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun z => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨(CappedColor.charge_mem z).1,
          (CappedColor.charge_mem z).2.trans (by norm_num)⟩)
    exact hi.congr (hentry.mono (fun _ h => h.2))
  have hi₁ : Integrable (fun p : Ω × Ω => y₁ (q p.1) (q p.2)) (μ.prod μ) := by
    obtain ⟨B, hB⟩ := (Set.finite_range (fun ij : ι × ι => ‖y₁ ij.1 ij.2‖)).bddAbove
    apply Integrable.of_bound
      (((measurable_of_countable (Function.uncurry y₁)).comp hpair).aestronglyMeasurable) B
    exact Eventually.of_forall (fun p => hB ⟨(q p.1, q p.2), rfl⟩)
  have hdgraph : FiniteCappedSamplingCost.physicalDensity μ (fun x z => G (q x) (q z)) =
      density W₀ := by
    unfold FiniteCappedSamplingCost.physicalDensity density
    congr 1
    exact integral_congr_ae (hentry.mono (fun _ h => h.1.symm))
  have hc₀ : FiniteCappedSamplingCost.physicalObjective μ (fun x z => y₀ (q x) (q z)) =
      objective W₀ := by
    unfold FiniteCappedSamplingCost.physicalObjective objective
    congr 1
    exact integral_congr_ae (hentry.mono (fun _ h => h.2.symm))
  have hlower : ∀ i j, G i j = true → -3 < y₁ i j := by
    by_contra hnot
    push Not at hnot
    obtain ⟨i, j, hij, hbad⟩ := hnot
    let J := {ij : ι × ι // G ij.1 ij.2 = true}
    obtain ⟨t, ht, hbox, k, hk⟩ := exists_finite_charge_boundary
      (fun ij : J => y₀ ij.val.1 ij.val.2) (fun ij : J => y₁ ij.val.1 ij.val.2) (-3) 1
      (fun ij => ⟨h₀lower _ _ ij.property, h₀upper _ _⟩)
      (fun ij => h₁upper _ _ ij.property) ⟨⟨(i, j), hij⟩, hbad⟩
    let y (i j : ι) := (1 - t) * y₀ i j + t * y₁ i j
    have hysym : ∀ i j, y i j = y j i := by
      intro i j
      dsimp only [y]
      rw [h₀sym i j, h₁sym i j]
    have hyzero : ∀ i j, G i j = false → y i j = 0 := by
      intro i j hg
      simp only [y, h₀zero i j hg, h₁zero i j hg, mul_zero, add_zero]
    have hybox : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1 := by
      intro i j
      by_cases hg : G i j = true
      · exact hbox ⟨(i, j), hg⟩
      · rw [hyzero _ _ (Bool.eq_false_iff.mpr hg)]
        norm_num
    have hyfull : ∀ n, FiniteArity.FeasibleOrder μ
        (fun x z => G (q x) (q z)) (fun x z => y (q x) (q z)) n :=
      full_scalar_tests_convex _ _ _ hfull₀ h₁full t ⟨ht.1.le, ht.2⟩
    have hycost : FiniteCappedSamplingCost.physicalObjective μ (fun x z => y (q x) (q z)) =
        objective W₀ := by
      unfold FiniteCappedSamplingCost.physicalObjective at hc₀ h₁cost ⊢
      dsimp only at hc₀ h₁cost
      change (∫ p : Ω × Ω,
        (1 - t) * y₀ (q p.1) (q p.2) + t * y₁ (q p.1) (q p.2) ∂μ.prod μ) / 2 = _
      rw [integral_add (hi₀.const_mul _) (hi₁.const_mul _), integral_const_mul,
        integral_const_mul]
      have hI₀ : (∫ p : Ω × Ω, y₀ (q p.1) (q p.2) ∂μ.prod μ) = 2 * objective W₀ := by
        linarith only [hc₀]
      have hI₁ : (∫ p : Ω × Ω, y₁ (q p.1) (q p.2) ∂μ.prod μ) = 2 * objective W₀ := by
        linarith only [h₁cost]
      rw [hI₀, hI₁]
      ring
    obtain ⟨V, hV, hmom, hdV, hcV, hphysical⟩ :=
      exists_boxed_finite_block_model q hq G hGsym y hysym hyzero hybox hyfull
    have hdV' : density V = density W₀ := hdV.trans hdgraph
    have hcV' : objective V = objective W₀ := hcV.trans hycost
    have hoptV : objective V = FractionalGraph.densityLimit (density V) := by
      rw [hdV', hcV']
      exact hopt₀
    have hgapV : benchmark (density V) < objective V := by rwa [hdV', hcV']
    have hown := ae_present_charge_gt_neg_three_of_full_optimum V hV hoptV hphysical
      (hdV' ▸ hd) hgapV
    have hstrict : ∀ i j, G i j = true → -3 < y i j := by
      apply block_property_of_ae q hpositive
      filter_upwards [hown] with p hp hg
      have hA : V.moment CappedColor.adjacency p = 1 := by simpa [hg] using (hmom p).1
      rw [← (hmom p).2]
      exact hp hA
    have h := hstrict k.val.1 k.val.2 k.property
    change -3 < (1 - t) * y₀ k.val.1 k.val.2 + t * y₁ k.val.1 k.val.2 at h
    rw [hk] at h
    exact (lt_irrefl (-3 : ℝ)) h
  exact fun i j hg => ⟨hlower i j hg, h₁upper i j hg⟩

end Erdos1017.CappedModel
