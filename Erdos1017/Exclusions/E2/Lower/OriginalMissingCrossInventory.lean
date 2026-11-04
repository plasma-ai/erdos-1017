module

public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve

/-!
# Missing-density inventory with a cross block

Original independent squares and both orientations of a missing cross block
consume disjoint parts of the original missing density, also for three distinct
atoms; a dominating atom missing one of two smaller atoms gives at least five
times their product, and square majority gives the `33/5` constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- Original independent squares and both orientations of an additional
missing cross block consume disjoint parts of the original missing density. -/
theorem original_squares_add_missing_cross_le (S : SelectedHighLowStructure W m)
    (r u : S.I) (hru : r ≠ u)
    (hzero : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 0) :
    (∑' i, (S.originalAtomMass i) ^ 2) +
      2 * S.originalAtomMass r * S.originalAtomMass u ≤ 1 - 2 * density W := by
  let : Countable S.I := S.hI.to_subtype
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let X := MultipartiteClassMasses.independentPairs S.collapsedPartLabel
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let C := (Ir ×ˢ Iu) ∪ (Iu ×ˢ Ir)
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hX : MeasurableSet X := MultipartiteClassMasses.independentPairs_measurable
    S.collapsedPartLabel S.measurable_collapsedPartLabel
  have hC : MeasurableSet C := (hIr.prod hIu).union (hIu.prod hIr)
  have hdisC : Disjoint (Ir ×ˢ Iu) (Iu ×ˢ Ir) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hru (Subtype.ext (hp.1.symm.trans hq.1))
  have hsame (p : Ω × Ω) (hp : p ∈ X) : S.ρ p.1 = S.ρ p.2 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rw [S.collapsedPartLabel_fiber i] at hi
    exact hi.1.trans hi.2.symm
  have hdis : Disjoint X C := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have he := hsame p hp
    rcases hq with hq | hq
    · exact hru (Subtype.ext (hq.1.symm.trans (he.trans hq.2)))
    · exact hru (Subtype.ext (hq.2.symm.trans (he.symm.trans hq.1)))
  have hzeroX := HalfGraphMultipartite.ae_sameAtom_adjacency_zero
    (adjacencyKernel W) S.ρ S.hρ.measurable S.I S.hI
    (fun r hr => (S.hfibers r hr).2.2.1)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hzero
  have hz : ∀ᵐ p ∂μ.prod μ, p ∈ X ∪ C → adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [hzeroX, hzero, hswap, adjacencyKernel_symm W] with p hx hr hu hs hp
    rcases hp with hp | hp
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      rw [S.collapsedPartLabel_fiber i] at hi
      exact hx ⟨i.val, i.property, hi.1, hi.2⟩
    · rcases hp with hp | hp
      · exact hr hp.1 hp.2
      · exact hs.trans (hu hp.2 hp.1)
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hle : (∫ p, (X ∪ C).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) ≤
      ∫ p, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator (hX.union hC))
      ((integrable_const 1).sub ha)
    filter_upwards [hz] with p hp
    change (X ∪ C).indicator (fun _ => (1 : ℝ)) p ≤ 1 - adjacencyKernel W p.1 p.2
    by_cases hmem : p ∈ X ∪ C
    · simp only [indicator_of_mem hmem, hp hmem, sub_zero, le_refl]
    · simp only [indicator_of_notMem hmem]
      exact sub_nonneg.mpr (adjacency_moment_mem W p).2
  have hXmass : (μ.prod μ).real X = ∑' i, (S.originalAtomMass i) ^ 2 := by
    rw [MultipartiteClassMasses.independentPairs_mass _ S.measurable_collapsedPartLabel]
    apply tsum_congr
    intro i
    rw [MultipartiteClassMasses.classMass, S.collapsedPartLabel_fiber i]
    rfl
  have hCmass : (μ.prod μ).real C = 2 * S.originalAtomMass r * S.originalAtomMass u := by
    rw [measureReal_union hdisC (hIu.prod hIr), measureReal_prod_prod, measureReal_prod_prod]
    change μ.real Ir * μ.real Iu + μ.real Iu * μ.real Ir = 2 * μ.real Ir * μ.real Iu
    ring
  rw [integral_indicator (hX.union hC), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_union hdis hC, hXmass, hCmass] at hle
  have hsub := integral_sub (integrable_const (1 : ℝ)) ha
  change (∫ p, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) = _ at hsub
  rw [hsub] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  unfold density
  linarith

/-- Three distinct original atoms retain all three square contributions
as well as the specified missing cross block. -/
theorem three_original_squares_add_missing_cross_le (S : SelectedHighLowStructure W m)
    (k r u : S.I) (hkr : k ≠ r) (hku : k ≠ u) (hru : r ≠ u)
    (hzero : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 0) :
    (S.originalAtomMass k) ^ 2 + (S.originalAtomMass r) ^ 2 +
      (S.originalAtomMass u) ^ 2 + 2 * S.originalAtomMass k * S.originalAtomMass r ≤
        1 - 2 * density W := by
  let : Countable S.I := S.hI.to_subtype
  have hfinite := Summable.sum_le_tsum (s := {k, r, u})
    (fun i _ => sq_nonneg (S.originalAtomMass i)) S.originalAtomMass_sq_summable
  have hnot : k ∉ ({r, u} : Finset S.I) := by simpa only [Finset.mem_insert,
    Finset.mem_singleton, not_or] using And.intro hkr hku
  have hsum : (S.originalAtomMass k) ^ 2 + (S.originalAtomMass r) ^ 2 +
      (S.originalAtomMass u) ^ 2 ≤ ∑' i, (S.originalAtomMass i) ^ 2 := by
    simpa only [Finset.sum_insert hnot, Finset.sum_pair hru,
      add_assoc] using hfinite
  linarith [S.original_squares_add_missing_cross_le k r hkr hzero]

/-- If a dominating original atom misses one of two smaller distinct
atoms, the same missing inventory is at least five times their product. -/
theorem five_product_le_missing_density_of_missing_cross (S : SelectedHighLowStructure W m)
    (k r u : S.I) (hkr : k ≠ r) (hku : k ≠ u) (hru : r ≠ u)
    (hr : S.originalAtomMass r ≤ S.originalAtomMass k)
    (hu : S.originalAtomMass u ≤ S.originalAtomMass k)
    (hzero : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 0) :
    5 * S.originalAtomMass r * S.originalAtomMass u ≤ 1 - 2 * density W := by
  have hA := S.originalAtomMass_summable.1 k
  have ha := S.originalAtomMass_summable.1 r
  have hAa : S.originalAtomMass r * S.originalAtomMass u ≤
      S.originalAtomMass k * S.originalAtomMass r := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu ha
  have hAA : S.originalAtomMass r * S.originalAtomMass u ≤
      (S.originalAtomMass k) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hr hA
    nlinarith
  have hsquare := sq_nonneg (S.originalAtomMass r - S.originalAtomMass u)
  have hbound := S.three_original_squares_add_missing_cross_le k r u hkr hku hru hzero
  nlinarith

/-- Original square majority gives a stronger cross-missing inventory,
with a rational constant sufficient throughout the lower-E2 interval. -/
theorem thirtyThree_fifths_product_le_missing_density (S : SelectedHighLowStructure W m)
    (k r u : S.I) (hkr : k ≠ r) (hku : k ≠ u) (hru : r ≠ u)
    (hmajority : (S.originalAtomMass r) ^ 2 + (S.originalAtomMass u) ^ 2 ≤
      (S.originalAtomMass k) ^ 2)
    (hzero : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 0) :
    (33 / 5 : ℝ) * S.originalAtomMass r * S.originalAtomMass u ≤ 1 - 2 * density W := by
  let A := S.originalAtomMass k
  let a := S.originalAtomMass r
  let b := S.originalAtomMass u
  have hA : 0 ≤ A := S.originalAtomMass_summable.1 k
  have ha : 0 ≤ a := S.originalAtomMass_summable.1 r
  have hb : 0 ≤ b := S.originalAtomMass_summable.1 u
  change a ^ 2 + b ^ 2 ≤ A ^ 2 at hmajority
  have hlinear : 3 * a + 4 * b ≤ 5 * A := by
    by_contra hn
    have hn' : 5 * A < 3 * a + 4 * b := lt_of_not_ge hn
    have hplus : 0 < 3 * a + 4 * b + 5 * A := by linarith
    have hprod := mul_pos (sub_pos.mpr hn') hplus
    nlinarith [sq_nonneg (4 * a - 3 * b)]
  have hcross := mul_le_mul_of_nonneg_right hlinear ha
  have hbound := S.three_original_squares_add_missing_cross_le k r u hkr hku hru hzero
  change A ^ 2 + a ^ 2 + b ^ 2 + 2 * A * a ≤ 1 - 2 * density W at hbound
  change (33 / 5 : ℝ) * a * b ≤ 1 - 2 * density W
  nlinarith [sq_nonneg (4 * b - 5 * a)]

end Erdos1017.CappedModel.SelectedHighLowStructure
