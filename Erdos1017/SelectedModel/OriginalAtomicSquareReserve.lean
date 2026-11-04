module

public import Erdos1017.SelectedModel.FiniteOriginalAtomicReserve

/-!
# The common forward peak pays all original atomic squares

Original independent atom squares are summable, and by exhausting the low atoms
with finite scalar sums the common forward peak pays all original atomic squares
and strictly dominates the sum of the others
(`exists_original_atomic_square_reserve`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Original independent atom squares are summable under the unchanged law. -/
theorem originalAtomMass_sq_summable (S : SelectedHighLowStructure W m) :
    Summable (fun k => (S.originalAtomMass k) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ S.originalAtomMass_summable.2
  intro k
  have hnonneg := S.originalAtomMass_summable.1 k
  have hbound : S.originalAtomMass k ≤ 1 := measureReal_le_one
  nlinarith

/-- The entire original reserve is exactly the kept nonLOW reserve plus
the actual LOW subtype's scalar square sum. No graphon edit is involved. -/
theorem original_square_reserve_split (S : SelectedHighLowStructure W m) :
    (∑' k, (S.keptAtomMass k) ^ 2) +
      (∑' k : {k : S.I // ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L},
        (S.originalAtomMass k.val) ^ 2) =
      ∑' k, (S.originalAtomMass k) ^ 2 := by
  let L : Set S.I := {k | ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L}
  change (∑' k, (S.keptAtomMass k) ^ 2) +
    (∑' k : L, (S.originalAtomMass k.val) ^ 2) = _
  rw [tsum_subtype L (fun k => (S.originalAtomMass k) ^ 2), ← S.keptAtomMass_sq_summable.tsum_add (S.originalAtomMass_sq_summable.indicator L)]
  apply tsum_congr
  intro k
  by_cases hk : k ∈ L
  · have hlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L := hk
    simp only [keptAtomMass, hlow, ↓reduceIte, zero_pow (by decide : (2 : ℕ) ≠ 0),
      indicator_of_mem hk, zero_add]
  · have hn : ¬(∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L) := hk
    simp only [keptAtomMass, hn, ↓reduceIte, indicator_of_notMem hk, add_zero]

namespace IsFullForwardFlow

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Exhaust the actual LOW atom subtype by finite scalar sums. Each finite
bound constructs its own genuine full flow; no limiting flow or infinite
simultaneous model edit is assumed. -/
theorem original_atomic_square_reserve (hq : S.IsFullForwardFlow q)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (i : S.I) (A : ℝ) (hA : 0 < A)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i)
    (hcap : ∀ (r : Ω × Ω → ℝ), S.IsFullForwardFlow r →
      (∀ᵐ p ∂μ.prod μ, r p ≠ 0 → S.ρ p.1 ≠ i) →
      ∀ k, S.forwardClassMass r k ≤ A)
    (hbound : ∀ k, S.originalAtomMass k ≤ A) :
    2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤ 2 * A ^ 2 := by
  let L := {k : S.I // ∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.L}
  have hsum : Summable (fun k : L => (S.originalAtomMass k.val) ^ 2) :=
    S.originalAtomMass_sq_summable.subtype _
  have hfinite (F : Finset L) :
      (∑ k ∈ F, (-m) * (S.originalAtomMass k.val) ^ 2) ≤
        2 * A ^ 2 - (2 * (c - m * d) + m) - (-m) * (∑' k, (S.keptAtomMass k) ^ 2) := by
    let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
    let j : Fin (Fintype.card F) → S.I := fun v => (e v).val.val
    have hj : Function.Injective j := fun _ _ h => e.injective (Subtype.ext (Subtype.ext h))
    have hjL (v : Fin (Fintype.card F)) :
        ∀ᵐ x ∂μ.restrict {x | S.ρ x = j v}, x ∈ S.L := (e v).val.property
    have hb := hq.finite_low_square_reserve hW hd hgap i A hA havoid hcap j hj hjL
      (fun v => hbound (j v))
    have heq : (∑ v, (S.originalAtomMass (j v)) ^ 2) =
        ∑ z ∈ F, (S.originalAtomMass z.val) ^ 2 := by
      calc
        _ = ∑ z : F, (S.originalAtomMass z.val.val) ^ 2 :=
          e.sum_comp (fun z => (S.originalAtomMass z.val.val) ^ 2)
        _ = _ := Finset.sum_coe_sort F (fun z => (S.originalAtomMass z.val) ^ 2)
    rw [heq] at hb
    rw [← Finset.mul_sum]
    nlinarith
  have htotal := (hsum.mul_left (-m)).tsum_le_of_sum_le hfinite
  rw [tsum_mul_left] at htotal
  have hsplit := S.original_square_reserve_split
  change (∑' k, (S.keptAtomMass k) ^ 2) +
    (∑' k : L, (S.originalAtomMass k.val) ^ 2) = _ at hsplit
  rw [← hsplit]
  nlinarith

end IsFullForwardFlow

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual same selected model has a common original forward peak
paying all original atomic squares and strictly dominating the sum of all
other original atomic squares. Every flow, endpoint cap, finite comparison
and countable limit is derived internally. No guarded missing-mass cap,
finite-family reserve, or endpoint stationarity premise is supplied. -/
theorem exists_original_atomic_square_reserve (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < forwardPeakGap d c m ∧ ∃ i : S.I,
      0 < S.originalAtomMass i ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      (∀ (r : Ω × Ω → ℝ), S.IsFullForwardFlow r →
        0 < S.forwardClassMass r i ∧
        ForwardPeak.massPeak (S.forwardClassMass r) = S.forwardClassMass r i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass r) (forwardPeakGap d c m) i) ∧
      (∀ k : S.I, k ≠ i → S.originalAtomMass k < S.originalAtomMass i) ∧
      (2 * (c - m * d) + m + (-m) * (∑' k, (S.originalAtomMass k) ^ 2) ≤
        2 * (S.originalAtomMass i) ^ 2) ∧
      (∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) <
        (S.originalAtomMass i) ^ 2 := by
  obtain ⟨hΔ, i, hA, hside, hpeak, _, hlargest, _, _⟩ :=
    S.exists_unique_largest_original_forward_peak hW hd hgap
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  have hcap (r : Ω × Ω → ℝ) (hr : S.IsFullForwardFlow r)
      (havoid : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → S.ρ p.1 ≠ i) :
      ∀ k, S.forwardClassMass r k ≤ S.originalAtomMass i := by
    have hret := hr.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
    change S.forwardClassMass r i = S.originalAtomMass i at hret
    intro k
    by_cases hki : k = i
    · rw [hki, hret]
    · have hsep := (hpeak r hr).2.2 k hki
      rw [hret] at hsep
      linarith
  have hbound (k : S.I) : S.originalAtomMass k ≤ S.originalAtomMass i := by
    by_cases hki : k = i
    · rw [hki]
    · exact (hlargest k hki).le
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hreserve := hq.original_atomic_square_reserve hW hd hgap i (S.originalAtomMass i)
    hA havoid hcap hbound
  have hQ : (∑' k, (S.originalAtomMass k) ^ 2) < 2 * (S.originalAtomMass i) ^ 2 := by
    have hs := hW.strict_gap_structure hd hgap
    have hgamma : 0 < 2 * (c - m * d) + m := hs.gamma_pos
    by_cases hm : -1 ≤ m
    · have hmissing := S.originalAtomMass_sq_sum_le_missing_density
      rw [hW.density_eq] at hmissing
      have hbase := Benchmark.benchmark_ge_missing ⟨hd.1.le, hd.2.le⟩
      have hdelta : 0 < 2 * c - (1 - 2 * d) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hmissing (show 0 ≤ 1 + m by linarith)
      nlinarith
    · have hQ0 : 0 ≤ ∑' k, (S.originalAtomMass k) ^ 2 := tsum_nonneg (fun _ => sq_nonneg _)
      have hmul := mul_nonneg (show 0 ≤ -m - 1 by linarith) hQ0
      nlinarith
  have hsplit := S.originalAtomMass_sq_summable.sum_add_tsum_subtype_compl {i}
  simp only [Finset.sum_singleton] at hsplit
  let e : {k : S.I // k ∉ ({i} : Finset S.I)} ≃ {k : S.I // k ≠ i} :=
    Equiv.subtypeEquivRight (fun k => by simp)
  have he := e.tsum_eq (fun k => (S.originalAtomMass k.val) ^ 2)
  change (∑' k : {k : S.I // k ∉ ({i} : Finset S.I)}, (S.originalAtomMass k.val) ^ 2) =
    (∑' k : {k : S.I // k ≠ i}, (S.originalAtomMass k.val) ^ 2) at he
  rw [he] at hsplit
  refine ⟨hΔ, i, hA, hside, hpeak, hlargest, hreserve, ?_⟩
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
