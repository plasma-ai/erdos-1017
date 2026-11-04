module

public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Routing a supply over infinitely many eligible labels

Every integrable nonnegative supply with infinitely many eligible labels where
it is positive has a measurable assignment within any positive individual
receipt cap (`exists_capped_routing`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Erdos1017.CountableResidualRouting

private theorem count_first {p : ℕ → Prop} [DecidablePred p] (K n : ℕ) :
    Nat.count (fun i => p i ∧ Nat.count p i < K) n = min K (Nat.count p n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih, Nat.count_succ]
    by_cases hp : p n
    · by_cases hc : Nat.count p n < K
      · simp only [hp, hc, and_self, ite_true]
        rw [min_eq_right hc.le, min_eq_right (Nat.succ_le_iff.mpr hc)]
      · have hle : K ≤ Nat.count p n := Nat.le_of_not_gt hc
        simp only [hp, hc, and_false, ite_false, ite_true, add_zero]
        rw [min_eq_left hle, min_eq_left (hle.trans (Nat.le_succ _))]
    · simp only [hp, false_and, ite_false, add_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

private def eligible (E : ℕ → Set Ω) (B : Finset ℕ) (x : Ω) (i : ℕ) : Prop :=
  i ∉ B ∧ x ∈ E i

private def rank (E : ℕ → Set Ω) (B : Finset ℕ) (n : ℕ) (x : Ω) : ℕ := by
  classical
  exact Nat.count (eligible E B x) n

private def chosen (E : ℕ → Set Ω) (B : Finset ℕ) (K i : ℕ) : Set Ω :=
  {x | eligible E B x i ∧ rank E B i x < K}

private def routing (E : ℕ → Set Ω) (B : Finset ℕ) (K : ℕ)
    (r : Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  (chosen E B K i).indicator (fun x => max (r x) 0 / (K : ℝ))

private theorem measurableSet_eligible (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (B : Finset ℕ) (i : ℕ) :
    MeasurableSet {x | eligible E B x i} := by
  by_cases hi : i ∈ B
  · simp [eligible, hi]
  · simpa [eligible, hi] using hE i

private theorem measurable_rank (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (B : Finset ℕ) (n : ℕ) :
    Measurable (rank E B n) := by
  classical
  induction n with
  | zero =>
    change Measurable (fun x => Nat.count (eligible E B x) 0)
    simpa only [Nat.count_zero] using measurable_const (a := (0 : ℕ))
  | succ n ih =>
    have hm : Measurable (fun x => if eligible E B x n then (1 : ℕ) else 0) :=
      Measurable.ite (measurableSet_eligible E hE B n) measurable_const measurable_const
    change Measurable (fun x => Nat.count (eligible E B x) (n + 1))
    change Measurable (fun x => Nat.count (eligible E B x) n) at ih
    simp only [Nat.count_succ]
    convert ih.add hm using 1

private theorem measurableSet_chosen (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (B : Finset ℕ) (K i : ℕ) :
    MeasurableSet (chosen E B K i) :=
  (measurableSet_eligible E hE B i).inter
    (measurableSet_lt (measurable_rank E hE B i) measurable_const)

omit [MeasurableSpace Ω] in
private theorem routing_sum (E : ℕ → Set Ω) (B : Finset ℕ) (K n : ℕ)
    (r : Ω → ℝ) (x : Ω) :
    (∑ i ∈ Finset.range n, routing E B K r i x) =
      (min K (rank E B n x) : ℕ) * (max (r x) 0 / (K : ℝ)) := by
  classical
  calc
    _ = ∑ i ∈ (Finset.range n).filter
        (fun i => eligible E B x i ∧ Nat.count (eligible E B x) i < K),
        max (r x) 0 / (K : ℝ) := by
      simp only [Finset.sum_filter, routing, indicator_apply, chosen, mem_ofPred_eq, rank]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Nat.count_eq_card_filter_range, count_first]
      rfl

omit [MeasurableSpace Ω] in
private theorem routing_nonneg (E : ℕ → Set Ω) (B : Finset ℕ) (K : ℕ)
    (r : Ω → ℝ) (i : ℕ) (x : Ω) : 0 ≤ routing E B K r i x := by
  classical
  exact indicator_nonneg (fun x _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) x

omit [MeasurableSpace Ω] in
private theorem routing_le (E : ℕ → Set Ω) (B : Finset ℕ) (K : ℕ)
    (r : Ω → ℝ) (i : ℕ) (x : Ω) :
    routing E B K r i x ≤ max (r x) 0 / (K : ℝ) := by
  classical
  by_cases hx : x ∈ chosen E B K i
  · simp only [routing, indicator_of_mem hx, le_refl]
  · simp only [routing, indicator_of_notMem hx]
    positivity

omit [MeasurableSpace Ω] in
private theorem routing_partial_bound (E : ℕ → Set Ω) (B : Finset ℕ) {K : ℕ}
    (hK : 0 < K) (r : Ω → ℝ) (n : ℕ) (x : Ω) :
    (∑ i ∈ Finset.range n, routing E B K r i x) ≤ max (r x) 0 := by
  rw [routing_sum]
  have hm : ((min K (rank E B n x) : ℕ) : ℝ) ≤ K :=
    Nat.cast_le.mpr (min_le_left _ _)
  have hpos : 0 ≤ max (r x) 0 / (K : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right hm hpos
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  simpa only [mul_div_cancel₀ _ hK0] using h

omit [MeasurableSpace Ω] in
private theorem routing_eventually_complete (E : ℕ → Set Ω) (B : Finset ℕ) {K : ℕ}
    (hK : 0 < K) (r : Ω → ℝ) (x : Ω)
    (hInf : {i | eligible E B x i}.Infinite) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ i ∈ Finset.range n, routing E B K r i x) = max (r x) 0 := by
  classical
  refine ⟨Nat.nth (eligible E B x) K, fun n hn => ?_⟩
  rw [routing_sum]
  have hcount : K ≤ rank E B n x := by
    have hm := Nat.count_monotone (eligible E B x) hn
    rw [Nat.count_nth_of_infinite hInf K] at hm
    exact hm
  rw [min_eq_left hcount]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hK.ne')

variable {μ : Measure Ω}

/-- Every integrable nonnegative supply with infinitely many eligible labels
where it is positive has a genuine measurable assignment within any positive
individual receipt cap. Finitely many blocked labels receive nothing. The
construction splits each source equally over its first finitely many eligible
unblocked labels; it makes no global assumption of infinitely many atoms. -/
theorem exists_capped_routing (E : ℕ → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (B : Finset ℕ) (r : Ω → ℝ) (hr : Measurable r) (hrInt : Integrable r μ)
    (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x) {ε : ℝ} (hε : 0 < ε)
    (hInf : ∀ᵐ x ∂μ, 0 < r x → {i | x ∈ E i}.Infinite) :
    ∃ q : ℕ → Ω → ℝ,
      (∀ i, Measurable (q i) ∧ Integrable (q i) μ) ∧
      (∀ i x, 0 ≤ q i x) ∧
      (∀ i x, i ∈ B ∨ x ∉ E i → q i x = 0) ∧
      (∀ i, (∫ x, q i x ∂μ) ≤ ε) ∧
      (∀ n x, (∑ i ∈ Finset.range n, q i x) ≤ max (r x) 0) ∧
      (∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n, N ≤ n → (∑ i ∈ Finset.range n, q i x) = r x) ∧
      (∀ᵐ x ∂μ, HasSum (fun i => q i x) (r x)) ∧
      HasSum (fun i => ∫ x, q i x ∂μ) (∫ x, r x ∂μ) := by
  classical
  have hrPos : Integrable (fun x => max (r x) 0) μ := hrInt.pos_part
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x, max (r x) 0 ∂μ) / ε)
  let K := N + 1
  have hK : 0 < K := Nat.succ_pos N
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hcap : (∫ x, max (r x) 0 ∂μ) / (K : ℝ) ≤ ε := by
    apply (div_le_iff₀ hKreal).mpr
    have hmass := (div_lt_iff₀ hε).mp hN
    dsimp only [K]
    push_cast
    nlinarith
  let q := routing E B K r
  have hmeas (i : ℕ) : Measurable (q i) :=
    ((hr.max measurable_const).div_const (K : ℝ)).indicator
      (measurableSet_chosen E hE B K i)
  have hint (i : ℕ) : Integrable (q i) μ :=
    (hrPos.div_const (K : ℝ)).indicator (measurableSet_chosen E hE B K i)
  have hnonneg (i : ℕ) (x : Ω) : 0 ≤ q i x := routing_nonneg E B K r i x
  have hsupport (i : ℕ) (x : Ω) (hbad : i ∈ B ∨ x ∉ E i) : q i x = 0 := by
    apply indicator_of_notMem
    intro hx
    rcases hx.1 with ⟨hi, hxE⟩
    exact hbad.elim hi (fun hxnot => hxnot hxE)
  have hreceipt (i : ℕ) : (∫ x, q i x ∂μ) ≤ ε := by
    calc
      _ ≤ ∫ x, max (r x) 0 / (K : ℝ) ∂μ :=
        integral_mono (hint i) (hrPos.div_const _) (routing_le E B K r i)
      _ = (∫ x, max (r x) 0 ∂μ) / (K : ℝ) := integral_div _ _
      _ ≤ ε := hcap
  have hpartial (n : ℕ) (x : Ω) :
      (∑ i ∈ Finset.range n, q i x) ≤ max (r x) 0 :=
    routing_partial_bound E B hK r n x
  have hcomplete : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ i ∈ Finset.range n, q i x) = r x := by
    filter_upwards [hr0, hInf] with x hx0 hxInf
    by_cases hx : r x = 0
    · refine ⟨0, fun n _ => ?_⟩
      change (∑ i ∈ Finset.range n, routing E B K r i x) = r x
      rw [routing_sum, hx]
      simp
    · have hxpos : 0 < r x := lt_of_le_of_ne hx0 (Ne.symm hx)
      have hInf' : {i | eligible E B x i}.Infinite := by
        have heq : {i | eligible E B x i} = {i | x ∈ E i} \ (B : Set ℕ) := by
          ext i
          simp only [eligible, mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe, and_comm]
        rw [heq]
        exact (hxInf hxpos).sdiff B.finite_toSet
      obtain ⟨N, hN⟩ := routing_eventually_complete E B hK r x hInf'
      exact ⟨N, fun n hn => by simpa only [max_eq_left hx0] using hN n hn⟩
  have hsum : ∀ᵐ x ∂μ, HasSum (fun i => q i x) (r x) := by
    filter_upwards [hcomplete] with x hx
    obtain ⟨N, hN⟩ := hx
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => hnonneg i x) (r x)).mpr
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hN n hn).symm
  have hmass : HasSum (fun i => ∫ x, q i x ∂μ) (∫ x, r x ∂μ) := by
    apply hasSum_integral_of_dominated_convergence q
      (fun i => (hmeas i).aestronglyMeasurable)
    · intro i
      exact Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hnonneg i x)])
    · exact hsum.mono (fun _ hx => hx.summable)
    · exact hrInt.congr (hsum.mono (fun _ hx => hx.tsum_eq.symm))
    · exact hsum
  exact ⟨q, fun i => ⟨hmeas i, hint i⟩, hnonneg, hsupport, hreceipt,
    hpartial, hcomplete, hsum, hmass⟩

end Erdos1017.CountableResidualRouting
