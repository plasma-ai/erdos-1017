module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleSurvivalLimit

/-!
# The nibble round in real-power form

This module restates the simultaneous nibble step in real-power form: mean
bounds with exceptional vertices, residual near-regularity outside the updated
exceptions, the active-survivor mean bound used by the exponential schedule, and
a round controlling all of these together (`exists_regular_rpow_round`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit mean bounds when a specified set of vertices is exceptional.
Edges meeting that set contribute at most their actual lost-degree count. -/
theorem prospectiveDegree_exceptional_mean_rpow_bounds (H : Finset (Finset V))
    (U W : Finset V) (p L D c : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p < 1) (hc : 0 ≤ c)
    (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r)
    (hdegree : ∀ u ∈ U, u ∉ W → L ≤ (degree H u : ℝ) ∧ (degree H u : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) (v : V) :
    (degree (removeVertices H W) v : ℝ) * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * D)) ≤
        (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) ∧
      (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) ≤
        (degree (removeVertices H W) v : ℝ) *
          ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c)) +
          ((degree H v : ℝ) - degree (removeVertices H W) v) := by
  classical
  let P := H.filter (fun e => v ∈ e)
  let Q := (removeVertices H W).filter (fun e => v ∈ e)
  let f (e : Finset V) : ℝ := (1 - p) ^ (blockers H v e).card
  have hsub : Q ⊆ P := by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
      (Finset.mem_filter.mp he).2⟩
  have hbound (e : Finset V) (he : e ∈ Q) :
      (1 - p) ^ (((r - 1 : ℕ) : ℝ) * D) ≤ f e ∧
      f e ≤ (1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c) := by
    obtain ⟨heR, hev⟩ := Finset.mem_filter.mp he
    obtain ⟨heH, heW⟩ := Finset.mem_filter.mp heR
    apply edge_exposure_rpow_bounds H v e p L D c r hp hp1 hc hev (huniform e heH) _ hcodegree
    intro u hu
    have hue := (Finset.mem_erase.mp hu).2
    exact hdegree u (hsupport e heH hue) (fun huW => Finset.disjoint_left.mp heW hue huW)
  have hnonneg (e : Finset V) : 0 ≤ f e := pow_nonneg (sub_nonneg.mpr hp1.le) _
  have hone (e : Finset V) : f e ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1.le) (by linarith)
  have hsplit : (∑ e ∈ P, f e) = (∑ e ∈ Q, f e) + ∑ e ∈ P \ Q, f e := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset hsub]
  have hlow : (Q.card : ℝ) * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * D)) ≤ ∑ e ∈ Q, f e := by
    calc
      _ = ∑ e ∈ Q, ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * D)) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun e he => (hbound e he).1)
  have hhigh : (∑ e ∈ Q, f e) ≤ (Q.card : ℝ) *
      ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c)) := by
    calc
      _ ≤ ∑ e ∈ Q, ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c)) := Finset.sum_le_sum (fun e he => (hbound e he).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hrestlo : 0 ≤ ∑ e ∈ P \ Q, f e := Finset.sum_nonneg (fun e _ => hnonneg e)
  have hresthi : (∑ e ∈ P \ Q, f e) ≤ (P.card : ℝ) - Q.card := by
    calc
      _ ≤ ∑ e ∈ P \ Q, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hone e)
      _ = _ := by simp [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [prospectiveDegree_expectation, ← Finset.sum_filter]
  change (Q.card : ℝ) * _ ≤ (∑ e ∈ P, f e) ∧ (∑ e ∈ P, f e) ≤ (Q.card : ℝ) * _ + ((P.card : ℝ) - Q.card)
  constructor <;> linarith

/-- Near-regularity of the actual residual graph outside the explicitly updated exception set. -/
theorem residual_regular_rpow_outside (H : Finset (Finset V)) (X : Finset V → Bool)
    (U W : Finset V) (p L D c t a : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p < 1) (hc : 0 ≤ c)
    (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r)
    (hdegree : ∀ u ∈ U, u ∉ W → L ≤ (degree H u : ℝ) ∧ (degree H u : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) :
    ∀ v ∈ survivors H X U, v ∉ nextExceptions H X U W p t a →
      (L - a) * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * D)) - t ≤ (degree (residual H X) v : ℝ) ∧
        (degree (residual H X) v : ℝ) ≤
          D * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c)) + a + t := by
  have hlo : 0 ≤ (1 - p) ^ (((r - 1 : ℕ) : ℝ) * D) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hhi : 0 ≤ (1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c) :=
    (Real.rpow_pos_of_pos (by linarith) _).le
  classical
  intro v hv hex
  have hnot : v ∉ W ∧ v ∉ damaged H W a ∧ v ∉ badDegrees H X p t := by
    simpa only [nextExceptions, Finset.mem_inter, hv, true_and, Finset.mem_union, not_or, and_assoc] using hex
  have hprior := hdegree v (Finset.mem_filter.mp hv).1 hnot.1
  have hloss : (degree H v : ℝ) - degree (removeVertices H W) v < a := by
    by_contra h
    exact hnot.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩)
  have hmean := prospectiveDegree_exceptional_mean_rpow_bounds H U W p L D c r hp hp1 hc
    hsupport huniform hdegree hcodegree v
  have hconcentration : |prospectiveDegree H X v -
      ∑ Y, CliqueSampling.weight (fun _ => p) Y * prospectiveDegree H Y v| < t := by
    rw [prospectiveDegree_expectation, ← Finset.sum_filter]
    by_contra h
    exact hnot.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩)
  have hactual : (degree (residual H X) v : ℝ) = prospectiveDegree H X v := by
    rw [residual_degree_eq_survival_mul]
    have hsurvive : untouched H X {v} = 1 := by
      unfold untouched
      split_ifs with h
      · rfl
      · exact (h (Finset.mem_filter.mp hv).2).elim
    rw [hsurvive, one_mul]
  have hgoodlo : L - a ≤ (degree (removeVertices H W) v : ℝ) := by linarith
  have hgoodhi : (degree (removeVertices H W) v : ℝ) ≤ D := by
    have hmono : (degree (removeVertices H W) v : ℝ) ≤ degree H v := by
      exact_mod_cast removeVertices_degree_le H W v
    exact hmono.trans hprior.2
  have hmullo := mul_le_mul_of_nonneg_right hgoodlo hlo
  have hmulhi := mul_le_mul_of_nonneg_right hgoodhi hhi
  have habs := abs_lt.mp hconcentration
  rw [hactual]
  constructor <;> linarith

omit [Fintype V] in
/-- Exact active-survivor mean bound used by the exponential schedule. -/
theorem active_survivor_mean_rpow_upper (H : Finset (Finset V)) (U W : Finset V)
    (p L : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hlower : ∀ v ∈ U, v ∉ W → L ≤ (degree H v : ℝ)) :
    (∑ v ∈ U, (1 - p) ^ degree H v) ≤ U.card * (1 - p) ^ L + W.card := by
  classical
  have hfactor : 0 ≤ (1 - p) ^ L := (Real.rpow_pos_of_pos (by linarith) _).le
  have hterm (v : V) (hv : v ∈ U) :
      (1 - p) ^ degree H v ≤ (1 - p) ^ L + (if v ∈ W then 1 else 0) := by
    by_cases hW : v ∈ W
    · simp only [hW, ↓reduceIte]
      have hpow : (1 - p) ^ degree H v ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    · simp only [hW, ↓reduceIte, add_zero]
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (hlower v hv hW)
  have hcount : (∑ v ∈ U, if v ∈ W then (1 : ℝ) else 0) ≤ W.card := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
    simpa using (show ((U ∩ W).card : ℝ) ≤ W.card from by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-- An actual simultaneous nibble step, including active vertex count, updated exceptions,
residual near-regularity and discarded waste. All selection estimates are derived from the
Bernoulli round; the only budget condition is an explicit numerical inequality. -/
theorem exists_regular_rpow_round (H : Finset (Finset V)) (U W : Finset V)
    (p L D M c t s A B a : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p < 1) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (ht : 0 < t) (hs : 0 < s) (hA : 0 < A) (hB : 0 < B) (ha : 0 < a)
    (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ M)
    (hregular : ∀ v ∈ U, v ∉ W → L ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ c)
    (hbudget : p * Fintype.card V * (M + Fintype.card V * c) / s ^ 2 +
      (p * (r * c) * (r * M) * M * Fintype.card V / t ^ 2) / B +
      (p ^ 2 * r ^ 2 * M * H.card) / A < 1) :
    ∃ X : Finset V → Bool,
      ((survivors H X U).card : ℝ) < U.card * ((1 - p) ^ L) + W.card + s ∧
      ((nextExceptions H X U W p t a).card : ℝ) < W.card + r * M * W.card / a + B ∧
      ((wasted H X U).card : ℝ) < A ∧
      (∀ e ∈ residual H X, e ⊆ survivors H X U) ∧
      (retained H X : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ v ∈ survivors H X U, v ∉ nextExceptions H X U W p t a →
        (L - a) * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * D)) - t ≤ (degree (residual H X) v : ℝ) ∧
          (degree (residual H X) v : ℝ) ≤
            D * ((1 - p) ^ (((r - 1 : ℕ) : ℝ) * (L - c) - ((r - 1 : ℕ) : ℝ) ^ 2 * c)) + a + t) := by
  obtain ⟨X, hlive, hbad, hwaste⟩ := exists_good_round H p M c t s A B r hp hp1.le hM hc
    ht hs hA hB huniform hdegree hcodegree hbudget
  have hlive' : |((survivors H X U).card : ℝ) - ∑ v ∈ U, (1 - p) ^ degree H v| < s := by
    rw [survivorCount_active H X U hsupport, survivor_mean_active H p U hsupport] at hlive
    convert hlive using 1
    congr 1
    ring
  have hmean := active_survivor_mean_rpow_upper H U W p L hp hp1
    (fun v hv hvW => (hregular v hv hvW).1)
  have hexceptions := nextExceptions_card_bound H X U W p t a M r ha huniform hdegree
  have hwaste_subset : wasted H X U ⊆ wasted H X Finset.univ := by
    intro v hv
    obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hvnot (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hvU, (Finset.mem_filter.mp h).2⟩))
    · exact hvnot (Finset.mem_union_right _ h)
  have hwaste_le : ((wasted H X U).card : ℝ) ≤ (wasted H X Finset.univ).card := by
    exact_mod_cast Finset.card_le_card hwaste_subset
  refine ⟨X, ?_, ?_, hwaste_le.trans_lt hwaste,
    residual_supported_on_survivors H X U hsupport, retained_pairwise_disjoint H X, ?_⟩
  · have h := (abs_lt.mp hlive').2
    linarith
  · linarith
  · exact residual_regular_rpow_outside H X U W p L D c t a r hp hp1 hc hsupport huniform
      hregular hcodegree

end Erdos1017.HypergraphNibble
