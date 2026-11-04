module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphDegreePruning

/-!
# Near-perfect matching from a bounded mean and squared error

A hypergraph with bounded mean degree and small aggregate squared degree error
has a near-perfect matching; pruning replaces the maximum-degree hypothesis
(`near_perfect_matching_of_squared_error`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

/-- Near-perfect matching with a bounded mean and a small aggregate squared
error. Pruning replaces a maximum-degree hypothesis, so the tolerance depends
only on rank, the mean multiplier and the desired matching error. -/
theorem near_perfect_matching_of_squared_error (r : ℕ) (C₀ δ : ℝ)
    (hr : 2 ≤ r) (hC₀ : 1 ≤ C₀) (hδ : 0 < δ) :
    ∃ η D₀ : ℝ, 0 < η ∧ 0 < D₀ ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
        (μ : V → ℝ) (W : Finset V) (D : ℝ),
        D₀ ≤ D → (∀ e ∈ H, e.card = r) →
        (∀ v, μ v ≤ C₀ * D) →
        (∀ v w, v ≠ w → (codegree H v w : ℝ) ≤ η * D) →
        (∀ v, v ∉ W → (1 - η) * D ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + η) * D) →
        (W.card : ℝ) ≤ η * Fintype.card V →
        (∑ v : V, ((degree H v : ℝ) - μ v) ^ 2) ≤ η * Fintype.card V * D ^ 2 →
        ∃ M : Finset (Finset V), M ⊆ H ∧ (M : Set (Finset V)).PairwiseDisjoint id ∧
          (1 - δ) * Fintype.card V / r ≤ (M.card : ℝ) := by
  classical
  let C := C₀ + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  obtain ⟨γ, D₀, hγ, hγ1, hD₀, hmatch⟩ := near_perfect_matching_fintype r C δ hr hC hδ
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let η := min (γ / 4) (γ ^ 2 / (8 * r * C))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ γ / 4 := min_le_left _ _
  have hη2 : 8 * r * C * η ≤ γ ^ 2 := by
    have h := min_le_right (γ / 4) (γ ^ 2 / (8 * r * C))
    have hden : 0 < 8 * (r : ℝ) * C := by positivity
    have h' := (le_div_iff₀ hden).mp h
    dsimp only [η]
    nlinarith
  refine ⟨η, D₀, hη, hD₀, ?_⟩
  intro V _ _ H μ W D hD huniform hμ hcodegree hregular hW hsquare
  have hDpos : 0 < D := hD₀.trans_le hD
  let K := removeVertices H (highDegrees H C D)
  let B := damaged H (highDegrees H C D) (γ * D / 2)
  have hμ' : ∀ v, μ v ≤ (C - 1) * D := by simpa only [C, add_sub_cancel_right] using hμ
  have hdam := pruned_damaged_count H μ r C D (γ * D / 2) hC hDpos huniform hμ'
  have hB : (B.card : ℝ) ≤ γ * Fintype.card V / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hsquare
      (mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (by linarith : 0 ≤ C))
    have hbound := hdam.trans hmul
    have hcoef := mul_le_mul_of_nonneg_right hη2
      (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
    apply le_of_mul_le_mul_left (a := γ * D ^ 2 / 2) ?_ (by positivity)
    dsimp only [B]
    nlinarith
  obtain ⟨M, hM, hdisj, hcard⟩ := hmatch V K (W ∪ B) D hD
    (fun e he => huniform e (Finset.mem_filter.mp he).1)
    (fun v => pruned_degree_le H C D (by positivity) v)
    (by
      intro v w hvw
      have hmono : codegree K v w ≤ codegree H v w := by
        apply Finset.card_le_card
        intro e he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
          (Finset.mem_filter.mp he).2⟩
      have hmono' : (codegree K v w : ℝ) ≤ codegree H v w := by exact_mod_cast hmono
      have htol : η * D ≤ γ * D := by nlinarith
      exact hmono'.trans ((hcodegree v w hvw).trans htol))
    (by
      intro v hv
      have hvW : v ∉ W := fun h => hv (Finset.mem_union_left B h)
      have hvB : v ∉ B := fun h => hv (Finset.mem_union_right W h)
      have hsmall : (degree H v : ℝ) - degree K v < γ * D / 2 := by
        simpa only [B, damaged, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hvB
      have hmono : (degree K v : ℝ) ≤ degree H v := by
        exact_mod_cast removeVertices_degree_le H (highDegrees H C D) v
      obtain ⟨hlow, hupp⟩ := hregular v hvW
      constructor <;> nlinarith)
    (by
      have hunion : ((W ∪ B).card : ℝ) ≤ W.card + B.card := by exact_mod_cast Finset.card_union_le W B
      have horder := Nat.cast_nonneg (α := ℝ) (Fintype.card V)
      nlinarith)
  exact ⟨M, hM.trans (Finset.filter_subset _ _), hdisj, hcard⟩

end Erdos1017.HypergraphNibble
