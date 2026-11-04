module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleGoodRound

/-!
# Removing an exceptional vertex set from a hypergraph

Removing every edge incident to an exceptional vertex set loses degree at each
vertex bounded by its codegrees with the deleted set, damages only a
quantitatively bounded number of vertices (`damaged_count_bound`), and keeps the
residual near-regular outside an explicit enlarged exception set.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Remove every edge incident to a specified exceptional vertex set. -/
def removeVertices (H : Finset (Finset V)) (W : Finset V) : Finset (Finset V) :=
  H.filter (fun e => Disjoint e W)

omit [Fintype V] in
/-- The edge loss caused by actual deletion is bounded by the exceptional vertices' degrees. -/
theorem removeVertices_edge_loss (H : Finset (Finset V)) (W : Finset V) :
    H.card - (removeVertices H W).card ≤ ∑ v ∈ W, degree H v := by
  classical
  have hremove : H \ removeVertices H W = incident H W := by
    ext e
    simp only [removeVertices, incident, Finset.mem_sdiff, Finset.mem_filter]
    rw [← Finset.not_disjoint_iff_nonempty_inter]
    tauto
  have hunion : incident H W = W.biUnion (fun v => H.filter (fun e => v ∈ e)) := by
    ext e
    simp only [incident, Finset.mem_filter, Finset.Nonempty, Finset.mem_inter, Finset.mem_biUnion]
    aesop
  have hsub : removeVertices H W ⊆ H := Finset.filter_subset _ H
  rw [← Finset.card_sdiff_of_subset hsub, hremove, hunion]
  exact Finset.card_biUnion_le

omit [Fintype V] in
theorem removeVertices_degree_le (H : Finset (Finset V)) (W : Finset V) (v : V) :
    degree (removeVertices H W) v ≤ degree H v := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
    (Finset.mem_filter.mp he).2⟩

omit [Fintype V] in
/-- At each vertex the degree loss is bounded by its codegrees with the deleted set. -/
theorem removeVertices_degree_loss (H : Finset (Finset V)) (W : Finset V) (v : V) :
    degree H v - degree (removeVertices H W) v ≤ ∑ u ∈ W, codegree H v u := by
  classical
  have hsub : (removeVertices H W).filter (fun e => v ∈ e) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
      (Finset.mem_filter.mp he).2⟩
  have hcover : H.filter (fun e => v ∈ e) \ (removeVertices H W).filter (fun e => v ∈ e) ⊆
      W.biUnion (fun u => H.filter (fun e => v ∈ e ∧ u ∈ e)) := by
    intro e he
    obtain ⟨heH, hev⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1
    have hn : ¬Disjoint e W := by
      intro h
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨heH, h⟩, hev⟩)
    obtain ⟨u, hu⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hn
    obtain ⟨hue, huW⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_biUnion.mpr ⟨u, huW, Finset.mem_filter.mpr ⟨heH, hev, hue⟩⟩
  change (H.filter (fun e => v ∈ e)).card - ((removeVertices H W).filter (fun e => v ∈ e)).card ≤ _
  rw [← Finset.card_sdiff_of_subset hsub]
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

/-- Total lost incidence is bounded by rank times the maximum degree times the exceptional count. -/
theorem removeVertices_total_degree_loss (H : Finset (Finset V)) (W : Finset V)
    (r : ℕ) (D : ℝ) (huniform : ∀ e ∈ H, e.card = r)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ D) :
    (∑ v : V, ((degree H v : ℝ) - degree (removeVertices H W) v)) ≤ r * D * W.card := by
  have huniform' : ∀ e ∈ removeVertices H W, e.card = r :=
    fun e he => huniform e (Finset.mem_filter.mp he).1
  have hsum : (∑ v : V, (degree H v : ℝ)) = r * (H.card : ℝ) := by
    exact_mod_cast sum_degrees H r huniform
  have hsum' : (∑ v : V, (degree (removeVertices H W) v : ℝ)) = r * ((removeVertices H W).card : ℝ) := by
    exact_mod_cast sum_degrees (removeVertices H W) r huniform'
  have hcard := removeVertices_edge_loss H W
  have hsubset : removeVertices H W ⊆ H := Finset.filter_subset _ _
  have hcast : (H.card : ℝ) - (removeVertices H W).card ≤ ∑ v ∈ W, (degree H v : ℝ) := by
    have hcast0 : ((H.card - (removeVertices H W).card : ℕ) : ℝ) ≤ ∑ v ∈ W, (degree H v : ℝ) := by
      exact_mod_cast hcard
    rwa [Nat.cast_sub (Finset.card_le_card hsubset)] at hcast0
  have hmax : (∑ v ∈ W, (degree H v : ℝ)) ≤ (W.card : ℝ) * D := by
    calc
      _ ≤ ∑ v ∈ W, D := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsum, hsum']
  have hmul := mul_le_mul_of_nonneg_left (hcast.trans hmax) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  nlinarith

/-- Vertices losing at least `a` incident edges when the exceptional set is removed. -/
def damaged (H : Finset (Finset V)) (W : Finset V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => a ≤ (degree H v : ℝ) - degree (removeVertices H W) v)

/-- Removing a small exceptional set damages only a quantitatively bounded number of vertices. -/
theorem damaged_count_bound (H : Finset (Finset V)) (W : Finset V) (a D : ℝ) (r : ℕ)
    (huniform : ∀ e ∈ H, e.card = r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D) :
    a * (damaged H W a).card ≤ r * D * W.card := by
  classical
  have hnonneg (v : V) : 0 ≤ (degree H v : ℝ) - degree (removeVertices H W) v := by
    have h : (degree (removeVertices H W) v : ℝ) ≤ degree H v := by
      exact_mod_cast removeVertices_degree_le H W v
    linarith
  calc
    _ = ∑ v ∈ damaged H W a, a := by simp [mul_comm]
    _ ≤ ∑ v ∈ damaged H W a, ((degree H v : ℝ) - degree (removeVertices H W) v) :=
      Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑ v : V, ((degree H v : ℝ) - degree (removeVertices H W) v) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => hnonneg v)
    _ ≤ _ := removeVertices_total_degree_loss H W r D huniform hdegree

/-- The initial exceptional vertices may be deleted without silently assuming
regularity everywhere: newly damaged vertices are retained as an explicit exception set. -/
theorem removeVertices_regular_outside_exceptions (H : Finset (Finset V))
    (U W : Finset V) (L D a : ℝ)
    (hsupport : ∀ e ∈ H, e ⊆ U)
    (hlower : ∀ v ∈ U, v ∉ W → L ≤ (degree H v : ℝ))
    (hupper : ∀ v, (degree H v : ℝ) ≤ D) :
    (∀ e ∈ removeVertices H W, e ⊆ U \ W) ∧
      ∀ v ∈ U \ W, v ∉ damaged H W a →
        L - a ≤ (degree (removeVertices H W) v : ℝ) ∧
          (degree (removeVertices H W) v : ℝ) ≤ D := by
  constructor
  · intro e he v hv
    obtain ⟨heH, heW⟩ := Finset.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨hsupport e heH hv, fun h => Finset.disjoint_left.mp heW hv h⟩
  · intro v hv hgood
    have hlow := hlower v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2
    have hsmall : (degree H v : ℝ) - degree (removeVertices H W) v < a := by
      apply lt_of_not_ge
      intro h
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hmono : (degree (removeVertices H W) v : ℝ) ≤ degree H v := by
      exact_mod_cast removeVertices_degree_le H W v
    exact ⟨by linarith, hmono.trans (hupper v)⟩

end Erdos1017.HypergraphNibble
