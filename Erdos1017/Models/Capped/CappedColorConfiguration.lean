module

public import Erdos1017.Models.Capped.CappedSubcliqueTests
public import Erdos1017.Models.Capped.CappedFiniteRepair

/-!
# Sampled color configurations as finite duals

A sampled color configuration gives a symmetric charge matrix (`pairColor`)
whose unordered color sum is exactly the finite signed-dual objective, subsets
have the charge of their enumerated subclique, and the subclique tests make the
matrix a feasible finite-graph dual.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {n : ℕ}

/-- The symmetric matrix represented by one color for each unordered pair. -/
def pairColor (c : CliquePair n → CappedColor) (i j : Fin n) : CappedColor :=
  if h : i < j then c ⟨(i, j), h⟩
  else if h : j < i then c ⟨(j, i), h⟩ else CappedColor.absent

@[simp] theorem pairColor_self (c : CliquePair n → CappedColor) (i : Fin n) :
    pairColor c i i = CappedColor.absent := by simp [pairColor]

theorem pairColor_symm (c : CliquePair n → CappedColor) (i j : Fin n) :
    pairColor c i j = pairColor c j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [pairColor, h, not_lt.mpr h.le]
  · rfl
  · simp [pairColor, h, not_lt.mpr h.le]

theorem pairColor_lt (c : CliquePair n → CappedColor) (i j : Fin n) (h : i < j) :
    pairColor c i j = c ⟨(i, j), h⟩ := by simp [pairColor, h]

theorem color_eq_absent_of_not_present (c : CappedColor) (hc : CappedColor.adjacency c ≠ 1) :
    c = CappedColor.absent := by
  rcases c.property with h | h
  · apply Subtype.ext
    exact Prod.ext h.1 h.2
  · exact False.elim (hc h.1)

/-- The actual finite graph sampled by the adjacency coordinates. -/
def configurationGraph (c : CliquePair n → CappedColor) : SimpleGraph (Fin n) where
  Adj i j := CappedColor.adjacency (pairColor c i j) = 1
  symm := ⟨by intro i j hij; rwa [pairColor_symm] at hij⟩
  loopless := ⟨by intro i; simp⟩

def chargeMatrix (c : CliquePair n → CappedColor) (i j : Fin n) : ℝ :=
  CappedColor.charge (pairColor c i j)

@[simp] theorem chargeMatrix_self (c : CliquePair n → CappedColor) (i : Fin n) :
    chargeMatrix c i i = 0 := by simp [chargeMatrix]

theorem chargeMatrix_symm (c : CliquePair n → CappedColor) (i j : Fin n) :
    chargeMatrix c i j = chargeMatrix c j i :=
  congrArg CappedColor.charge (pairColor_symm c i j)

theorem chargeMatrix_nonedge (c : CliquePair n → CappedColor) (i j : Fin n)
    (hij : ¬(configurationGraph c).Adj i j) : chargeMatrix c i j = 0 := by
  change CappedColor.adjacency (pairColor c i j) ≠ 1 at hij
  rw [chargeMatrix, color_eq_absent_of_not_present _ hij, CappedColor.charge_absent]

/-- A symmetric zero-diagonal matrix counts each unordered pair twice. -/
theorem ordered_sum_eq_twice_upper (y : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, y i j = y j i) (hdiag : ∀ i, y i i = 0) :
    (∑ i, ∑ j, y i j) = 2 * ∑ i, ∑ j, if i < j then y i j else 0 := by
  have hpoint (i j : Fin n) : y i j =
      (if i < j then y i j else 0) + (if j < i then y i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ i, ∑ j, if j < i then y i j else 0) =
      ∑ i, ∑ j, if i < j then y i j else 0 := by
    rw [Finset.sum_comm]
    simp_rw [hsym]
  calc
    _ = (∑ i, ∑ j, if i < j then y i j else 0) +
        ∑ i, ∑ j, if j < i then y i j else 0 := by
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hpoint]
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

theorem sum_cliquePair_eq_upper (f : CliquePair n → ℝ) :
    (∑ e, f e) = ∑ i, ∑ j, if h : i < j then f ⟨(i, j), h⟩ else 0 := by
  let g (p : Fin n × Fin n) : ℝ := if h : p.1 < p.2 then f ⟨p, h⟩ else 0
  have h := Finset.sum_subtype (p := fun p : Fin n × Fin n => p.1 < p.2)
    (F := inferInstance)
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) g
  rw [Finset.sum_filter] at h
  calc
    _ = ∑ e : CliquePair n, g e.val := by
      apply Finset.sum_congr rfl
      intro e _
      simp [g, e.property]
    _ = ∑ p : Fin n × Fin n, if p.1 < p.2 then g p else 0 := h.symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [g, hij]

/-- The sampled unordered color sum is exactly the finite signed-dual
objective, including zero charges on absent pairs. -/
theorem chargeMatrix_objective (c : CliquePair n → CappedColor) :
    WeightedGraph.objective (fun _ => 1) (chargeMatrix c) = ∑ e, CappedColor.charge (c e) := by
  rw [WeightedGraph.objective]
  simp only [mul_one]
  rw [ordered_sum_eq_twice_upper _ (chargeMatrix_symm c) (chargeMatrix_self c),
    sum_cliquePair_eq_upper]
  have hupper : (∑ i, ∑ j, if i < j then chargeMatrix c i j else 0) =
      ∑ i, ∑ j, if h : i < j then CappedColor.charge (c ⟨(i, j), h⟩) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j <;> simp [hij, chargeMatrix, pairColor]
  rw [hupper]
  ring

theorem pairColor_subclique (c : CliquePair n → CappedColor) {k : ℕ}
    (e : Fin k ↪o Fin n) (i j : Fin k) :
    pairColor (fun p => c (pairEmbedding e p)) i j = pairColor c (e i) (e j) := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [pairColor, hij, e.strictMono hij, pairEmbedding]
  · simp
  · simp [pairColor, hij, not_lt.mpr hij.le, e.strictMono hij,
      not_lt.mpr (e.strictMono hij).le, pairEmbedding]

theorem charge_eq_pairCharge (y : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    WeightedGraph.charge y S = FiniteArity.pairCharge S y := by
  rw [WeightedGraph.charge_eq_sum]
  rfl

/-- A subset's matrix charge is exactly the charge of its increasingly
enumerated sampled subclique. -/
theorem chargeMatrix_subset (c : CliquePair n → CappedColor) (S : Finset (Fin n)) :
    WeightedGraph.charge (chargeMatrix c) S =
      ∑ p, CappedColor.charge (c (pairEmbedding (S.orderEmbOfFin rfl) p)) := by
  let e := S.orderEmbOfFin rfl
  have h := FiniteArity.pairCharge_map (Finset.univ : Finset (Fin S.card)) e.toEmbedding
    (chargeMatrix c)
  rw [Finset.map_orderEmbOfFin_univ S rfl] at h
  rw [charge_eq_pairCharge, h]
  change FiniteArity.pairCharge Finset.univ (fun i j => chargeMatrix c (e i) (e j)) = _
  have heq : (fun i j => chargeMatrix c (e i) (e j)) =
      chargeMatrix (fun p => c (pairEmbedding e p)) := by
    funext i j
    exact (congrArg CappedColor.charge (pairColor_subclique c e i j)).symm
  rw [heq]
  rw [← charge_eq_pairCharge]
  have hobj : WeightedGraph.charge
      (chargeMatrix (fun p => c (pairEmbedding e p))) Finset.univ =
      WeightedGraph.objective (fun _ => 1) (chargeMatrix (fun p => c (pairEmbedding e p))) := by
    simp [WeightedGraph.charge_eq_sum, WeightedGraph.objective]
  rw [hobj, chargeMatrix_objective]

/-- All actual sampled subclique tests make the sampled finite signed
charge matrix a genuine feasible finite-graph dual. -/
theorem configuration_dualFeasible (c : CliquePair n → CappedColor)
    (htests : ∀ k, 2 ≤ k → k ≤ n → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    WeightedGraph.DualFeasible (configurationGraph c) (chargeMatrix c) := by
  refine ⟨chargeMatrix_symm c, chargeMatrix_nonedge c, ?_⟩
  intro S hS
  by_cases hcard : 2 ≤ S.card
  · let e := S.orderEmbOfFin rfl
    have ht := htests S.card hcard (by simpa using Finset.card_le_univ S) e
    have hp (p : CliquePair S.card) : CappedColor.adjacency (c (pairEmbedding e p)) = 1 := by
      have h := hS (S.orderEmbOfFin_mem rfl p.val.1) (S.orderEmbOfFin_mem rfl p.val.2)
        (e.strictMono p.property).ne
      change CappedColor.adjacency (pairColor c (e p.val.1) (e p.val.2)) = 1 at h
      rwa [pairColor_lt _ _ _ (e.strictMono p.property)] at h
    simp only [violation, hp, Finset.prod_const_one, mul_one] at ht
    rw [chargeMatrix_subset]
    have hle := le_max_left ((∑ p, CappedColor.charge (c (pairEmbedding e p))) - 1) 0
    rw [ht] at hle
    linarith
  · have hsmall : S.card ≤ 1 := by omega
    rw [charge_eq_pairCharge, FiniteArity.pairCharge_eq_sum_pairs _ _ (chargeMatrix_self c),
      Finset.powersetCard_eq_empty.mpr (by omega), Finset.sum_empty]
    norm_num

end Erdos1017.CappedModel
