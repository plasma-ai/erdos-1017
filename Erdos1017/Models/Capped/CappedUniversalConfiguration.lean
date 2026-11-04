module

public import Erdos1017.Models.Capped.CappedColorConfiguration

/-!
# Universal zero-charge vertices in sampled configurations

Marking vertices as universal with zero incident charge
(`universalConfiguration`) preserves the full tested clique inequality, because
the original-vertex subset is a tested subclique.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.CappedModel

variable {n : ℕ}

def zeroChargePresent : CappedColor := CappedColor.present 0 ⟨by norm_num, by norm_num⟩

@[simp] theorem adjacency_zeroChargePresent : CappedColor.adjacency zeroChargePresent = 1 := rfl

@[simp] theorem charge_zeroChargePresent : CappedColor.charge zeroChargePresent = 0 := rfl

/-- Marked vertices are universal and have zero incident charge. -/
def universalConfiguration (b : Fin n → Bool) (c : CliquePair n → CappedColor)
    (p : CliquePair n) : CappedColor :=
  if b p.val.1 = true ∨ b p.val.2 = true then zeroChargePresent else c p

theorem pairColor_universalConfiguration (b : Fin n → Bool) (c : CliquePair n → CappedColor)
    (i j : Fin n) : pairColor (universalConfiguration b c) i j =
      if i = j then CappedColor.absent else
        if b i = true ∨ b j = true then zeroChargePresent else pairColor c i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [pairColor, universalConfiguration, hij, hij.ne]
  · simp
  · simp [pairColor, universalConfiguration, hij, hij.ne', not_lt.mpr hij.le, or_comm]

theorem chargeMatrix_universalConfiguration (b : Fin n → Bool) (c : CliquePair n → CappedColor)
    (i j : Fin n) : chargeMatrix (universalConfiguration b c) i j =
      if b i = false ∧ b j = false then chargeMatrix c i j else 0 := by
  rw [chargeMatrix, pairColor_universalConfiguration]
  by_cases hij : i = j
  · subst j
    simp
  · cases hbi : b i <;> cases hbj : b j <;> simp_all [chargeMatrix]

theorem configurationGraph_eq_top_of_present (c : CliquePair n → CappedColor)
    (hA : ∀ p, CappedColor.adjacency (c p) = 1) : configurationGraph c = ⊤ := by
  ext i j
  constructor
  · intro hij
    exact hij.ne
  · intro hij
    change i ≠ j at hij
    change CappedColor.adjacency (pairColor c i j) = 1
    rcases lt_or_gt_of_ne hij with h | h
    · rw [pairColor_lt c i j h]
      exact hA _
    · rw [pairColor_symm, pairColor_lt c j i h]
      exact hA _

/-- Universal zero-charge vertices preserve the full tested clique
inequality because its old-vertex subset is an actually tested subclique. -/
theorem violation_universalConfiguration (b : Fin n → Bool) (c : CliquePair n → CappedColor)
    (htests : ∀ k, 2 ≤ k → k ≤ n → ∀ e : Fin k ↪o Fin n,
      violation (fun p => c (pairEmbedding e p)) = 0) :
    violation (universalConfiguration b c) = 0 := by
  classical
  by_cases hz : ∃ p, CappedColor.adjacency (universalConfiguration b c p) = 0
  · obtain ⟨p, hp⟩ := hz
    have hprod : (∏ q, CappedColor.adjacency (universalConfiguration b c q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hp
    simp only [violation, hprod, mul_zero]
  · have hA (p : CliquePair n) : CappedColor.adjacency (universalConfiguration b c p) = 1 :=
      (CappedColor.adjacency_eq_zero_or_one _).resolve_left (fun hp => hz ⟨p, hp⟩)
    have hgraph := configurationGraph_eq_top_of_present (universalConfiguration b c) hA
    let S : Finset (Fin n) := Finset.univ.filter (fun i => b i = false)
    have hS : (configurationGraph c).IsClique (S : Set (Fin n)) := by
      intro i hi j hj hij
      have hbi := (Finset.mem_filter.mp hi).2
      have hbj := (Finset.mem_filter.mp hj).2
      have hnew : (configurationGraph (universalConfiguration b c)).Adj i j := by
        rw [hgraph]
        exact hij
      change CappedColor.adjacency (pairColor (universalConfiguration b c) i j) = 1 at hnew
      rw [pairColor_universalConfiguration] at hnew
      change CappedColor.adjacency (pairColor c i j) = 1
      simpa [hij, hbi, hbj] using hnew
    have hcharge := (configuration_dualFeasible c htests).2.2 S hS
    have hmatrix (i j : Fin n) : chargeMatrix (universalConfiguration b c) i j =
        if i ∈ S ∧ j ∈ S then chargeMatrix c i j else 0 := by
      rw [chargeMatrix_universalConfiguration]
      simp [S]
    have hsum : (∑ p, CappedColor.charge (universalConfiguration b c p)) =
        WeightedGraph.charge (chargeMatrix c) S := by
      rw [← chargeMatrix_objective]
      unfold WeightedGraph.objective WeightedGraph.charge
      simp only [mul_one, hmatrix]
    rw [← hsum] at hcharge
    simp only [violation, max_eq_right (sub_nonpos.mpr hcharge), zero_mul]

end Erdos1017.CappedModel
