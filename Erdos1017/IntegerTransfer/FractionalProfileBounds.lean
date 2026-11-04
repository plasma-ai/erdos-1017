module

public import Erdos1017.IntegerTransfer.ProfileMassBudget
public import Erdos1017.IntegerTransfer.MultipartiteProfileRegularity

/-!
# Size and total bounds on profile masses

Bounded clique support gives the same size bounds for every nonzero aggregate
profile mass (`typeMass_card_bounds`), and the fractional objective is at most
the square of the ambient order (`typeMass_total_le_square`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ b : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Actual bounded clique support gives the same size bounds for every
nonzero aggregate profile mass. -/
theorem typeMass_card_bounds (G : SimpleGraph (Fin ℓ × A))
    (hparts : ∀ i (a z : A), ¬G.Adj (i, a) (i, z))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → 2 ≤ S.card ∧ S.card ≤ b ∧ G.IsClique (S : Set (Fin ℓ × A)))
    (K : Finset (Fin ℓ)) (hK : typeMass w K ≠ 0) : 2 ≤ K.card ∧ K.card ≤ b := by
  obtain ⟨S, hprofile, hw⟩ := typeMass_witness w K hK
  have hS := hsupport S hw
  have hcard := profile_card S (profile_injOn G hparts S hS.2.2)
  rw [hprofile] at hcard
  exact hcard ▸ ⟨hS.1, hS.2.1⟩

/-- The actual fractional objective is at most the square of the ambient order. -/
theorem typeMass_total_le_square (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a z : A), ¬G.Adj (i, a) (i, z))
    (w : Finset (Fin ℓ × A) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hsupport : ∀ S, w S ≠ 0 → 2 ≤ S.card ∧ G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1) :
    (∑ K, typeMass w K) ≤ (ℓ * Fintype.card A : ℕ) ^ 2 := by
  have hmass := typeMass_nonneg w hw
  have hbound : (∑ K, typeMass w K) ≤ ∑ K, (K.card.choose 2 : ℝ) * typeMass w K := by
    apply Finset.sum_le_sum
    intro K _
    by_cases hz : typeMass w K = 0
    · simp only [hz, mul_zero, le_refl]
    obtain ⟨S, hprofile, hS⟩ := typeMass_witness w K hz
    have hcard : 2 ≤ K.card := by
      rw [← hprofile, profile_card S (profile_injOn G hparts S (hsupport S hS).2)]
      exact (hsupport S hS).1
    have hchoose : (1 : ℝ) ≤ K.card.choose 2 := by exact_mod_cast Nat.choose_pos hcard
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hchoose (hmass K)
  rw [typeMass_pair_mass G hparts w (fun S hS => (hsupport S hS).2) hbalance] at hbound
  have hcount : ((TransversalClique.graphEdges G).card : ℝ) ≤ (ℓ * Fintype.card A : ℕ) ^ 2 := by
    have h := Finset.card_le_univ (TransversalClique.graphEdges G)
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, pow_two] using
      (show ((TransversalClique.graphEdges G).card : ℝ) ≤ Fintype.card (TransversalThinning.Coordinate ℓ A) by exact_mod_cast h)
  exact hbound.trans hcount

end Erdos1017.MultipartiteAllocation
