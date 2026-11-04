module

public import Erdos1017.IntegerTransfer.MultipartiteTypeMass

/-!
# Pair balance of aggregated profile masses

Aggregating a fractional clique partition over profiles gives exact total mass
on every role pair (`typeMass_pair_balance`), bounds each profile mass by the
edge count of any pair it uses, and preserves the total fractional objective
(`sum_typeMass_eq`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual number of graph edges between two labelled parts. -/
def pairEdgeCount (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj] (i j : Fin ℓ) : ℕ :=
  (Finset.univ.filter (fun p : A × A => G.Adj (i, p.1) (j, p.2))).card

/-- Exact fractional edge balance also determines the zero load on nonedges
between distinct roles, because every nonzero weight belongs to an actual clique. -/
theorem pairLoad_eq_bit (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (i j : Fin ℓ) (hij : i ≠ j) (a b : A) :
    pairLoad w (i, a) (j, b) = if G.Adj (i, a) (j, b) then 1 else 0 := by
  by_cases hadj : G.Adj (i, a) (j, b)
  · exact (hbalance _ _ hadj).trans (ite_eq_left hadj).symm
  · rw [ite_eq_right hadj]
    apply Finset.sum_eq_zero
    intro S _
    by_cases hz : w S = 0
    · simp [hz]
    · apply ite_eq_right
      rintro ⟨ha, hb⟩
      exact hadj (hsupport S hz ha hb (fun h => hij (congrArg Prod.fst h)))

omit [DecidableEq A] in
/-- The sum of actual edge indicators is the actual part-pair cardinality. -/
theorem pairEdgeCount_eq_sum (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (i j : Fin ℓ) :
    (pairEdgeCount G i j : ℝ) = ∑ a : A, ∑ b : A, if G.Adj (i, a) (j, b) then (1 : ℝ) else 0 := by
  rw [pairEdgeCount, Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter, Fintype.sum_prod_type]

/-- Aggregating an actual fractional clique partition gives exact total mass
on every role pair. These masses determine a mutually exclusive allocation law. -/
theorem typeMass_pair_balance (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (i j : Fin ℓ) (hij : i ≠ j) :
    (∑ K, if i ∈ K ∧ j ∈ K then typeMass w K else 0) = (pairEdgeCount G i j : ℝ) := by
  rw [typeMass_pair_sum w (fun S hS => profile_injOn G hparts S (hsupport S hS)), pairEdgeCount_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact pairLoad_eq_bit G w hsupport hbalance i j hij a b

/-- A single profile's mass cannot exceed the total number of edges in any
part pair that profile uses. -/
theorem typeMass_le_pairEdgeCount (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (K : Finset (Fin ℓ)) (i j : Fin ℓ) (hij : i ≠ j) (hi : i ∈ K) (hj : j ∈ K) :
    typeMass w K ≤ (pairEdgeCount G i j : ℝ) := by
  rw [← typeMass_pair_balance G hparts w hsupport hbalance i j hij]
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun K => if i ∈ K ∧ j ∈ K then typeMass w K else 0)
    (fun K _ => by split_ifs; exact typeMass_nonneg w hw K; exact le_rfl) (Finset.mem_univ K)
  simpa only [ite_eq_left (show i ∈ K ∧ j ∈ K from ⟨hi, hj⟩)] using h

omit [DecidableEq A] in
/-- Nonzero profile mass has an actual nonzero clique-weight witness. -/
theorem typeMass_witness (w : Finset (Fin ℓ × A) → ℝ) (K : Finset (Fin ℓ))
    (hK : typeMass w K ≠ 0) : ∃ S, profile S = K ∧ w S ≠ 0 := by
  by_contra h
  push Not at h
  apply hK
  apply Finset.sum_eq_zero
  intro S _
  by_cases hs : profile S = K
  · simp only [ite_eq_left hs, h S hs]
  · exact ite_eq_right hs

omit [DecidableEq A] in
/-- Profile aggregation preserves the exact total fractional objective. -/
theorem sum_typeMass_eq (w : Finset (Fin ℓ × A) → ℝ) :
    (∑ K, typeMass w K) = ∑ S, w S := by simpa using sum_typeMass w (fun _ => 1)

end Erdos1017.MultipartiteAllocation
