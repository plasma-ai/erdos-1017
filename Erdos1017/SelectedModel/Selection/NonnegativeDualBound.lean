module

public import Erdos1017.LowerBound.WeightedGraphRealization
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Half bound for a nonnegative dual

A nonnegative feasible dual plus adjacency has weighted objective at most one
half.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {n : ℕ}

private def combined (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := fun i j => adjacencyMatrix G i j + y i j

private def support (w : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i ≠ 0

private def squareMass (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2

private def direction (u v : Fin n) (i : Fin n) : ℝ :=
  if i = u then 1 else if i = v then -1 else 0

private def transfer (w : Fin n → ℝ) (u v : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun i => w i + t * direction u v i

private theorem transfer_at_left (w : Fin n → ℝ) (u v : Fin n) (t : ℝ) :
    transfer w u v t u = w u + t := by
  simp [transfer, direction]

private theorem transfer_at_right (w : Fin n → ℝ) (u v : Fin n) (t : ℝ)
    (huv : u ≠ v) : transfer w u v t v = w v - t := by
  simp [transfer, direction, huv.symm]
  ring

private theorem transfer_at_other (w : Fin n → ℝ) (u v i : Fin n) (t : ℝ)
    (hiu : i ≠ u) (hiv : i ≠ v) : transfer w u v t i = w i := by
  simp [transfer, direction, hiu, hiv]

private theorem transfer_sum (w : Fin n → ℝ) (u v : Fin n) (t : ℝ)
    (huv : u ≠ v) : ∑ i, transfer w u v t i = ∑ i, w i := by
  simp only [transfer, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hshift : (∑ i : Fin n, direction u v i) = 0 := by
    have hcard : (Finset.univ.filter (· = u)).card = 1 := by
      have heq : Finset.univ.filter (· = u) = {u} := by ext i; simp
      rw [heq]
      simp
    simp [direction, Finset.sum_ite, huv.symm, hcard]
  rw [hshift]
  ring

private theorem objective_transfer_barycentric (c : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (u v : Fin n)
    (hzero : ∀ i j, c i j * direction u v i * direction u v j = 0) :
    w u * objective (transfer w u v (w v)) c +
      w v * objective (transfer w u v (-w u)) c =
        (w u + w v) * objective w c := by
  have hterm (i j : Fin n) :
      w u * (c i j * (transfer w u v (w v) i * transfer w u v (w v) j)) +
        w v * (c i j * (transfer w u v (-w u) i * transfer w u v (-w u) j)) =
          (w u + w v) * (c i j * (w i * w j)) := by
    unfold transfer
    calc
      _ = (w u + w v) * (c i j * (w i * w j)) +
          w u * w v * (w u + w v) *
            (c i j * direction u v i * direction u v j) := by ring
      _ = _ := by rw [hzero i j]; ring
  have hsum :
      w u * (∑ i, ∑ j, c i j * (transfer w u v (w v) i * transfer w u v (w v) j)) +
        w v * (∑ i, ∑ j, c i j * (transfer w u v (-w u) i * transfer w u v (-w u) j)) =
          (w u + w v) * (∑ i, ∑ j, c i j * (w i * w j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hterm i j
  unfold objective
  calc
    _ = (w u * (∑ i, ∑ j, c i j * (transfer w u v (w v) i * transfer w u v (w v) j)) +
          w v * (∑ i, ∑ j, c i j * (transfer w u v (-w u) i * transfer w u v (-w u) j))) / 2 := by ring
    _ = _ := by rw [hsum]; ring

private theorem combined_zero_of_nonadjacent (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y)
    (u v : Fin n) (hno : ¬G.Adj u v) (i j : Fin n) :
    combined G y i j * direction u v i * direction u v j = 0 := by
  have hdiag (a : Fin n) : combined G y a a = 0 := by
    have hno' : ¬G.Adj a a := fun h => G.irrefl h
    simp [combined, adjacencyMatrix, hy.2.1 a a hno']
  have huv : combined G y u v = 0 := by
    simp [combined, adjacencyMatrix, hno, hy.2.1 u v hno]
  have hvu : combined G y v u = 0 := by
    have hno' : ¬G.Adj v u := fun h => hno h.symm
    simp [combined, adjacencyMatrix, hno', hy.2.1 v u hno']
  by_cases hiu : i = u
  · subst i
    by_cases hju : j = u
    · subst j
      simp [hdiag]
    · by_cases hjv : j = v
      · subst j
        simp [huv]
      · simp [direction, hju, hjv]
  · by_cases hiv : i = v
    · subst i
      by_cases hju : j = u
      · subst j
        simp [hvu]
      · by_cases hjv : j = v
        · subst j
          simp [hdiag]
        · simp [direction, hju, hjv]
    · simp [direction, hiu, hiv]

private theorem transfer_left_nonneg (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u v : Fin n) (huv : u ≠ v) :
    ∀ i, 0 ≤ transfer w u v (w v) i := by
  intro i
  by_cases hiu : i = u
  · subst i
    rw [transfer_at_left w u v (w v)]
    exact add_nonneg (hw u) (hw v)
  · by_cases hiv : i = v
    · subst i
      rw [transfer_at_right w u v (w v) huv]
      simp
    · rw [transfer_at_other w u v i (w v) hiu hiv]
      exact hw i

private theorem transfer_right_nonneg (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u v : Fin n) (huv : u ≠ v) :
    ∀ i, 0 ≤ transfer w u v (-w u) i := by
  intro i
  by_cases hiu : i = u
  · subst i
    rw [transfer_at_left w u v (-w u)]
    simp
  · by_cases hiv : i = v
    · subst i
      rw [transfer_at_right w u v (-w u) huv]
      linarith [hw u, hw v]
    · rw [transfer_at_other w u v i (-w u) hiu hiv]
      exact hw i

private theorem support_transfer_left_ssubset (w : Fin n → ℝ)
    (u v : Fin n) (huv : u ≠ v) (hu : w u ≠ 0) (hv : w v ≠ 0) :
    support (transfer w u v (w v)) ⊂ support w := by
  have hsub : support (transfer w u v (w v)) ⊆ support w := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hiu : i = u
    · simpa [hiu] using hu
    · by_cases hiv : i = v
      · subst i
        rw [transfer_at_right w u v (w v) huv] at hi
        exact (by simp at hi)
      · rwa [transfer_at_other w u v i (w v) hiu hiv] at hi
  apply (Finset.ssubset_iff_of_subset hsub).mpr
  refine ⟨v, ?_, ?_⟩
  · simpa [support] using hv
  · simp [support, transfer_at_right w u v (w v) huv]

private theorem support_transfer_right_ssubset (w : Fin n → ℝ)
    (u v : Fin n) (hu : w u ≠ 0) (hv : w v ≠ 0) :
    support (transfer w u v (-w u)) ⊂ support w := by
  have hsub : support (transfer w u v (-w u)) ⊆ support w := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hiu : i = u
    · subst i
      rw [transfer_at_left w u v (-w u)] at hi
      exact (by simp at hi)
    · by_cases hiv : i = v
      · simpa [hiv] using hv
      · rwa [transfer_at_other w u v i (-w u) hiu hiv] at hi
  apply (Finset.ssubset_iff_of_subset hsub).mpr
  refine ⟨u, ?_, ?_⟩
  · simpa [support] using hu
  · simp [support, transfer_at_left w u v (-w u)]

private theorem objective_combined (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (w : Fin n → ℝ) :
    objective w (combined G y) = objective w y + density G w := by
  change objective w (combined G y) = objective w y + objective w (adjacencyMatrix G)
  unfold objective combined
  simp only [add_mul, Finset.sum_add_distrib]
  ring

private theorem exists_nonedge_transfer (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (u v : Fin n) (huv : u ≠ v) (hno : ¬G.Adj u v)
    (hu : 0 < w u) (hv : 0 < w v) :
    ∃ w' : Fin n → ℝ, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i = 1) ∧
      (support w').card < (support w).card ∧
      objective w (combined G y) ≤ objective w' (combined G y) := by
  let w₁ := transfer w u v (w v)
  let w₂ := transfer w u v (-w u)
  have hbar := objective_transfer_barycentric (combined G y) w u v
    (combined_zero_of_nonadjacent G y hy u v hno)
  by_cases hleft : objective w (combined G y) ≤ objective w₁ (combined G y)
  · refine ⟨w₁, transfer_left_nonneg w hw u v huv,
      (transfer_sum w u v (w v) huv).trans hsum, ?_, hleft⟩
    exact Finset.card_lt_card (support_transfer_left_ssubset w u v huv hu.ne' hv.ne')
  · have hright : objective w (combined G y) ≤ objective w₂ (combined G y) := by
      by_contra hnot
      have h₁ := mul_lt_mul_of_pos_left (lt_of_not_ge hleft) hu
      have h₂ := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hv
      dsimp only [w₁, w₂] at h₁ h₂
      linarith
    refine ⟨w₂, transfer_right_nonneg w hw u v huv,
      (transfer_sum w u v (-w u) huv).trans hsum, ?_, hright⟩
    exact Finset.card_lt_card (support_transfer_right_ssubset w u v hu.ne' hv.ne')

private theorem pair_product_le_half_squareMass (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) : w i * w j ≤ squareMass w / 2 := by
  have hpair : w i ^ 2 + w j ^ 2 ≤ squareMass w := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (fun k _ _ => sq_nonneg (w k))
    simpa [Finset.sum_pair hij, squareMass] using h
  nlinarith [sq_nonneg (w i - w j)]

private theorem objective_le_half_squareMass (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y)
    (hy_nonneg : ∀ i j, 0 ≤ y i j)
    (w : Fin n → ℝ) (hclique : G.IsClique (support w : Set (Fin n))) :
    objective w y ≤ squareMass w / 2 := by
  let S := support w
  let Q := squareMass w
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  have hterm (i j : Fin n) :
      y i j * (w i * w j) ≤
        (Q / 2) * (if i ∈ S ∧ j ∈ S then y i j else 0) := by
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp only [hi, hj, and_self, ite_true]
        by_cases hij : i = j
        · subst j
          have hdiag : y i i = 0 := hy.2.1 i i (fun h => G.irrefl h)
          simp [hdiag]
        · have hbound := pair_product_le_half_squareMass w i j hij
          have hmul := mul_le_mul_of_nonneg_left hbound (hy_nonneg i j)
          dsimp only [Q] at *
          nlinarith
      · have hz : w j = 0 := by
          by_contra h
          exact hj (by simp [S, support, h])
        simp [hz, hj]
    · have hz : w i = 0 := by
        by_contra h
        exact hi (by simp [S, support, h])
      simp [hz, hi]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, y i j * (w i * w j)) ≤
      (Q / 2) * (∑ i : Fin n, ∑ j : Fin n,
        if i ∈ S ∧ j ∈ S then y i j else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact hterm i j
  have hcharge : charge y S ≤ 1 := hy.2.2 S hclique
  have hscaled : (Q / 2) * charge y S ≤ Q / 2 :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcharge (div_nonneg hQ (by norm_num))
  unfold objective charge at *
  dsimp only [Q] at *
  nlinarith only [hsum, hscaled]

private theorem density_eq_half_complement_squareMass (G : SimpleGraph (Fin n))
    (w : Fin n → ℝ) (hsum : ∑ i, w i = 1)
    (hclique : G.IsClique (support w : Set (Fin n))) :
    density G w = (1 - squareMass w) / 2 := by
  let S := support w
  have hterm (i j : Fin n) :
      adjacencyMatrix G i j * (w i * w j) =
        w i * w j - if i = j then w i ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [adjacencyMatrix, pow_two]
    · by_cases hi : i ∈ S
      · by_cases hj : j ∈ S
        · have hadj : G.Adj i j := hclique hi hj hij
          simp [adjacencyMatrix, hadj, hij]
        · have hz : w j = 0 := by
            by_contra h
            exact hj (by simp [S, support, h])
          simp [hz, hij]
      · have hz : w i = 0 := by
          by_contra h
          exact hi (by simp [S, support, h])
        simp [hz, hij]
  have hprod : (∑ i : Fin n, ∑ j : Fin n, w i * w j) = (∑ i, w i) ^ 2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hdiag : (∑ i : Fin n, ∑ j : Fin n, if i = j then w i ^ 2 else 0) = squareMass w := by
    simp [squareMass]
  have htotal : (∑ i : Fin n, ∑ j : Fin n,
      adjacencyMatrix G i j * (w i * w j)) = 1 - squareMass w := by
    simp_rw [hterm]
    simp only [Finset.sum_sub_distrib]
    rw [hprod, hdiag, hsum]
    ring
  change (∑ i : Fin n, ∑ j : Fin n,
    adjacencyMatrix G i j * (w i * w j)) / 2 = _
  rw [htotal]

/-- A nonnegative feasible dual plus adjacency has weighted objective at most one half. -/
theorem nonnegative_dual_objective_add_density_le_half (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y)
    (hy_nonneg : ∀ i j, 0 ≤ y i j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    objective w y + density G w ≤ 1 / 2 := by
  have hbound : ∀ k : ℕ, ∀ v : Fin n → ℝ,
      (support v).card = k → (∀ i, 0 ≤ v i) → (∑ i, v i = 1) →
        objective v (combined G y) ≤ 1 / 2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hcard hv hsumv
      by_cases hclique : G.IsClique (support v : Set (Fin n))
      · have hybound := objective_le_half_squareMass G y hy hy_nonneg v hclique
        have hden := density_eq_half_complement_squareMass G v hsumv hclique
        rw [objective_combined, hden]
        linarith
      · have hex : ∃ u ∈ support v, ∃ z ∈ support v, u ≠ z ∧ ¬G.Adj u z := by
          simp only [SimpleGraph.IsClique, Set.Pairwise] at hclique
          push Not at hclique
          simpa only [Finset.mem_coe] using hclique
        obtain ⟨u, hu, z, hz, huz, hno⟩ := hex
        have hupos : 0 < v u := by
          have hne : v u ≠ 0 := by simpa [support] using hu
          exact lt_of_le_of_ne (hv u) (Ne.symm hne)
        have hzpos : 0 < v z := by
          have hne : v z ≠ 0 := by simpa [support] using hz
          exact lt_of_le_of_ne (hv z) (Ne.symm hne)
        obtain ⟨v', hv', hsum', hsmall, hobj⟩ :=
          exists_nonedge_transfer G y hy v hv hsumv u z huz hno hupos hzpos
        exact hobj.trans (ih (support v').card (by simpa [← hcard] using hsmall)
          v' rfl hv' hsum')
  have h := hbound (support w).card w rfl hw hsum
  rwa [objective_combined] at h

end Erdos1017.WeightedGraph
