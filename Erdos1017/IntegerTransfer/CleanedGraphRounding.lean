module

public import Erdos1017.IntegerTransfer.ProfilePackingCost
public import Erdos1017.IntegerTransfer.FractionalProfileBounds
public import Erdos1017.IntegerTransfer.RoundingCostBudget

/-!
# Rounding bounded fractional partitions on cleaned graphs

Bounded fractional clique partitions of sufficiently large equal-part cleaned
graphs round to integer partitions on the same graph, with the regularity
tolerance chosen in advance (`exists_cleaned_rounding_tolerance`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators
open TransversalThinning TransversalClique

/-- Actual bounded fractional clique partitions of sufficiently large equal-part
cleaned graphs round on the same graph. The regularity tolerance is chosen
before the partition bound and allocation floor. -/
theorem exists_cleaned_rounding_tolerance (b : ℕ) (hb : 3 ≤ b) (δ τ : ℝ)
    (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (p C : ℕ), 0 < C → 1 ≤ (C : ℝ) * δ →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ p →
        ∀ (G : SimpleGraph (Fin ℓ × Fin n)) [DecidableRel G.Adj],
          (∀ i (a z : Fin n), ¬G.Adj (i, a) (i, z)) →
          ∀ (w : Finset (Fin ℓ × Fin n) → ℝ), (∀ S, 0 ≤ w S) →
          (∀ S, w S ≠ 0 → 2 ≤ S.card ∧ S.card ≤ b ∧ G.IsClique (S : Set (Fin ℓ × Fin n))) →
          (∀ v z, G.Adj v z → pairLoad w v z = 1) →
          ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
          (∀ i j : Fin ℓ, i < j → (∀ a z : Fin n, ¬G.Adj (i, a) (j, z)) ∨
            (G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
              δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j))) →
          ∀ (N : ℕ) (f : (Fin ℓ × Fin n) ↪ Fin N),
            (cliquePartitionNumber (G.map f) : ℝ) ≤ (∑ S, w S) + τ * (ℓ * n : ℕ) ^ 2 := by
  classical
  let R : ℝ := b.choose 2
  have hR : 0 < R := by
    dsimp only [R]
    exact_mod_cast Nat.choose_pos (show 2 ≤ b by omega)
  let ρ := τ / (16 * (R + 1))
  have hρ : 0 < ρ := div_pos hτ (by dsimp only [R]; positivity)
  have hρτ : ρ ≤ τ / 16 := by
    dsimp only [ρ]
    exact div_le_div_of_nonneg_left hτ.le (by norm_num) (by linarith)
  obtain ⟨ε₀, hε₀, hprofile⟩ := exists_coupled_profile_matchings b hb δ ρ hδ hρ
  refine ⟨ε₀, hε₀, ?_⟩
  intro p C hC hscale
  let M := 2 ^ p * C
  have hM : 0 < M := Nat.mul_pos (pow_pos (by omega) _) hC
  let α₀ := τ / (16 * (M : ℝ) * R)
  have hα₀ : 0 < α₀ := by
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    dsimp only [α₀]
    positivity
  obtain ⟨n₀, hn₀, hsize⟩ := hprofile M α₀ hα₀
  refine ⟨n₀, hn₀, ?_⟩
  intro n hn ℓ hℓ hℓp G _ hparts w hw hsupport hbalance ε hε hsmall hclean N f
  have hnpos : 0 < n := hn₀.trans_le hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  let mass := typeMass w
  let Q : ℝ := (ℓ * n : ℕ) ^ 2
  let P := pairProfileMass mass
  let L := largeLayers n C mass α₀
  have hmass : ∀ K, 0 ≤ mass K := typeMass_nonneg w hw
  have hcard : ∀ K, mass K ≠ 0 → 2 ≤ K.card ∧ K.card ≤ b :=
    typeMass_card_bounds G hparts w hsupport
  have hL : ∀ s ∈ L, 3 ≤ s.1.card ∧ s.1.card ≤ b :=
    largeLayers_card_bounds mass hcard α₀ hα₀ hnpos hC
  have hLM : L.card ≤ M := by
    have h := Finset.card_le_univ L
    have hpow : 2 ^ ℓ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hℓp
    apply h.trans
    simpa only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, M] using Nat.mul_le_mul_right C hpow
  have hfloor : ∀ s ∈ L, α₀ ≤ allocationDensity n C (mass s.1) :=
    fun s hs => ((largeLayers_mem mass α₀ s).mp hs).2
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hP : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro K _
    split_ifs
    · exact hmass K
    · exact le_rfl
  have htotal : (∑ K, mass K) ≤ Q := by
    simpa only [Q, Fintype.card_fin] using typeMass_total_le_square G hparts w hw
      (fun S hS => ⟨(hsupport S hS).1, (hsupport S hS).2.2⟩) hbalance
  have hbig : 0 ≤ ∑ i : L, mass i.val.1 / C :=
    Finset.sum_nonneg (fun i _ => div_nonneg (hmass _) (Nat.cast_nonneg C))
  have hsplit : P + (∑ i : L, mass i.val.1 / C) ≤ ∑ K, mass K :=
    pair_add_large_mass_le mass hmass α₀ hC
  have hPQ : P ≤ Q := by linarith only [hsplit, htotal, hbig]
  have hden : 0 < P + τ * Q / 4 := by positivity
  let Z (X : Coordinate ℓ (Fin n) → AllocationLabel ℓ C) :=
    ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ) / (P + τ * Q / 4)
  have hZ : ∀ X, 0 ≤ Z X := fun X => div_nonneg (Nat.cast_nonneg _) hden.le
  have hmean : (∑ X, CategoricalSampling.weight (allocationProbability G mass C) X * Z X) ≤
      1 - min ρ (1 / 2) := by
    have hres := residualAllocatedEdges_expectation G hparts w
      (fun S hS => (hsupport S hS).2.2) hbalance hC L
    have hbudget := unselected_layer_mass_le mass hmass hcard α₀ hα₀ hnpos hC
    have hMbound : ((2 ^ ℓ * C : ℕ) : ℝ) ≤ M := by
      exact_mod_cast Nat.mul_le_mul_right C (Nat.pow_le_pow_right (by omega) hℓp)
    have hcoeff : (M : ℝ) * R * α₀ = τ / 16 := by dsimp only [α₀]; field_simp
    have hsizeQ : (n : ℝ) ^ 2 ≤ Q := by
      have hmul : n ≤ ℓ * n := by nlinarith only [hℓ]
      have hmul' : (n : ℝ) ≤ (ℓ * n : ℕ) := by exact_mod_cast hmul
      exact pow_le_pow_left₀ hnp.le hmul' 2
    have hsmallcost : (2 ^ ℓ * C : ℕ) * (b.choose 2 : ℝ) * α₀ * (n : ℝ) ^ 2 ≤ τ * Q / 16 := by
      have h1 := mul_le_mul_of_nonneg_right hMbound
        (show 0 ≤ R * α₀ * (n : ℝ) ^ 2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hsizeQ (div_nonneg hτ.le (by norm_num : (0 : ℝ) ≤ 16))
      dsimp only [R] at hcoeff h1
      nlinarith only [hcoeff, h1, h2]
    have hB : (∑ X, CategoricalSampling.weight (allocationProbability G mass C) X *
        ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ)) ≤ P + τ * Q / 16 := by
      rw [hres]
      exact hbudget.trans (add_le_add_right hsmallcost P)
    simp only [Z, ← mul_div_assoc, ← Finset.sum_div]
    exact normalized_residual_budget hP hPQ hQ hτ hτ1 hρ hρτ hB
  obtain ⟨X, hX, hZX, T, hsub, hdisjoint, hmatching, horder⟩ :=
    hsize n hn ℓ C hC hscale G hparts w hw (fun S hS => (hsupport S hS).2.2) hbalance
      ε hε hsmall hclean L hL hLM hfloor Z hZ hmean
  have hcost := cliquePartitionNumber_map_le_profile_cost G hparts f mass hmass L hL X ρ hρ.le T hsub hdisjoint hmatching horder
  have hrescost : ((residualAllocatedEdges G X (fun i : L => some i.val)).card : ℝ) < P + τ * Q / 4 :=
    (div_lt_one hden).mp hZX
  have hinflate : (1 + ρ * (b.choose 2 : ℝ)) * (1 + ρ) ≤ 1 + τ / 8 :=
    matching_inflation_le hR.le hτ hτ1
  have htotalcost := mul_le_mul_of_nonneg_right hinflate hbig
  have hbigQ : (∑ i : L, mass i.val.1 / C) ≤ Q := by linarith only [hsplit, hP, htotal]
  have herror := mul_le_mul_of_nonneg_left hbigQ (div_nonneg hτ.le (by norm_num : (0 : ℝ) ≤ 8))
  rw [← sum_typeMass_eq w]
  change (cliquePartitionNumber (G.map f) : ℝ) ≤ (∑ K, mass K) + τ * Q
  nlinarith only [hcost, hrescost, hsplit, htotalcost, herror, mul_pos hτ hQ]

end Erdos1017.MultipartiteAllocation
