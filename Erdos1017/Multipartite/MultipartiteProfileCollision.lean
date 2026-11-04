module

public import Erdos1017.Multipartite.MultipartiteCollision
public import Erdos1017.Multipartite.MultipartiteDensitySelection

/-!
# Collision estimate for profile values

Equal dust cells transfer the finite anchored collision estimate to a fixed
finite-head coefficient value, the residual dust-square term can be removed, and
the countable profile value inherits the bound with only the atomic square
masses remaining.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Equal dust cells transfer the finite anchored collision estimate to a
fixed finite-head coefficient value, with the cell-square error. -/
theorem value_le_split_add_square_error {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) :
    value p s ≤ (1 + (∑ i, p i) + s) ^ 2 *
        Benchmark.splitValue (1 / (1 + (∑ i, p i) + s)) +
      (∑ i, p i ^ 2) / 2 + s ^ 2 / (2 * n) := by
  let q := DustPaddedCells.target p s n
  let M := 1 + (∑ i, p i) + s
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := DustPaddedCells.target_cube p hp s hs n hn hsn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 < M := by
    dsimp [M]
    have hpnonneg : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => (hp i).1)
    linarith
  have hsumq : (∑ i, q i) = (∑ i, p i) + s := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hsquareq : (∑ i, q i ^ 2) = (∑ i, p i ^ 2) + s ^ 2 / n := by
    dsimp [q]
    rw [Fin.sum_univ_add]
    simp only [DustPaddedCells.target_head, DustPaddedCells.target_cell,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  let a : Option (Fin (m + n)) → ℝ :=
    fun i => (1 / M) * Multipartite.anchorMasses q i
  have ha : 0 < a none := by simp [a, Multipartite.anchorMasses, hM]
  have hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none := by
    intro i
    simp only [a, Multipartite.anchorMasses, Option.elim']
    constructor
    · exact mul_nonneg (by positivity) (hq i).1
    · exact mul_le_mul_of_nonneg_left (hq i).2 (by positivity)
  have hasum : ∑ i, a i = 1 := by
    calc
      ∑ i, a i = (1 + ∑ i, q i) / M := by
        simp only [Fintype.sum_option, a, Multipartite.anchorMasses, Option.elim',
          ← Finset.mul_sum]
        ring
      _ = 1 := by
        rw [hsumq]
        rw [show 1 + ((∑ i, p i) + s) = M by dsimp [M]; ring]
        exact div_self hM.ne'
  have htail : (∑ i, a (some i) ^ 2) = (∑ i, q i ^ 2) / M ^ 2 := by
    simp only [a, Multipartite.anchorMasses, Option.elim', mul_pow,
      ← Finset.mul_sum]
    field_simp
  have hcollision := Multipartite.value_le_split_add_collision a ha hsecondary hasum
  have hanchor := Multipartite.closed_anchoring q hq (1 / M)
  change Multipartite.value a = (1 / M) ^ 2 * Selector.value q at hanchor
  rw [hanchor, show a none = 1 / M by simp [a, Multipartite.anchorMasses], htail] at hcollision
  have hcell := (DustPaddedCells.finite_cell_value_error p hp s hs n hn hsn).1
  have hbound : Selector.value q ≤ M ^ 2 * Benchmark.splitValue (1 / M) +
      (∑ i, q i ^ 2) / 2 := by
    have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
    have hinv : M ^ 2 * (1 / M) ^ 2 = 1 := by field_simp
    calc
      Selector.value q = M ^ 2 * ((1 / M) ^ 2 * Selector.value q) := by
        rw [← mul_assoc, hinv, one_mul]
      _ ≤ M ^ 2 * (Benchmark.splitValue (1 / M) +
          (∑ i, q i ^ 2) / M ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcollision hM2.le
      _ = M ^ 2 * Benchmark.splitValue (1 / M) + (∑ i, q i ^ 2) / 2 := by
        field_simp
  rw [hsquareq] at hbound
  change 0 ≤ Selector.value q - value p s at hcell
  dsimp only [M] at hbound
  have hsplit : ((∑ i, p i ^ 2) + s ^ 2 / n) / 2 =
      (∑ i, p i ^ 2) / 2 + s ^ 2 / (2 * n) := by
    field_simp [hnreal.ne']
  rw [hsplit] at hbound
  linarith

/-- The actual finite-head dust value obeys the anchored collision estimate
without a residual dust-square term. -/
theorem value_le_split_add_square {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    value p s ≤ (1 + (∑ i, p i) + s) ^ 2 *
        Benchmark.splitValue (1 / (1 + (∑ i, p i) + s)) +
      (∑ i, p i ^ 2) / 2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / (2 * ε)))
  have hnreal : (0 : ℝ) < n := by
    exact lt_of_le_of_lt hs ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hnreal
  have hsn : s ≤ n := (le_max_left _ _).trans hn.le
  have hsmall : s ^ 2 / (2 * (n : ℝ)) < ε := by
    have h := (le_max_right s (s ^ 2 / (2 * ε))).trans_lt hn
    have h' := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp h
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [sq_nonneg s]
  linarith [value_le_split_add_square_error p hp s hs n hn0 hsn]

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteProfiles

/-- The countable profile value inherits the finite anchored collision bound;
only the atomic square masses remain after dust is refined into cells. -/
theorem normalizedValue_le_split_add_square {L : ℝ} {x : Profile}
    (hx : x ∈ space L) :
    normalizedValue x ≤ Benchmark.splitValue (1 / (1 + x.1)) +
      (∑' i, (x.2 i) ^ 2) / (2 * (1 + x.1) ^ 2) := by
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  have hM2 : 0 < (1 + x.1) ^ 2 := sq_pos_of_pos hM
  have hraw : limitValue x ≤ (1 + x.1) ^ 2 * Benchmark.splitValue (1 / (1 + x.1)) +
      (∑' i, (x.2 i) ^ 2) / 2 := by
    unfold limitValue
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    have hp : ∀ i : Fin n, 0 ≤ x.2 i.val ∧ x.2 i.val ≤ 1 :=
      fun i => ⟨hx.1.1.2 i.val, hx.1.2.2 i.val⟩
    have hsum : (∑ i : Fin n, x.2 i.val) + residual n x = x.1 := by
      rw [Fin.sum_univ_eq_sum_range]
      unfold residual
      ring
    have hsquares : (∑ i : Fin n, (x.2 i.val) ^ 2) ≤ ∑' i, (x.2 i) ^ 2 := by
      simpa only [← Fin.sum_univ_eq_sum_range] using
        Summable.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg (x.2 i))
          (squares_summable hx)
    have h := MultipartiteDust.value_le_split_add_square
      (fun i : Fin n => x.2 i.val) hp (residual n x) (residual_nonneg hx n)
    unfold finiteValue
    rw [add_assoc, hsum] at h
    linarith
  unfold normalizedValue
  apply (div_le_iff₀ hM2).mpr
  calc
    limitValue x ≤ (1 + x.1) ^ 2 * Benchmark.splitValue (1 / (1 + x.1)) +
        (∑' i, (x.2 i) ^ 2) / 2 := hraw
    _ = (Benchmark.splitValue (1 / (1 + x.1)) +
        (∑' i, (x.2 i) ^ 2) / (2 * (1 + x.1) ^ 2)) * (1 + x.1) ^ 2 := by
      field_simp

end Erdos1017.MultipartiteProfiles
