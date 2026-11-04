module

public import Erdos1017.Multipartite.Countable.CountableTypeCompletion
public import Erdos1017.Multipartite.Dust.DustTwoHeadChord

/-!
# Two-head chord in the countable model

`replaceTwo` replaces two head masses leaving all others fixed, changing total
mass and the square moment only at those slots, and the exact finite two-head
chord identity persists for the countable objective with every exterior head and
dust interaction.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Replace two head masses, leaving every other independent mass fixed. -/
def replaceTwo (p : ℕ → ℝ) (i j : ℕ) (u v : ℝ) : ℕ → ℝ :=
  Function.update (Function.update p i u) j v

theorem replaceTwo_replaceTwo (p : ℕ → ℝ) (i j : ℕ) (a b u v : ℝ) :
    replaceTwo (replaceTwo p i j a b) i j u v = replaceTwo p i j u v := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [replaceTwo]
  · by_cases hki : k = i
    · subst k
      simp [replaceTwo, hkj]
    · simp [replaceTwo, Function.update_of_ne, hkj, hki]

theorem replaceTwo_self (p : ℕ → ℝ) (i j : ℕ) :
    replaceTwo p i j (p i) (p j) = p := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [replaceTwo]
  · by_cases hki : k = i
    · subst k
      simp [replaceTwo, hkj]
    · simp [replaceTwo, Function.update_of_ne, hkj]

theorem replaceTwo_nonneg (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (i j : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∀ k, 0 ≤ replaceTwo p i j u v k := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa [replaceTwo] using hv
  · by_cases hki : k = i
    · subst k
      simpa [replaceTwo, Function.update_of_ne, hkj] using hu
    · simpa [replaceTwo, Function.update_of_ne, hkj, hki] using hp k

/-- Replacing finitely many masses changes total mass by their exact difference. -/
theorem replaceTwo_tsum (p : ℕ → ℝ) (hsum : Summable p) (i j : ℕ) (hij : i ≠ j)
    (u v : ℝ) :
    (∑' k, replaceTwo p i j u v k) = (∑' k, p k) - p i - p j + u + v := by
  have h := ((hsum.hasSum.update i u).update j v).tsum_eq
  simp only [Function.update_of_ne (Ne.symm hij)] at h
  change (∑' k, replaceTwo p i j u v k) = _ at h
  rw [h]
  ring

/-- The square moment changes only at the two replaced head slots. -/
theorem replaceTwo_square_tsum (p : ℕ → ℝ) (hsum : Summable (fun k => (p k) ^ 2))
    (i j : ℕ) (hij : i ≠ j) (u v : ℝ) :
    (∑' k, (replaceTwo p i j u v k) ^ 2) =
      (∑' k, (p k) ^ 2) - (p i) ^ 2 - (p j) ^ 2 + u ^ 2 + v ^ 2 := by
  have heq : (fun k => (replaceTwo p i j u v k) ^ 2) =
      replaceTwo (fun k => (p k) ^ 2) i j (u ^ 2) (v ^ 2) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [replaceTwo]
    · by_cases hki : k = i
      · subst k
        simp [replaceTwo, hij]
      · simp [replaceTwo, Function.update_of_ne, hkj, hki]
  rw [heq, replaceTwo_tsum _ hsum i j hij]

/-- The exact finite two-head chord identity persists for the actual
countable objective, with every exterior head and old dust interaction. -/
theorem two_head_chord {D : Coefficients} (hD : D ∈ feasible)
    (i j : ℕ) (hij : i ≠ j) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (hpi : p i = 0) (hpj : p j = 0)
    (x r s : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) (hrx : r ≤ x) :
    (x - r) * objective (replaceTwo p i j x 0) s D +
      r * objective (replaceTwo p i j 0 x) s D -
      x * objective (replaceTwo p i j (x - r) r) s D =
        -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) *
          x * r * (x - r) := by
  have ht (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :=
    objective_restrict_tendsto (replaceTwo p i j u v)
      (replaceTwo_nonneg p hp i j u v hu hv) ((hsum.update i u).update j v) s hD.1
  have hlim := (((ht x 0 hx le_rfl).const_mul (x - r)).add
    ((ht 0 x le_rfl hx).const_mul r)).sub
      ((ht (x - r) r (sub_nonneg.mpr hrx) hr).const_mul x)
  apply tendsto_nhds_unique hlim
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop (max i j)] with n hn
  have hi : i < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
  have hj : j < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
  have hij' : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)
  have hup (u v : ℝ) : (fun k : Fin n => replaceTwo p i j u v k.val) =
      Function.update (Function.update (fun k : Fin n => p k.val) ⟨i, hi⟩ u) ⟨j, hj⟩ v := by
    funext k
    by_cases hkj : k.val = j
    · have hkj' : k = ⟨j, hj⟩ := Fin.ext hkj
      subst k
      simp [replaceTwo]
    · have hkj' : k ≠ ⟨j, hj⟩ := fun h => hkj (congrArg Fin.val h)
      by_cases hki : k.val = i
      · have hki' : k = ⟨i, hi⟩ := Fin.ext hki
        subst k
        simp [replaceTwo, hij, hij']
      · have hki' : k ≠ ⟨i, hi⟩ := fun h => hki (congrArg Fin.val h)
        simp [replaceTwo, Function.update_of_ne, hkj, hki, hkj', hki']
  simp only [hup]
  have hk : (DustCellRestriction.headDual (restrict n D)).beta ⟨i, hi⟩ ⟨j, hj⟩ =
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) :=
    (MultipartiteCountableMeasure.kernel_embed D n
      (.inl (some ⟨i, hi⟩)) (.inl (some ⟨j, hj⟩))).symm
  rw [← hk]
  exact (MultipartiteDust.two_head_chord (restrict n D) ⟨i, hi⟩ ⟨j, hj⟩ hij'
    (fun k : Fin n => p k.val) hpi hpj x r s).symm

end Erdos1017.MultipartiteCountableDual
