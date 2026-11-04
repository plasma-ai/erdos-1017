module

public import Erdos1017.Multipartite.MultipartiteDensitySelection
public import Erdos1017.Multipartite.Dust.DustObjectiveVariation

/-!
# Mass variations of the countable objective

The anchor row and head rows of a dual are defined and shown absolutely
summable; changing one or two head masses gives exact quadratic expansions, and
the raw-mass `physicalObjective` scales, normalizes and is bounded by the
selected density maximum.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The old dual's row against the anchor, before mass normalization. -/
def anchorRow (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) : ℝ :=
  (∑' i, head D i * p i) + linear D * s

/-- The exterior row of a positive independent head, in raw mass units. -/
def headRow (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) (i : ℕ) : ℝ :=
  head D i + (∑' j, MultipartiteCountableMeasure.kernel D
    (.inl (some i)) (.inl (some j)) * p j) - s * incident D i

/-- Bounded physical type charges make every exterior row absolutely summable. -/
theorem headRow_summable {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (i : ℕ) :
    Summable (fun j => MultipartiteCountableMeasure.kernel D
      (.inl (some i)) (.inl (some j)) * p j) := by
  apply hsum.of_norm_bounded
  intro j
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  apply mul_le_of_le_one_left (hp j)
  simpa only [Real.norm_eq_abs] using MultipartiteCountableMeasure.norm_kernel_le_one hD
    (.inl (some i)) (.inl (some j))

/-- The actual countable objective has its exterior row as the exact slope
of each admissible single-head mass change. -/
theorem objective_update {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : Summable p) (s : ℝ)
    (i : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    objective (Function.update p i y) s D = objective p s D + (y - p i) * headRow p s D i := by
  have hp' : ∀ j, 0 ≤ Function.update p i y j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hy
    · simpa [Function.update_of_ne, hj] using hp j
  have hleft := objective_restrict_tendsto (Function.update p i y) hp' (hsum.update i y) s hD.1
  have hrow : Filter.Tendsto (fun n => head D i +
      (∑ j ∈ Finset.range n, MultipartiteCountableMeasure.kernel D
        (.inl (some i)) (.inl (some j)) * p j) - s * incident D i)
      Filter.atTop (nhds (headRow p s D i)) :=
    (tendsto_const_nhds.add (headRow_summable hD p hp hsum i).hasSum.tendsto_sum_nat).sub_const
      (s * incident D i)
  have hright := (objective_restrict_tendsto p hp hsum s hD.1).add
    (hrow.const_mul (y - p i))
  apply tendsto_nhds_unique hleft
  apply Filter.Tendsto.congr' _ hright
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  have hup : (fun j : Fin n => Function.update p i y j.val) =
      Function.update (fun j : Fin n => p j.val) ⟨i, hn⟩ y := by
    funext j
    by_cases hj : j.val = i
    · have hji : j = ⟨i, hn⟩ := Fin.ext hj
      subst j
      simp
    · have hji : j ≠ ⟨i, hn⟩ := fun h => hj (congrArg Fin.val h)
      simp [Function.update_of_ne, hj, hji]
  have hk (j : Fin n) : (DustCellRestriction.headDual (restrict n D)).beta ⟨i, hn⟩ j =
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j.val)) :=
    (MultipartiteCountableMeasure.kernel_embed D n
      (.inl (some ⟨i, hn⟩)) (.inl (some j))).symm
  rw [hup, MultipartiteDust.objective_update]
  simp only [hk, MultipartiteDust.head, MultipartiteDust.incident, restrict]
  congr 4
  exact (Fin.sum_univ_eq_sum_range (fun j => MultipartiteCountableMeasure.kernel D
    (.inl (some i)) (.inl (some j)) * p j) n).symm

theorem headKernel_symm (D : Coefficients) (i j : ℕ) :
    MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) =
      MultipartiteCountableMeasure.kernel D (.inl (some j)) (.inl (some i)) := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [MultipartiteCountableMeasure.kernel, h, not_lt_of_gt h]
  · rfl
  · simp [MultipartiteCountableMeasure.kernel, h, not_lt_of_gt h]

/-- A finite change in head mass changes every exterior row by its literal
pair charge times the changed mass. -/
theorem headRow_update {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ) (i j : ℕ) (y : ℝ) :
    headRow (Function.update p j y) s D i = headRow p s D i +
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) * (y - p j) := by
  have heq : (fun k => MultipartiteCountableMeasure.kernel D
      (.inl (some i)) (.inl (some k)) * Function.update p j y k) =
      Function.update (fun k => MultipartiteCountableMeasure.kernel D
        (.inl (some i)) (.inl (some k)) * p k) j
        (MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) * y) := by
    funext k
    by_cases hk : k = j <;> simp [Function.update_of_ne, hk]
  have h := ((headRow_summable hD p hp hsum i).hasSum.update j
    (MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) * y)).tsum_eq
  unfold headRow
  rw [heq, h]
  ring

theorem anchorRow_update {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ) (i : ℕ) (y : ℝ) :
    anchorRow (Function.update p i y) s D = anchorRow p s D + head D i * (y - p i) := by
  have heq : (fun k => head D k * Function.update p i y k) =
      Function.update (fun k => head D k * p k) i (head D i * y) := by
    funext k
    by_cases hk : k = i <;> simp [Function.update_of_ne, hk]
  have h := ((head_summable p hp hsum hD.1).hasSum.update i (head D i * y)).tsum_eq
  unfold anchorRow
  rw [heq, h]
  ring

/-- Changing two head masses gives the exact quadratic, including their
single cross interaction and every unchanged exterior row. -/
theorem objective_two_updates {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ)
    (i j : ℕ) (hij : i ≠ j) (t r : ℝ) (ht : 0 ≤ p i + t) (hr : 0 ≤ p j + r) :
    objective (replaceTwo p i j (p i + t) (p j + r)) s D = objective p s D +
      t * headRow p s D i + r * headRow p s D j +
        MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) * t * r := by
  have hpI : ∀ k, 0 ≤ Function.update p i (p i + t) k := by
    intro k
    by_cases hk : k = i
    · subst k
      simpa using ht
    · simpa [Function.update_of_ne, hk] using hp k
  rw [replaceTwo, objective_update hD _ hpI (hsum.update i _) s j _ hr,
    headRow_update hD p hp hsum s j i, objective_update hD p hp hsum s i _ ht,
    Function.update_of_ne (Ne.symm hij), headKernel_symm D j i]
  ring

/-- The same feasible type charges evaluated with an arbitrary anchor mass. -/
def physicalObjective (a : ℝ) (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) : ℝ :=
  a * anchorRow p s D -
    (∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) -
    (∑' i, incident D i * p i * s) - penalty D * s ^ 2 / 2

theorem physicalObjective_one (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) :
    physicalObjective 1 p s D = objective p s D := by
  simp only [physicalObjective, anchorRow, objective, one_mul]

theorem physicalObjective_eq_objective (a : ℝ) (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) :
    physicalObjective a p s D = objective p s D + (a - 1) * anchorRow p s D := by
  unfold physicalObjective objective anchorRow
  ring

/-- Moving two head masses and balancing their total at the anchor gives
an exact physical variation polynomial. -/
theorem physicalObjective_two_transfers {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ)
    (i j : ℕ) (hij : i ≠ j) (t r : ℝ) (ht : 0 ≤ p i + t) (hr : 0 ≤ p j + r) :
    physicalObjective (1 - t - r) (replaceTwo p i j (p i + t) (p j + r)) s D =
      objective p s D + t * (headRow p s D i - anchorRow p s D) +
        r * (headRow p s D j - anchorRow p s D) - head D i * t ^ 2 - head D j * r ^ 2 +
        (MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) -
          head D i - head D j) * t * r := by
  have hpI : ∀ k, 0 ≤ Function.update p i (p i + t) k := by
    intro k
    by_cases hk : k = i
    · subst k
      simpa using ht
    · simpa [Function.update_of_ne, hk] using hp k
  have hrow : anchorRow (replaceTwo p i j (p i + t) (p j + r)) s D =
      anchorRow p s D + head D i * t + head D j * r := by
    rw [replaceTwo, anchorRow_update hD _ hpI (hsum.update i _) s j,
      anchorRow_update hD p hp hsum s i, Function.update_of_ne (Ne.symm hij)]
    ring
  rw [physicalObjective_eq_objective, objective_two_updates hD p hp hsum s i j hij t r ht hr,
    hrow]
  ring

/-- Simultaneous scaling of the anchor, heads, and dust scales every actual
pair charge by the square of the mass factor. -/
theorem physicalObjective_scale (a : ℝ) (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) :
    physicalObjective a (fun i => a * p i) (a * s) D = a ^ 2 * objective p s D := by
  have hh : (∑' i, head D i * (a * p i)) = a * ∑' i, head D i * p i := by
    simp_rw [show ∀ i, head D i * (a * p i) = a * (head D i * p i) from fun i => by ring]
    exact tsum_mul_left
  have hp : (∑' z : ℕ × ℕ,
      if z.1 < z.2 then pair D z.1 z.2 * (a * p z.1) * (a * p z.2) else 0) =
      a ^ 2 * ∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0 := by
    have ht (z : ℕ × ℕ) :
        (if z.1 < z.2 then pair D z.1 z.2 * (a * p z.1) * (a * p z.2) else 0) =
        a ^ 2 * (if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) := by
      split_ifs <;> ring
    simp_rw [ht]
    exact tsum_mul_left
  have hi : (∑' i, incident D i * (a * p i) * (a * s)) =
      a ^ 2 * ∑' i, incident D i * p i * s := by
    simp_rw [show ∀ i, incident D i * (a * p i) * (a * s) =
      a ^ 2 * (incident D i * p i * s) from fun i => by ring]
    exact tsum_mul_left
  rw [physicalObjective, anchorRow, hh, hp, hi, objective]
  ring

/-- Normalizing a positive anchor leaves the total normalized pair charge
unchanged. The total mass is allowed to differ from one. -/
theorem normalized_physicalObjective (a : ℝ) (ha : 0 < a) (p : ℕ → ℝ) (s : ℝ)
    (hM : 0 < a + s + ∑' i, p i) (D : Coefficients) :
    objective (fun i => p i / a) (s / a) D /
      (1 + (s / a + ∑' i, p i / a)) ^ 2 =
        physicalObjective a p s D / (a + s + ∑' i, p i) ^ 2 := by
  have hscaled := physicalObjective_scale a (fun i => p i / a) (s / a) D
  have hback : (fun i => a * (p i / a)) = p := by
    funext i
    field_simp
  rw [hback, mul_div_cancel₀ _ ha.ne'] at hscaled
  have hden : 1 + (s / a + ∑' i, p i / a) = (a + s + ∑' i, p i) / a := by
    rw [tsum_div_const]
    field_simp
    ring
  rw [hden, div_pow]
  field_simp [ha.ne', hM.ne']
  nlinarith [hscaled]

/-- The selected compact density maximum bounds actual raw-mass competitors
at the same density. Feasibility and the normalization bridge are proved. -/
theorem physicalObjective_le_density_maximum {ε : ℝ} (hε : 0 < ε)
    {x : MultipartiteProfiles.Profile}
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε ≤ MultipartiteProfiles.normalizedValue x)
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ a)
    (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s)
    (hmoment : a ^ 2 + (∑' i, (p i) ^ 2) = 2 * ε * (a + s + ∑' i, p i) ^ 2)
    {D : Coefficients} (hD : D ∈ feasible) :
    physicalObjective a p s D / (a + s + ∑' i, p i) ^ 2 ≤
      MultipartiteProfiles.normalizedValue x := by
  have hM : 0 < a + s + ∑' i, p i := by
    have hpSum : 0 ≤ ∑' i, p i := tsum_nonneg hp
    linarith
  have hp' : ∀ i, 0 ≤ p i / a := fun i => div_nonneg (hp i) ha.le
  have hp1' : ∀ i, p i / a ≤ 1 := fun i => (div_le_one ha).mpr (hp1 i)
  have hmoment' : 1 + (∑' i, (p i / a) ^ 2) =
      2 * ε * (1 + (s / a + ∑' i, p i / a)) ^ 2 := by
    simp_rw [div_pow, tsum_div_const]
    field_simp
    nlinarith [hmoment]
  rw [← normalized_physicalObjective a ha p s hM D]
  exact MultipartiteProfiles.normalized_objective_le_density_maximum hε hmax hxvalue
    (fun i => p i / a) hp' hp1' (hsum.div_const a) (s / a) (div_nonneg hs ha.le) hmoment' hD

end Erdos1017.MultipartiteCountableDual
