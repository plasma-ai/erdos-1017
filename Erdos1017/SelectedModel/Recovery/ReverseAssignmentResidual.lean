module

public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCompactness
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Total and residual of a reverse assignment

The pointwise total of the assignment coordinates and a bounded measurable
residual equal to the remaining supply almost everywhere for every feasible
assignment, with measurability, integrability, and infinitely many eligible
labels where the residual is positive on the zero-diffuse region.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1017.ReverseAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The literal pointwise total of the actual assignment coordinates. -/
def total (q : ℕ → Lp ℝ 2 μ) (x : Ω) : ℝ := ∑' i, q i x

/-- A globally bounded measurable residual, equal to the literal remaining
supply almost everywhere for every feasible assignment. -/
def residual (q : ℕ → Lp ℝ 2 μ) (x : Ω) : ℝ := max 0 (min 1 (1 - total q x))

theorem measurable_total (q : ℕ → Lp ℝ 2 μ) : Measurable (total q) :=
  Measurable.tsum (fun i => (Lp.stronglyMeasurable (q i)).measurable)

theorem residual_mem (q : ℕ → Lp ℝ 2 μ) (x : Ω) : residual q x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem measurable_residual (q : ℕ → Lp ℝ 2 μ) : Measurable (residual q) :=
  measurable_const.max (measurable_const.min (measurable_const.sub (measurable_total q)))

theorem stronglyMeasurable_residual (q : ℕ → Lp ℝ 2 μ) : StronglyMeasurable (residual q) :=
  (measurable_residual q).stronglyMeasurable

/-- All finite supply constraints give actual pointwise summability and
the total-supply bound on one common conull set. -/
theorem Feasible.ae_summable_and_total_le_one {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) :
    ∀ᵐ x ∂μ, Summable (fun i => q i x) ∧ total q x ∈ Icc (0 : ℝ) 1 := by
  have hn : ∀ᵐ x ∂μ, ∀ i, 0 ≤ q i x :=
    ae_all_iff.mpr (fun i => (hq.box i).mono fun _ hx => hx.1)
  have hp : ∀ᵐ x ∂μ, ∀ J : Finset ℕ, ∑ i ∈ J, q i x ≤ 1 :=
    ae_all_iff.mpr hq.partial_sum
  filter_upwards [hn, hp] with x hn hp
  have hsum : Summable (fun i => q i x) := summable_of_sum_le hn hp
  exact ⟨hsum, tsum_nonneg hn, hsum.tsum_le_of_sum_le hp⟩

theorem Feasible.ae_hasSum_total {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) :
    ∀ᵐ x ∂μ, HasSum (fun i => q i x) (total q x) :=
  hq.ae_summable_and_total_le_one.mono (fun _ hx => hx.1.hasSum)

/-- The bounded residual represents exactly the remaining actual supply. -/
theorem Feasible.residual_eq {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) :
    residual q =ᵐ[μ] (fun x => 1 - total q x) := by
  filter_upwards [hq.ae_summable_and_total_le_one] with x hx
  unfold residual
  rw [min_eq_right (by linarith [hx.2.1]), max_eq_right (by linarith [hx.2.2])]

/-- Positive residual on the zero-diffuse region has infinitely many
actual eligible labels, derived from all finite patterns including the empty one. -/
theorem Feasible.residual_infinite_allowed {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) :
    ∀ᵐ x ∂μ, δ x = 0 → 0 < residual q x → {i | x ∈ allowed i}.Infinite := by
  classical
  have hs : ∀ᵐ x ∂μ, ∀ i, x ∉ allowed i → q i x = 0 := ae_all_iff.mpr hq.support
  have hp : ∀ᵐ x ∂μ, ∀ J : Finset ℕ,
      x ∈ finitePattern allowed δ J → ∑ i ∈ J, q i x = 1 := by
    apply ae_all_iff.mpr
    intro J
    exact (ae_restrict_iff' (measurableSet_finitePattern hallowed hδ J)).mp (hq.full_pattern J)
  filter_upwards [hs, hp, hq.residual_eq] with x hs hp hr hδx hpos
  by_contra hnot
  have hfinite : {i | x ∈ allowed i}.Finite := Set.not_infinite.mp hnot
  let J := hfinite.toFinset
  have hx : x ∈ finitePattern allowed δ J :=
    ⟨hδx, fun i => hfinite.mem_toFinset⟩
  have ht : total q x = ∑ i ∈ J, q i x := by
    apply tsum_eq_sum
    intro i hi
    apply hs i
    exact fun hia => hi (hfinite.mem_toFinset.mpr hia)
  rw [hr, ht, hp J hx, sub_self] at hpos
  exact lt_irrefl 0 hpos

variable [IsFiniteMeasure μ]

theorem Feasible.total_integrable {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) : Integrable (total q) μ := by
  apply Integrable.of_bound (measurable_total q).aestronglyMeasurable 1
  filter_upwards [hq.ae_summable_and_total_le_one] with x hx
  rw [Real.norm_of_nonneg hx.2.1]
  exact hx.2.2

theorem residual_integrable (q : ℕ → Lp ℝ 2 μ) : Integrable (residual q) μ := by
  apply Integrable.of_bound (measurable_residual q).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => by
    rw [Real.norm_of_nonneg (residual_mem q x).1]
    exact (residual_mem q x).2)

end Erdos1017.ReverseAssignment
