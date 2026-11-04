module

public import Erdos1017.Multipartite.MultipartiteDust
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Countable bounded homogeneous duals

Coordinates are countably many independent heads with one common dust type; the
objective is absolutely convergent on summable nonnegative head masses, counting
each unordered head pair once, the feasible set is compact, and a countable
feasible dual attains the maximum `value`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators
open Set

/-- Countably many independent heads, with one common dust type. -/
abbrev Coordinate := ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ ⊕ Bool))
abbrev Coefficients := Coordinate → ℝ

def head (D : Coefficients) (i : ℕ) : ℝ := D (.inl i)
def pair (D : Coefficients) (i j : ℕ) : ℝ := D (.inr (.inl (i, j)))
def incident (D : Coefficients) (i : ℕ) : ℝ := D (.inr (.inr (.inl i)))
def linear (D : Coefficients) : ℝ := D (.inr (.inr (.inr false)))
def penalty (D : Coefficients) : ℝ := D (.inr (.inr (.inr true)))

/-- Restriction retains the original dust coefficients. -/
def restrict (n : ℕ) (D : Coefficients) : MultipartiteDust.Coefficients n
  | .inl i => head D i
  | .inr (.inl (i, j)) => pair D i j
  | .inr (.inr (.inl i)) => incident D i
  | .inr (.inr (.inr b)) => D (.inr (.inr (.inr b)))

theorem restrict_continuous (n : ℕ) : Continuous (restrict n) := by
  apply continuous_pi
  intro c
  rcases c with i | (⟨i, j⟩ | (i | b)) <;>
    exact continuous_apply _

/-- All prefix constraints include every finitely supported head selection. -/
def feasible : Set Coefficients :=
  Icc 0 1 ∩ {D | ∀ n X k, MultipartiteDust.charge (restrict n D) X k ≤ 1}

theorem feasible_isCompact : IsCompact feasible := by
  apply isCompact_Icc.inter_right
  simp only [ofPred_forall]
  exact isClosed_iInter fun n => isClosed_iInter fun X => isClosed_iInter fun k =>
    isClosed_le ((MultipartiteDust.charge_continuous X k).comp (restrict_continuous n))
      continuous_const

theorem zero_mem_feasible : (0 : Coefficients) ∈ feasible := by
  constructor
  · exact ⟨le_rfl, fun _ => zero_le_one⟩
  · intro n X k
    have heq : restrict n 0 = 0 := by
      funext c
      rcases c with i | (⟨i, j⟩ | (i | b)) <;> rfl
    rw [heq]
    exact (MultipartiteDust.zero_mem_feasible n).2 X k

theorem restrict_mem_feasible {D : Coefficients} (hD : D ∈ feasible) (n : ℕ) :
    restrict n D ∈ MultipartiteDust.feasible n := by
  refine ⟨⟨?_, ?_⟩, hD.2 n⟩
  · intro c
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> exact hD.1.1 _
  · intro c
    rcases c with i | (⟨i, j⟩ | (i | b)) <;> exact hD.1.2 _

/-- Absolutely convergent objective on summable nonnegative head masses.
The pair series counts each unordered head pair exactly once. -/
def objective (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) : ℝ :=
  (∑' i, head D i * p i) + linear D * s -
    (∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) -
    (∑' i, incident D i * p i * s) - penalty D * s ^ 2 / 2

/-- Summability gives uniform domination over the whole coefficient box. -/
theorem objective_continuousOn (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) : ContinuousOn (objective p s) (Icc 0 1) := by
  have hhead : ContinuousOn (fun D : Coefficients => ∑' i, head D i * p i) (Icc 0 1) := by
    apply continuousOn_tsum (fun i => (by unfold head; fun_prop)) hsum
    intro i D hD
    rw [Real.norm_eq_abs]
    change |D _ * p i| ≤ p i
    rw [abs_of_nonneg (mul_nonneg (hD.1 _) (hp i))]
    exact mul_le_of_le_one_left (hp i) (hD.2 _)
  have hpair : ContinuousOn (fun D : Coefficients =>
      ∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0)
      (Icc 0 1) := by
    refine continuousOn_tsum (fun z => ?_) (hsum.mul_of_nonneg hsum hp hp) ?_
    · by_cases hz : z.1 < z.2
      · simp only [hz, ↓reduceIte, pair]
        fun_prop
      · simp only [hz, ↓reduceIte]
        exact continuousOn_const
    · intro z D hD
      split_ifs
      · rw [Real.norm_eq_abs]
        unfold pair
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hD.1 _) (hp _)) (hp _))]
        calc
          pair D z.1 z.2 * p z.1 * p z.2 ≤ 1 * p z.1 * p z.2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD.2 _) (hp _)) (hp _)
          _ = p z.1 * p z.2 := by ring
      · simp only [norm_zero]
        exact mul_nonneg (hp _) (hp _)
  have hincident : ContinuousOn (fun D : Coefficients => ∑' i, incident D i * p i)
      (Icc 0 1) := by
    apply continuousOn_tsum (fun i => (by unfold incident; fun_prop)) hsum
    intro i D hD
    rw [Real.norm_eq_abs]
    change |D _ * p i| ≤ p i
    rw [abs_of_nonneg (mul_nonneg (hD.1 _) (hp i))]
    exact mul_le_of_le_one_left (hp i) (hD.2 _)
  have heq : objective p s = fun D => (∑' i, head D i * p i) + linear D * s -
      (∑' z : ℕ × ℕ, if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0) -
      (∑' i, incident D i * p i) * s - penalty D * s ^ 2 / 2 := by
    funext D
    simp only [objective, tsum_mul_right]
  rw [heq]
  exact ((hhead.add (by unfold linear; fun_prop)).sub hpair).sub
    (hincident.mul continuousOn_const) |>.sub (by unfold penalty; fun_prop)

/-- A genuine countable feasible dual attains the series objective maximum.
Its identification with the limit of finite merged-dust values is not part of
this theorem. -/
theorem exists_optimal (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) :
    ∃ D ∈ feasible, ∀ E ∈ feasible, objective p s E ≤ objective p s D := by
  exact feasible_isCompact.exists_isMaxOn ⟨0, zero_mem_feasible⟩
    ((objective_continuousOn p hp hsum s).mono Set.inter_subset_left)

/-- The countable bounded-coefficient maximum, prior to its physical identification. -/
def value (p : ℕ → ℝ) (s : ℝ) : ℝ := sSup (objective p s '' feasible)

theorem exists_value_eq (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) :
    ∃ D ∈ feasible, value p s = objective p s D := by
  obtain ⟨D, hD, heq, _⟩ := feasible_isCompact.exists_sSup_image_eq_and_ge
    ⟨0, zero_mem_feasible⟩ ((objective_continuousOn p hp hsum s).mono Set.inter_subset_left)
  exact ⟨D, hD, heq⟩

end Erdos1017.MultipartiteCountableDual
