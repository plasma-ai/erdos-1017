module

public import Erdos1017.Multipartite.Multipartite
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.Module.BigOperators

/-!
# Lifting finite clique selections to physical laws

Finite clique selections are lifted by independent sampling in each part, with
same-cell edge repairs; the lifted laws have occupation equal to the
block-product demand and cost equal to the finite cost plus half the completed
square mass, giving a feasible physical family on atomless cells
(`feasible_lift`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalCellLift

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- A finite clique selection is lifted by independent sampling in each part.
Coordinates outside the selection are auxiliary and contribute no vertices. -/
def law (μ : ι → Measure Ω) (w : Multipartite.Selection ι → ℝ)
    (X : Multipartite.Selection ι) : Measure (ι → Ω) :=
  ENNReal.ofReal (w X) • Measure.pi μ

/-- Empty and singleton selections receive no physical clique mass. -/
theorem law_trivial (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (hw : Multipartite.PrimalFeasible a w)
    (X : Multipartite.Selection ι) (hX : ¬Multipartite.Nontrivial X) : law μ w X = 0 := by
  simp [law, hw.2.1 X hX]

/-- The ordered pair occupation of two distinct selected parts. -/
def pairLoad (μ : ι → Measure Ω) (w : Multipartite.Selection ι → ℝ)
    (i j : ι) : Measure (Ω × Ω) :=
  ∑ X, if X i = true ∧ X j = true then
    (law μ w X).map (fun x => (x i, x j)) else 0

omit [DecidableEq ι] in
/-- Independent physical samples have the prescribed product pair law. -/
theorem pair_map (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (i j : ι) (hij : i ≠ j) :
    (Measure.pi μ).map (fun x => (x i, x j)) = (μ i).prod (μ j) := by
  have hind := iIndepFun_pi (μ := μ) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)
  have h := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [id_eq, (measurePreserving_eval μ i).map_eq,
    (measurePreserving_eval μ j).map_eq] using h

/-- Lifting a finite fractional partition preserves each entire pair measure,
not merely the total mass of its edges. -/
theorem pairLoad_eq (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ)
    (hw : Multipartite.PrimalFeasible a w) (i j : ι) (hij : i ≠ j) :
    pairLoad μ w i j = ENNReal.ofReal (a i * a j) • (μ i).prod (μ j) := by
  have ht (X : Multipartite.Selection ι) :
      (if X i = true ∧ X j = true then
        (law μ w X).map (fun x => (x i, x j)) else 0) =
      ENNReal.ofReal (w X * (Selector.bit (X i) * Selector.bit (X j))) •
        (μ i).prod (μ j) := by
    rw [law, Measure.map_smul _ ((measurable_pi_apply i).prodMk
      (measurable_pi_apply j)).aemeasurable, pair_map μ i j hij]
    cases X i <;> cases X j <;> simp [Selector.bit]
  unfold pairLoad
  simp_rw [ht]
  rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [hw.2.2 i j hij]
  · intro X _
    exact mul_nonneg (hw.1 X) (mul_nonneg (by cases X i <;> norm_num [Selector.bit])
      (by cases X j <;> norm_num [Selector.bit]))

/-- Total physical clique mass equals the cost of the finite partition. -/
theorem law_cost (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (w : Multipartite.Selection ι → ℝ) (hw : ∀ X, 0 ≤ w X) :
    (∑ X, (law μ w X) Set.univ).toReal = Multipartite.cost w := by
  simp only [law, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun X _ => hw X), ENNReal.toReal_ofReal]
  · rfl
  · exact Finset.sum_nonneg (fun X _ => hw X)

/-- Missing pairs inside completed cells are repaired by genuine two-point laws.
The one-half is the cost per unordered pair, with both orientations sampled. -/
def repair (μ : ι → Measure Ω) (a : ι → ℝ) (i : ι) : Measure (Ω × Ω) :=
  ENNReal.ofReal (a i ^ 2 / 2) • (μ i).prod (μ i)

omit [Fintype ι] [DecidableEq ι] in
/-- The exact same-cell repair cost is half the completed square mass. -/
theorem repair_cost (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (S : Finset ι) :
    (∑ i ∈ S, repair μ a i Set.univ).toReal = (∑ i ∈ S, a i ^ 2) / 2 := by
  simp only [repair, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ENNReal.toReal_ofReal]
  · exact Finset.sum_div S (fun i => a i ^ 2) 2 |>.symm
  · exact Finset.sum_nonneg (fun i _ => by positivity)

/-- Completing a cell makes its internal pairs edges. Distinct cell labels
always form edges; the physical diagonal is never an edge. -/
def Adj (S : Finset ι) (x y : ι × Ω) : Prop :=
  x ≠ y ∧ (x.1 ≠ y.1 ∨ x.1 ∈ S)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] in
/-- Each selected vector is an actual clique in the tagged physical space. -/
theorem selected_clique (S : Finset ι) (X : Multipartite.Selection ι) (x : ι → Ω)
    (i j : ι) (hij : i ≠ j) (_hi : X i = true) (_hj : X j = true) :
    Adj S (i, x i) (j, x j) := by
  exact ⟨fun h => hij (congrArg Prod.fst h), Or.inl hij⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Atomless cell sampling puts no mass on repeated physical points. -/
theorem product_diagonal_null [MeasurableEq Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (μ.prod μ) (Set.diagonal Ω) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have hpre (x : Ω) : Prod.mk x ⁻¹' Set.diagonal Ω = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp_rw [hpre, measure_singleton]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- A same-cell repair consists almost everywhere of genuine physical edges. -/
theorem repair_edges [MeasurableEq Ω] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (a : ι → ℝ) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    ∀ᵐ z ∂repair μ a i, Adj S (i, z.1) (i, z.2) := by
  have hnull : repair μ a i (Set.diagonal Ω) = 0 := by
    simp [repair, Measure.smul_apply, product_diagonal_null]
  have hne : ∀ᵐ z ∂repair μ a i, z.1 ≠ z.2 := by
    rw [ae_iff]
    simpa only [not_not, Set.diagonal] using hnull
  filter_upwards [hne] with z hz
  exact ⟨fun h => hz (congrArg Prod.snd h), Or.inr hi⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Repair laws are symmetric under reversing their two physical vertices. -/
theorem repair_swap (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (i : ι) : (repair μ a i).map Prod.swap = repair μ a i := by
  rw [repair, Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap]

omit [Fintype ι] [DecidableEq ι] in
/-- Both ordered orientations of a repair have the full internal product demand. -/
theorem repair_pairLoad (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (i : ι) :
    repair μ a i + (repair μ a i).map Prod.swap =
      ENNReal.ofReal (a i ^ 2) • (μ i).prod (μ i) := by
  rw [repair_swap, repair, ← add_smul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 2
  ring

/-- Exact ordered pair occupation after completing a specified collection of cells. -/
def completedPairLoad (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) (i j : ι) : Measure (Ω × Ω) :=
  if i = j then
    if i ∈ S then repair μ a i + (repair μ a i).map Prod.swap else 0
  else pairLoad μ w i j

/-- Every labeled pair has its exact product measure after the explicit repair. -/
theorem completedPairLoad_eq (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ)
    (hw : Multipartite.PrimalFeasible a w) (S : Finset ι) (i j : ι) :
    completedPairLoad μ a w S i j =
      if i ≠ j ∨ i ∈ S then ENNReal.ofReal (a i * a j) • (μ i).prod (μ j) else 0 := by
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;> simp [completedPairLoad, hi, repair_pairLoad, pow_two]
  · simp [completedPairLoad, hij, pairLoad_eq μ a w hw i j hij]

/-- Cost of the lifted finite clique laws and their same-cell edge repairs. -/
def cost (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ X, law μ w X Set.univ).toReal + (∑ i ∈ S, repair μ a i Set.univ).toReal

/-- The construction pays precisely the finite cost plus half the completed square mass. -/
theorem cost_eq (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ) (hw : ∀ X, 0 ≤ w X) (S : Finset ι) :
    cost μ a w S = Multipartite.cost w + (∑ i ∈ S, a i ^ 2) / 2 := by
  rw [cost, law_cost μ w hw, repair_cost]

/-- Embed a pair from its labeled cells into the common physical space. -/
def tagPair (i j : ι) (z : Ω × Ω) : (ι × Ω) × (ι × Ω) := ((i, z.1), (j, z.2))

variable [MeasurableSpace ι]

/-- The constructed laws' total ordered edge occupation on the tagged space. -/
def occupation (μ : ι → Measure Ω) (a : ι → ℝ)
    (w : Multipartite.Selection ι → ℝ) (S : Finset ι) : Measure ((ι × Ω) × (ι × Ω)) :=
  ∑ i, ∑ j, (completedPairLoad μ a w S i j).map (tagPair i j)

/-- The exact block-product demand of the completed multipartite physical profile.
Each off-diagonal block is counted in both ordered orientations. -/
def demand (μ : ι → Measure Ω) (a : ι → ℝ)
    (S : Finset ι) : Measure ((ι × Ω) × (ι × Ω)) :=
  ∑ i, ∑ j, if i ≠ j ∨ i ∈ S then
    ENNReal.ofReal (a i * a j) • ((μ i).prod (μ j)).map (tagPair i j) else 0

/-- The lifted clique laws and repair laws satisfy an equality of full physical
edge measures, including every measurable event in the common tagged space. -/
theorem occupation_eq_demand (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ)
    (hw : Multipartite.PrimalFeasible a w) (S : Finset ι) :
    occupation μ a w S = demand μ a S := by
  unfold occupation demand
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [completedPairLoad_eq μ a w hw S i j]
  split_ifs
  · exact Measure.map_smul _ (((measurable_const.prodMk measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)).aemeasurable)
  · exact Measure.map_zero _

/-- Feasibility of the concrete sampled family: all nonzero laws describe
nontrivial cliques or repair edges, and their full ordered edge demand is exact. -/
def Feasible (μ : ι → Measure Ω) (a : ι → ℝ) (S : Finset ι)
    (w : Multipartite.Selection ι → ℝ) : Prop :=
  (∀ X, ¬Multipartite.Nontrivial X → law μ w X = 0) ∧
    (∀ X, ∀ᵐ x ∂law μ w X, ∀ i j, i ≠ j → X i = true → X j = true →
      Adj S (i, x i) (j, x j)) ∧
    (∀ i ∈ S, ∀ᵐ z ∂repair μ a i, Adj S (i, z.1) (i, z.2)) ∧
    occupation μ a w S = demand μ a S

/-- Finite exact moments construct a feasible physical family on atomless cells.
No physical feasibility or value identity occurs among the hypotheses. -/
theorem feasible_lift [MeasurableEq Ω] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (a : ι → ℝ) (w : Multipartite.Selection ι → ℝ)
    (hw : Multipartite.PrimalFeasible a w) (S : Finset ι) : Feasible μ a S w := by
  refine ⟨law_trivial μ a w hw, ?_, ?_, occupation_eq_demand μ a w hw S⟩
  · intro X
    exact Filter.Eventually.of_forall (fun x i j hij hi hj => selected_clique S X x i j hij hi hj)
  · intro i hi
    exact repair_edges μ a S i hi

end Erdos1017.PhysicalCellLift
