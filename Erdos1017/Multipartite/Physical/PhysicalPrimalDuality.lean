module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Weak duality for unrestricted physical laws

Physical feasibility for laws of every finite order, allowing singular joint
measures, asks for clique support and exact pair balance; exact balance forces
summable mass, and weak duality holds under the laws themselves, under pairwise
tests and under pointwise clique tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Ordered distinct coordinate pairs in an arbitrary finite clique. -/
abbrev PairIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≠ ij.2}

/-- Actual ordered pair occupation of one arbitrary tuple law. -/
def orderOccupation (n : ℕ) (μ : Measure (Fin n → V)) : Measure (V × V) :=
  ∑ ij : PairIndex n, μ.map (fun v => (v ij.val.1, v ij.val.2))

/-- Unrestricted laws at every finite order. No absolute continuity or
independent-sampling condition is imposed. -/
abbrev Laws (V : Type*) [MeasurableSpace V] := ∀ n : ℕ, Measure (Fin n → V)

/-- Full ordered pair occupation, retaining both orientations. -/
def occupation (μ : Laws V) : Measure (V × V) :=
  Measure.sum (fun n => orderOccupation n (μ n))

/-- Total parent mass, for families whose real masses are summable. -/
def cost (μ : Laws V) : ℝ := ∑' n, (μ n).real Set.univ

/-- Charge counts each unordered pair once, even when the kernel is signed. -/
def charge (Y : V × V → ℝ) {n : ℕ} (v : Fin n → V) : ℝ :=
  (∑ ij : PairIndex n, Y (v ij.val.1, v ij.val.2)) / 2

/-- The physical constraints refer to actual clique support and exact pair
measure balance. In particular they permit singular joint measures. -/
def Feasible (A : V → V → Prop) (demand : Measure (V × V)) (μ : Laws V) : Prop :=
  μ 0 = 0 ∧ μ 1 = 0 ∧
    (∀ n, ∀ᵐ v ∂μ n, ∀ i j, i ≠ j → A (v i) (v j)) ∧
    occupation μ = demand

private theorem pair_measurable {n : ℕ} (ij : PairIndex n) :
    Measurable (fun v : Fin n → V => (v ij.val.1, v ij.val.2)) :=
  (measurable_pi_apply _).prodMk (measurable_pi_apply _)

/-- Every ordered coordinate marginal is dominated by its full occupation. -/
theorem pair_le_orderOccupation (n : ℕ) (μ : Measure (Fin n → V)) (ij : PairIndex n) :
    μ.map (fun v => (v ij.val.1, v ij.val.2)) ≤ orderOccupation n μ := by
  classical
  unfold orderOccupation
  exact Finset.single_le_sum
    (f := fun kl : PairIndex n => μ.map (fun v : Fin n → V => (v kl.val.1, v kl.val.2)))
    (fun _ _ => by intro s; exact bot_le) (Finset.mem_univ ij)

/-- One demand-null exception can be removed simultaneously at every pair
inside each arbitrary parent law. This does not remove tuple-null exceptions. -/
theorem ae_all_pairs_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (P : V × V → Prop)
    (hP : ∀ᵐ z ∂demand, P z) (n : ℕ) :
    ∀ᵐ v ∂μ n, ∀ i j, i ≠ j → P (v i, v j) := by
  have htotal : ∀ᵐ z ∂occupation μ, P z := hbalance.symm ▸ hP
  have horder : orderOccupation n (μ n) ≤ occupation μ :=
    Measure.le_sum (fun n => orderOccupation n (μ n)) n
  have hpair (ij : PairIndex n) : ∀ᵐ v ∂μ n, P (v ij.val.1, v ij.val.2) := by
    apply ae_of_ae_map (pair_measurable ij).aemeasurable
    exact (ae_mono ((pair_le_orderOccupation n (μ n) ij).trans horder)) htotal
  simp only [ae_all_iff]
  intro i j hij
  exact hpair ⟨(i, j), hij⟩

/-- Pair occupation gives the integral of the actual finite tuple charge. -/
theorem integral_charge (n : ℕ) (μ : Measure (Fin n → V)) (Y : V × V → ℝ)
    (hY : Integrable Y (orderOccupation n μ)) :
    Integrable (charge Y) μ ∧
      (∫ v, charge Y v ∂μ) = (∫ z, Y z ∂orderOccupation n μ) / 2 := by
  classical
  have hi (ij : PairIndex n) :
      Integrable Y (μ.map (fun v => (v ij.val.1, v ij.val.2))) := by
    exact hY.mono_measure (pair_le_orderOccupation n μ ij)
  have hc (ij : PairIndex n) :
      Integrable (fun v => Y (v ij.val.1, v ij.val.2)) μ :=
    (integrable_map_measure (hi ij).aestronglyMeasurable
      (pair_measurable ij).aemeasurable).mp (hi ij)
  refine ⟨(integrable_finsetSum _ (fun ij _ => hc ij)).div_const 2, ?_⟩
  simp only [charge, integral_div]
  rw [integral_finsetSum _ (fun ij _ => hc ij)]
  congr 1
  rw [orderOccupation, integral_finsetSum_measure (fun ij _ => hi ij)]
  apply Finset.sum_congr rfl
  intro ij _
  exact (integral_map (pair_measurable ij).aemeasurable (hi ij).aestronglyMeasurable).symm

/-- Exact finite pair demand forces summable parent mass once orders zero
and one are excluded. Thus finite cost is not a restriction on balanced laws. -/
theorem summable_mass_of_balance (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (demand : Measure (V × V)) [IsFiniteMeasure demand]
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = demand) :
    Summable (fun n => (μ n).real Set.univ) := by
  have htotal : Integrable (fun _ : V × V => (1 : ℝ))
      (Measure.sum (fun n => orderOccupation n (μ n))) := by
    change Integrable _ (occupation μ)
    rw [hbalance]
    exact integrable_const 1
  have hs : Summable (fun n => (orderOccupation n (μ n)).real Set.univ) := by
    simpa using htotal.summable_integral
  apply Summable.of_nonneg_of_le (fun n => ENNReal.toReal_nonneg) _ hs
  intro n
  cases n with
  | zero => simp [hzero]
  | succ n =>
    cases n with
    | zero => simp [hone]
    | succ n =>
      let ij : PairIndex (n + 1 + 1) := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
        intro h
        have := congrArg Fin.val h
        simp at this⟩
      have hle := pair_le_orderOccupation (n + 1 + 1) (μ (n + 1 + 1)) ij Set.univ
      have hmass : μ (n + 1 + 1) Set.univ ≤
          orderOccupation (n + 1 + 1) (μ (n + 1 + 1)) Set.univ := by
        simpa [Measure.map_apply (pair_measurable ij) MeasurableSet.univ] using hle
      have hfinite : orderOccupation (n + 1 + 1) (μ (n + 1 + 1)) Set.univ ≠ ∞ := by
        apply ne_of_lt
        apply lt_of_le_of_lt (Measure.le_sum (fun n => orderOccupation n (μ n)) _ Set.univ)
        change occupation μ Set.univ < ∞
        rw [hbalance]
        exact measure_lt_top _ _
      exact ENNReal.toReal_mono hfinite hmass

/-- Weak duality for arbitrary all-orders laws. Feasibility must hold under
these laws themselves; product-almost-everywhere tests are not substituted. -/
theorem weak_duality (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (Y : V × V → ℝ) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (hY : Integrable Y demand)
    (hcost : Summable (fun n => (μ n).real Set.univ))
    (hfeasible : ∀ n, ∀ᵐ v ∂μ n, charge Y v ≤ 1) :
    (∫ z, Y z ∂demand) / 2 ≤ cost μ := by
  have htotal : Integrable Y (Measure.sum (fun n => orderOccupation n (μ n))) := by
    change Integrable Y (occupation μ)
    rw [hbalance]
    exact hY
  have hi (n : ℕ) : Integrable Y (orderOccupation n (μ n)) :=
    htotal.mono_measure (Measure.le_sum (fun n => orderOccupation n (μ n)) n)
  have heq (n : ℕ) := integral_charge n (μ n) Y (hi n)
  have hs : Summable (fun n => (∫ z, Y z ∂orderOccupation n (μ n)) / 2) :=
    (hasSum_integral_measure htotal).summable.div_const 2
  have hle (n : ℕ) : (∫ z, Y z ∂orderOccupation n (μ n)) / 2 ≤
      (μ n).real Set.univ := by
    rw [← (heq n).2]
    simpa using integral_mono_ae (heq n).1 (integrable_const (1 : ℝ)) (hfeasible n)
  calc
    (∫ z, Y z ∂demand) / 2 =
        ∑' n, (∫ z, Y z ∂orderOccupation n (μ n)) / 2 := by
      rw [← hbalance, occupation, integral_sum_measure htotal, tsum_div_const]
    _ ≤ cost μ := hs.tsum_le_tsum hle hcost

/-- A common pair-null exception is harmless for every balanced parent law.
The remaining clique test is pointwise outside those pair exceptions. -/
theorem weak_duality_of_pairwise_tests (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (A : V → V → Prop) (Y : V × V → ℝ) (demand : Measure (V × V))
    [IsFiniteMeasure demand] (hμ : Feasible A demand μ) (hY : Integrable Y demand)
    (P : V × V → Prop) (hP : ∀ᵐ z ∂demand, P z)
    (htest : ∀ n (v : Fin n → V),
      (∀ i j, i ≠ j → A (v i) (v j)) →
      (∀ i j, i ≠ j → P (v i, v j)) → charge Y v ≤ 1) :
    (∫ z, Y z ∂demand) / 2 ≤ cost μ := by
  apply weak_duality μ Y demand hμ.2.2.2 hY
    (summable_mass_of_balance μ demand hμ.1 hμ.2.1 hμ.2.2.2)
  intro n
  filter_upwards [hμ.2.2.1 n, ae_all_pairs_of_balance μ demand hμ.2.2.2 P hP n] with v hv hPv
  exact htest n v hv hPv

/-- A pointwise clique test applies to every supported law, including singular
laws, and therefore gives genuine physical weak duality. -/
theorem weak_duality_of_clique_tests (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (A : V → V → Prop) (Y : V × V → ℝ) (demand : Measure (V × V))
    [IsFiniteMeasure demand] (hμ : Feasible A demand μ) (hY : Integrable Y demand)
    (htest : ∀ n (v : Fin n → V),
      (∀ i j, i ≠ j → A (v i) (v j)) → charge Y v ≤ 1) :
    (∫ z, Y z ∂demand) / 2 ≤ cost μ := by
  exact weak_duality_of_pairwise_tests μ A Y demand hμ hY (fun _ => True)
    (Filter.Eventually.of_forall fun _ => trivial) (fun n v hv _ => htest n v hv)

end Erdos1017.PhysicalPrimal
