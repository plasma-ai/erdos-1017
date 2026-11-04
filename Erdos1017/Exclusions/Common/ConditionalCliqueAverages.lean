module

public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost
public import Erdos1017.Models.Decorated.DecoratedAbsoluteContinuity
public import Erdos1017.SelectedModel.Structure.FeatureCountSampling
public import Mathlib.Probability.ConditionalProbability

/-!
# Clique tests under independent conditional averaging

Full scalar feasibility implies every independently averaged clique test:
conditioning independently on positive measurable regions gives the averaged
clique inequality, and every natural count vector has its conditional-average
test.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.FiniteArity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Distinct coordinates of an independent heterogeneous sample have
their actual two conditional laws, even when their region labels agree. -/
theorem measurePreserving_heterogeneous_pair {n : ℕ} (σ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (σ i)] (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun v : Fin n → Ω => (v i, v j))
      (Measure.pi σ) ((σ i).prod (σ j)) := by
  have hind : iIndepFun (fun i (v : Fin n → Ω) => v i) (Measure.pi σ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval σ i).map_eq, (measurePreserving_eval σ j).map_eq]

/-- The average of the actual diagonal-free tuple charge is the
diagonal-free charge of the independent pair averages. -/
theorem integral_tupleCharge_heterogeneous {n : ℕ} (σ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (σ i)] (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B) :
    (∫ v : Fin n → Ω, tupleCharge Y v ∂Measure.pi σ) =
      pairCharge Finset.univ (fun i j => if i = j then 0
        else ∫ p, Y p.1 p.2 ∂(σ i).prod (σ j)) := by
  have hi (i j : Fin n) : Integrable
      (fun v : Fin n → Ω => if i = j then (0 : ℝ) else Y (v i) (v j)) (Measure.pi σ) := by
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact integrable_const 0
    · simp only [hij, ite_false]
      have hp := measurePreserving_heterogeneous_pair σ i j hij
      exact hp.integrable_comp_of_integrable
        (Integrable.of_bound hY.aestronglyMeasurable B
          (Eventually.of_forall (fun p => hbound p.1 p.2)))
  unfold tupleCharge pairCharge crossSum
  rw [integral_div]
  congr 1
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false]
    have hp := measurePreserving_heterogeneous_pair σ i j hij
    have hYP : Integrable (Function.uncurry Y) ((σ i).prod (σ j)) :=
      Integrable.of_bound hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound p.1 p.2))
    have he := integral_map (μ := Measure.pi σ) hp.measurable.aemeasurable
      (f := Function.uncurry Y) (by simpa only [hp.map_eq] using hYP.aestronglyMeasurable)
    rw [hp.map_eq] at he
    exact he.symm

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual full scalar feasibility implies every independently averaged
clique test. The coordinate laws and clique blocks are genuine measured
inputs; no expected-feasibility or joint conditional-law certificate occurs. -/
theorem heterogeneous_clique_average_le_one {n : ℕ} (σ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (σ i)] (hσ : ∀ i, σ i ≪ μ)
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hfull : FeasibleOrder μ A Y n)
    (hclique : ∀ i j, i ≠ j → ∀ᵐ p ∂(σ i).prod (σ j), A p.1 p.2 = true) :
    pairCharge Finset.univ (fun i j => if i = j then 0
      else ∫ p, Y p.1 p.2 ∂(σ i).prod (σ j)) ≤ 1 := by
  have hac := DecoratedKernel.pi_fin_absolutelyContinuous n σ (fun _ => μ) hσ
  have hc : ∀ᵐ v ∂Measure.pi σ, TupleClique A v := by
    simp only [TupleClique, ae_all_iff]
    intro i j hij
    exact (measurePreserving_heterogeneous_pair σ i j hij).quasiMeasurePreserving.ae
      (hclique i j hij)
  have ht : ∀ᵐ v ∂Measure.pi σ, tupleCharge Y v ≤ 1 := by
    filter_upwards [hac.ae_le hfull, hc] with v hv hvC
    exact hv hvC
  rw [← integral_tupleCharge_heterogeneous σ Y hY B hbound]
  have hint : Integrable (fun v : Fin n → Ω => tupleCharge Y v) (Measure.pi σ) := by
    unfold tupleCharge pairCharge crossSum
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact integrable_const 0
    · simp only [hij, ite_false]
      have hp := measurePreserving_heterogeneous_pair σ i j hij
      exact hp.integrable_comp_of_integrable
        (Integrable.of_bound hY.aestronglyMeasurable B
          (Eventually.of_forall (fun p => hbound p.1 p.2)))
  simpa using integral_mono_ae hint (integrable_const (1 : ℝ)) ht

/-- Conditioning independently on actual positive measurable regions
gives their averaged clique inequality. Repeated regions are permitted
precisely when their original square is a clique almost everywhere. -/
theorem conditional_clique_average_le_one {n : ℕ} (T : Fin n → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hpos : ∀ i, 0 < μ (T i))
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hfull : FeasibleOrder μ A Y n)
    (hclique : ∀ i j, i ≠ j → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T i → p.2 ∈ T j → A p.1 p.2 = true) :
    pairCharge Finset.univ (fun i j => if i = j then 0
      else ∫ p, Y p.1 p.2 ∂(cond μ (T i)).prod (cond μ (T j))) ≤ 1 := by
  let σ := fun i => cond μ (T i)
  let : ∀ i, IsProbabilityMeasure (σ i) := fun i => cond_isProbabilityMeasure (hpos i).ne'
  apply heterogeneous_clique_average_le_one σ (fun _ => cond_absolutelyContinuous)
    A Y hY B hbound hfull
  intro i j hij
  have hac : (σ i).prod (σ j) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  filter_upwards [hac.ae_le (hclique i j hij),
    Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp hi hj
  exact hp hi hj

/-- Every natural count vector has the actual conditional-average test.
Independent regions need only the tests for distinct labels; a region
used at least twice must be a genuine original clique region. -/
theorem conditional_multiplicity_average_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : κ → Set Ω) (hT : ∀ a, MeasurableSet (T a)) (hpos : ∀ a, 0 < μ (T a))
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (k : κ → ℕ) (hfull : FeasibleOrder μ A Y (∑ a, k a))
    (hself : ∀ a, 2 ≤ k a → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T a → p.2 ∈ T a → A p.1 p.2 = true)
    (hcross : ∀ a b, a ≠ b → 0 < k a → 0 < k b → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T a → p.2 ∈ T b → A p.1 p.2 = true) :
    multiplicityCharge (fun a b => ∫ p, Y p.1 p.2 ∂(cond μ (T a)).prod (cond μ (T b))) k ≤ 1 := by
  obtain ⟨label, hlabel⟩ := exists_label_with_counts k (∑ a, k a) rfl
  have hcount (i : Fin (∑ a, k a)) : 0 < k (label i) := by
    rw [← hlabel]
    unfold PhysicalPrimal.labelCount
    exact lt_of_lt_of_le (by simp) (Finset.single_le_sum (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have ht := conditional_clique_average_le_one (fun i => T (label i))
    (fun i => hT (label i)) (fun i => hpos (label i)) A Y hY B hbound hfull
    (fun i j hij => by
      by_cases heq : label i = label j
      · have hrepeat : 2 ≤ k (label i) := by
          rw [← hlabel]
          exact two_le_labelCount_of_eq label i j hij heq
        simpa only [← heq] using hself (label i) hrepeat
      · exact hcross (label i) (label j) heq (hcount i) (hcount j))
  change tupleCharge
    (fun a b => ∫ p, Y p.1 p.2 ∂(cond μ (T a)).prod (cond μ (T b))) label ≤ 1 at ht
  rw [tupleCharge_eq_multiplicityCharge] at ht
  simpa only [funext hlabel] using ht

end Erdos1017.FiniteArity
