module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalSampling
public import Erdos1017.SelectedModel.Capped.FiniteCappedGraphRealization
public import Erdos1017.SelectedModel.Capped.CappedValueContinuity
public import Erdos1017.Models.Decorated.DecoratedSamplingConcentration
public import Erdos1017.SelectedModel.Capped.CappedDeterministicTests

/-!
# Capped LP cost of sampled graphs

The capped LP cost of the graph induced by independent physical samples. The
expected cost has the physical normalization `n * (n - 1)`. The sampling
measures and their occupation identity are constructed separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos1017.FiniteCappedSamplingCost

open PhysicalPrimalSampling CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

attribute [local instance] Classical.propDecidable

/-- Every real observable of the finitely many actual graph outcomes is
measurable, even though adjacency is only measurable in the physical vertices. -/
theorem measurable_graph_observable {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (F : SimpleGraph (Fin n) → ℝ) :
    Measurable (fun v : Fin n → Ω => F (sampleGraph A hsym v)) := by
  have heq : (fun v : Fin n → Ω => F (sampleGraph A hsym v)) =
      fun v => ∑ G : SimpleGraph (Fin n),
        {v : Fin n → Ω | sampleGraph A hsym v = G}.indicator (fun _ => F G) v := by
    funext v
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp
  rw [heq]
  exact Finset.measurable_sum _ (fun G _ =>
    measurable_const.indicator (sampleGraph_event_measurable A hsym hA G))

/-- Finite graph observables are genuinely bounded and hence integrable
under the independent vertex sampling law. -/
theorem integrable_graph_observable {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (F : SimpleGraph (Fin n) → ℝ) :
    Integrable (fun v : Fin n → Ω => F (sampleGraph A hsym v))
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply Integrable.of_bound (measurable_graph_observable A hsym hA F).aestronglyMeasurable
    (∑ G : SimpleGraph (Fin n), ‖F G‖)
  exact Filter.Eventually.of_forall (fun v => Finset.single_le_sum
    (fun G _ => norm_nonneg (F G)) (Finset.mem_univ (sampleGraph A hsym v)))

/-- The density of the actual finite sampled graph, with n-squared normalization. -/
def sampleGraphDensity {n : ℕ} (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (v : Fin n → Ω) : ℝ :=
  ((sampleGraph A hsym v).edgeSet.ncard : ℝ) / (n : ℝ) ^ 2

/-- The Boolean physical adjacency density. -/
def physicalDensity (μ : Measure Ω) (A : Ω → Ω → Bool) : ℝ :=
  (∫ p, if A p.1 p.2 = true then (1 : ℝ) else 0 ∂μ.prod μ) / 2

/-- The signed physical dual objective. -/
def physicalObjective (μ : Measure Ω) (Y : Ω → Ω → ℝ) : ℝ :=
  (∫ p, Y p.1 p.2 ∂μ.prod μ) / 2

/-- The expected actual optimum of the finite capped clique LP. -/
def expectedCappedCost (μ : Measure Ω) (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (N n : ℕ) : ℝ :=
  (∫ v : Fin n → Ω, FractionalCappedGraph.value (sampleGraph A hsym v) N
    ∂Measure.pi (fun _ : Fin n => μ)) / ((n * (n - 1) : ℕ) : ℝ)

private def adjacencyColor (A : Ω → Ω → Bool) (p : Ω × Ω) : CappedColor :=
  if A p.1 p.2 = true then CappedColor.present 0 (by norm_num) else CappedColor.absent

private theorem measurable_adjacencyColor (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) : Measurable (adjacencyColor A) :=
  Measurable.ite (hA (measurableSet_singleton true)) measurable_const measurable_const

omit [IsProbabilityMeasure μ] in
private def adjacencyModel (μ : Measure Ω) (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) : Model Ω μ where
  kernel := Kernel.deterministic (adjacencyColor A) (measurable_adjacencyColor A hA)
  markov := by infer_instance
  symm := Filter.Eventually.of_forall (fun p => by
    simp only [Kernel.deterministic_apply]
    congr 1
    change adjacencyColor A (p.2, p.1) = adjacencyColor A p
    simp only [adjacencyColor, hsym p.2 p.1])

omit [IsProbabilityMeasure μ] in
private theorem adjacencyModel_moment (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) (p : Ω × Ω) :
    (adjacencyModel μ A hsym hA).moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0 := by
  by_cases h : A p.1 p.2 = true <;>
    simp [DecoratedKernel.moment, adjacencyModel, Kernel.deterministic_apply,
      adjacencyColor, h, CappedColor.adjacency, CappedColor.present, CappedColor.absent]

omit [IsProbabilityMeasure μ] in
private theorem density_adjacencyModel (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    density (adjacencyModel μ A hsym hA) = physicalDensity μ A := by
  unfold density physicalDensity
  simp_rw [adjacencyModel_moment]

private def sampledColors {n : ℕ} (A : Ω → Ω → Bool) (x : Fin n → Ω)
    (e : CliquePair n) : CappedColor := adjacencyColor A (x e.val.1, x e.val.2)

omit [IsProbabilityMeasure μ] in
private theorem adjacencyModel_cliqueLaw_ae {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) (x : Fin n → Ω) :
    ∀ᵐ c ∂cliqueLaw (adjacencyModel μ A hsym hA) x, c = sampledColors A x := by
  change ∀ᵐ c ∂Measure.pi (fun e : CliquePair n => Measure.dirac (sampledColors A x e)),
    c = sampledColors A x
  have h := Measure.ae_eq_pi
    (μ := fun e : CliquePair n => Measure.dirac (sampledColors A x e))
    (f := fun _ => id) (f' := fun e _ => sampledColors A x e)
    (fun _ => ae_eq_dirac (fun c : CappedColor => c))
  filter_upwards [h] with c hc
  exact hc

omit [MeasurableSpace Ω] in
private theorem configurationGraph_sampledColors {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (x : Fin n → Ω) :
    configurationGraph (sampledColors A x) = sampleGraph A hsym x := by
  ext i j
  change CappedColor.adjacency (pairColor (sampledColors A x) i j) = 1 ↔
    i ≠ j ∧ A (x i) (x j) = true
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases h : A (x i) (x j) = true <;>
      simp [pairColor, hij, sampledColors, adjacencyColor, h,
        CappedColor.adjacency, CappedColor.present, CappedColor.absent, ne_of_lt hij]
  · simp
  · rw [pairColor_symm]
    by_cases h : A (x i) (x j) = true <;>
      simp [pairColor, hji, sampledColors, adjacencyColor, h,
        CappedColor.adjacency, CappedColor.present, CappedColor.absent, ne_of_gt hji,
        hsym (x j) (x i)]

omit [MeasurableSpace Ω] in
private theorem sampleDensity_sampledColors {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (x : Fin n → Ω) :
    sampleDensity (sampledColors A x) = sampleGraphDensity A hsym x := by
  rw [sampleDensity, configuration_adjacency_sum, configurationGraph_sampledColors]
  rfl

private theorem integral_adjacencyModel_sampledColorLaw {n : ℕ} (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (F : C(CliquePair n → CappedColor, ℝ)) :
    (∫ c, F c ∂(sampledColorLaw (adjacencyModel μ A hsym hA) n :
      Measure (CliquePair n → CappedColor))) =
      ∫ x : Fin n → Ω, F (sampledColors A x) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_sampledColorLaw, continuousTestIntegral]
  apply integral_congr_ae
  filter_upwards with x
  calc
    (∫ c, F c ∂cliqueLaw (adjacencyModel μ A hsym hA) x) =
        ∫ _c, F (sampledColors A x) ∂cliqueLaw (adjacencyModel μ A hsym hA) x :=
      integral_congr_ae (by
        filter_upwards [adjacencyModel_cliqueLaw_ae A hsym hA x] with c hc
        rw [hc])
    _ = _ := by simp

/-- The decorated sampling concentration applies to the actual
Boolean sample graph, with no continuity assumption on physical adjacency. -/
theorem sampleGraphDensity_abs_error_tendsto (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    Tendsto (fun n => ∫ x : Fin n → Ω, |sampleGraphDensity A hsym x - physicalDensity μ A|
      ∂Measure.pi (fun _ : Fin n => μ)) atTop (𝓝 0) := by
  have h := sampleDensity_abs_error_tendsto (adjacencyModel μ A hsym hA)
  have heq (n : ℕ) :
      (∫ c, |sampleDensity c - density (adjacencyModel μ A hsym hA)|
        ∂(sampledColorLaw (adjacencyModel μ A hsym hA) n : Measure (CliquePair n → CappedColor))) =
      ∫ x : Fin n → Ω, |sampleGraphDensity A hsym x - physicalDensity μ A|
        ∂Measure.pi (fun _ : Fin n => μ) := by
    let F : C(CliquePair n → CappedColor, ℝ) :=
      ⟨fun c => |sampleDensity c - density (adjacencyModel μ A hsym hA)|, by
        unfold sampleDensity
        fun_prop⟩
    have hi := integral_adjacencyModel_sampledColorLaw (μ := μ) A hsym hA F
    simpa only [F, ContinuousMap.coe_mk, sampleDensity_sampledColors A hsym,
      density_adjacencyModel] using hi
  simpa only [heq] using h

/-- Every actual capped physical clique test becomes a capped dual
constraint on almost every sampled graph, simultaneously for all its subsets. -/
theorem ae_sampled_capped_dual (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0) (N n : ℕ)
    (hcap : ∀ k, 2 ≤ k → k ≤ N → FiniteArity.FeasibleOrder μ A Y k) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      WeightedGraph.CappedDualFeasible (sampleGraph A hsym v) N
        (fun i j => if i = j then 0 else Y (v i) (v j)) := by
  have htests : ∀ k, k ≤ N → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
      FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1 := by
    intro k hk
    by_cases h2 : 2 ≤ k
    · exact hcap k h2 hk
    · exact Filter.Eventually.of_forall (fun v _ => by
        rw [FiniteArity.tupleCharge_small (by omega) Y v]
        norm_num)
  have hsub := FiniteArity.ae_all_subtuples μ N n
    (fun _ v => FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) htests
  have hpairs := FiniteArity.ae_all_pairs μ n _ (hYsym.and hzero)
  filter_upwards [hsub, hpairs] with v hv hpairs
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp only [hij, Ne.symm hij, ↓reduceIte]
      exact (hpairs i j hij).1
  · intro i j hij
    by_cases heq : i = j
    · simp [heq]
    · have ha : A (v i) (v j) = false := Bool.eq_false_iff.mpr
        (fun h => hij ⟨heq, h⟩)
      simp only [heq, ↓reduceIte]
      exact (hpairs i j heq).2 ha
  · intro S hSN hS
    let e := (S.orderEmbOfFin rfl).toEmbedding
    have hclique : FiniteArity.TupleClique A (fun i => v (e i)) := by
      intro i j hij
      exact (hS (by simp [e]) (by simp [e]) (fun h => hij (e.injective h))).2
    have ht := hv S.card hSN e hclique
    rw [FiniteArity.tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ S rfl] at ht
    rw [charge_eq_pairCharge]
    exact ht

/-- Actual finite capped weak duality bounds the sampled signed charge. -/
theorem ae_tupleCharge_le_value (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (Y : Ω → Ω → ℝ)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0) (N n : ℕ) (hN : 2 ≤ N)
    (hcap : ∀ k, 2 ≤ k → k ≤ N → FiniteArity.FeasibleOrder μ A Y k) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      FiniteArity.tupleCharge Y v ≤ FractionalCappedGraph.value (sampleGraph A hsym v) N := by
  filter_upwards [ae_sampled_capped_dual A hsym Y hYsym hzero N n hcap] with v hv
  have h := WeightedGraph.capped_dual_objective_le_value (sampleGraph A hsym v) N hN _ hv
  simpa only [WeightedGraph.objective, one_mul, mul_one, FiniteArity.tupleCharge,
    FiniteArity.pairCharge, FiniteArity.crossSum] using h

private theorem integrable_pair_sample {n : ℕ} (Y : Ω → Ω → ℝ)
    (hY : Integrable (Function.uncurry Y) (μ.prod μ)) (e : CliquePair n) :
    Integrable (fun v : Fin n → Ω => Y (v e.val.1) (v e.val.2))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hp := FiniteArity.measurePreserving_pair μ e.val.1 e.val.2 (ne_of_lt e.property)
  exact hp.integrable_comp_of_integrable hY

private theorem integral_pair_sample {n : ℕ} (Y : Ω → Ω → ℝ)
    (hY : Integrable (Function.uncurry Y) (μ.prod μ)) (e : CliquePair n) :
    (∫ v : Fin n → Ω, Y (v e.val.1) (v e.val.2) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ p, Y p.1 p.2 ∂μ.prod μ := by
  have hp := FiniteArity.measurePreserving_pair μ e.val.1 e.val.2 (ne_of_lt e.property)
  have hi := integral_map (μ := Measure.pi (fun _ : Fin n => μ)) hp.measurable.aemeasurable
    (f := Function.uncurry Y) (by simpa only [hp.map_eq] using hY.aestronglyMeasurable)
  rw [hp.map_eq] at hi
  exact hi.symm

private theorem ae_tupleCharge_eq_upper (Y : Ω → Ω → ℝ)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1) (n : ℕ) :
    (fun v : Fin n → Ω => FiniteArity.tupleCharge Y v) =ᵐ[Measure.pi (fun _ : Fin n => μ)]
      fun v => ∑ e : CliquePair n, Y (v e.val.1) (v e.val.2) := by
  filter_upwards [FiniteArity.ae_all_pairs μ n _ hYsym] with v hv
  exact tupleCharge_eq_upper Y v hv

/-- The signed physical dual has exactly the unordered-pair sample expectation. -/
theorem integral_tupleCharge (Y : Ω → Ω → ℝ)
    (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1) (n : ℕ) :
    (∫ v : Fin n → Ω, FiniteArity.tupleCharge Y v ∂Measure.pi (fun _ : Fin n => μ)) =
      (n.choose 2 : ℝ) * (2 * physicalObjective μ Y) := by
  rw [integral_congr_ae (ae_tupleCharge_eq_upper Y hYsym n)]
  rw [integral_finsetSum Finset.univ (fun e _ => integrable_pair_sample Y hY e)]
  simp_rw [integral_pair_sample Y hY]
  simp only [Finset.sum_const, Finset.card_univ, card_cliquePair, nsmul_eq_mul]
  unfold physicalObjective
  ring

/-- The expected actual capped optimum dominates every integrable physical
dual satisfying exactly the imposed orders, with no omitted-order assumption. -/
theorem physicalObjective_le_expectedCappedCost (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0) (N n : ℕ) (hN : 2 ≤ N) (hn : 2 ≤ n)
    (hcap : ∀ k, 2 ≤ k → k ≤ N → FiniteArity.FeasibleOrder μ A Y k) :
    physicalObjective μ Y ≤ expectedCappedCost μ A hsym N n := by
  have hcharge : Integrable (fun v : Fin n → Ω => FiniteArity.tupleCharge Y v)
      (Measure.pi (fun _ : Fin n => μ)) := by
    exact (integrable_finsetSum _ (fun e _ => integrable_pair_sample Y hY e)).congr
      (ae_tupleCharge_eq_upper Y hYsym n).symm
  have hbound := integral_mono_ae hcharge
    (integrable_graph_observable A hsym hA (fun G => FractionalCappedGraph.value G N))
    (ae_tupleCharge_le_value A hsym Y hYsym hzero N n hN hcap)
  rw [integral_tupleCharge Y hY hYsym n] at hbound
  have hn1 : 1 ≤ n := by omega
  have hden : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (show 0 < n by omega) (show 0 < n - 1 by omega))
  have hchoose : (n.choose 2 : ℝ) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one, Nat.cast_choose_two]
    ring
  rw [← mul_assoc, hchoose] at hbound
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
/-- Every normalized finite graph density lies in the entire admissible
interval, including samples outside any strict-gap region. -/
theorem finiteGraphDensity_mem_Icc {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 ∈ Icc (0 : ℝ) (1 / 2) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (∑ _i : Fin n, (1 : ℝ) / (n : ℝ)) = 1 := by simp [ne_of_gt hnreal]
  have h := WeightedGraph.density_mem_Icc G (fun _ => (1 : ℝ) / (n : ℝ))
    (fun _ => by positivity) hs
  simpa only [WeightedGraph.density, WeightedGraph.objective_div,
    WeightedGraph.adjacency_objective] using h

/-- The physical density is admissible without any pointwise regularity
beyond measurable symmetric Boolean adjacency. -/
theorem physicalDensity_mem_Icc (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    physicalDensity μ A ∈ Icc (0 : ℝ) (1 / 2) := by
  rw [← density_adjacencyModel A hsym hA]
  exact density_mem _

section CappedComparison

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- The actual restricted finite LP realizes a capped competitor at each
sampled density. Three-Lipschitz continuity then gives the upper cost estimate
with the exact physical finite-sample normalization. -/
theorem expectedCappedCost_le (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (N n : ℕ) (hN : 2 ≤ N) (hn : 2 ≤ n) (d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    expectedCappedCost μ A hsym N n ≤
      ((n : ℝ) / ((n : ℝ) - 1)) * (capValue Ω μ N d +
        3 * ∫ v : Fin n → Ω, |sampleGraphDensity A hsym v - d|
          ∂Measure.pi (fun _ : Fin n => μ)) := by
  have hn0 : 0 < n := by omega
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : 1 ≤ n := by omega
  have hcost := integrable_graph_observable (μ := μ) A hsym hA
    (fun G : SimpleGraph (Fin n) => FractionalCappedGraph.value G N)
  have herror := integrable_graph_observable (μ := μ) A hsym hA
    (fun G : SimpleGraph (Fin n) => |(G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 - d|)
  have hpoint (v : Fin n → Ω) :
      FractionalCappedGraph.value (sampleGraph A hsym v) N / (n : ℝ) ^ 2 ≤
        capValue Ω μ N d + 3 * |sampleGraphDensity A hsym v - d| := by
    exact (FractionalCappedGraph.value_le_capValue (Ω := Ω) (μ := μ)
      (sampleGraph A hsym v) hn0 N hN).trans
      (capValue_le_add_three_mul_abs_sub (μ := μ) N _ d
        (finiteGraphDensity_mem_Icc _ hn0) hd)
  have hi := integral_mono (hcost.div_const ((n : ℝ) ^ 2))
    ((integrable_const (capValue Ω μ N d)).add (herror.const_mul 3)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_div, integral_add (integrable_const _) (herror.const_mul 3),
    integral_const, integral_const_mul] at hi
  simp only [probReal_univ, one_smul] at hi
  have hden : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
  calc
    expectedCappedCost μ A hsym N n = ((n : ℝ) / ((n : ℝ) - 1)) *
        ((∫ v : Fin n → Ω, FractionalCappedGraph.value (sampleGraph A hsym v) N
          ∂Measure.pi (fun _ : Fin n => μ)) / (n : ℝ) ^ 2) := by
      unfold expectedCappedCost
      rw [hden]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

/-- The n/(n−1) correction in the physical normalization tends to one. -/
theorem normalization_ratio_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds.sub
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have heq : ∀ᶠ n : ℕ in atTop,
      (1 - 1 / (n : ℝ))⁻¹ = (n : ℝ) / ((n : ℝ) - 1) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    field_simp
  simpa only [sub_zero, inv_one] using h.congr' heq

/-- At actual capped optimality, the expected actual finite capped LP costs
converge to the physical objective. Only clique orders through N are used. -/
theorem expectedCappedCost_tendsto (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0) (N : ℕ) (hN : 2 ≤ N)
    (hcap : ∀ k, 2 ≤ k → k ≤ N → FiniteArity.FeasibleOrder μ A Y k)
    (hopt : physicalObjective μ Y = capValue Ω μ N (physicalDensity μ A)) :
    Tendsto (fun n => expectedCappedCost μ A hsym N n) atTop (𝓝 (physicalObjective μ Y)) := by
  have hupper : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) - 1)) *
      (capValue Ω μ N (physicalDensity μ A) +
        3 * ∫ v : Fin n → Ω, |sampleGraphDensity A hsym v - physicalDensity μ A|
          ∂Measure.pi (fun _ : Fin n => μ))) atTop (𝓝 (physicalObjective μ Y)) := by
    simpa only [mul_zero, add_zero, one_mul, ← hopt] using
      normalization_ratio_tendsto.mul
        (tendsto_const_nhds.add ((sampleGraphDensity_abs_error_tendsto A hsym hA).const_mul 3))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact physicalObjective_le_expectedCappedCost A hsym hA Y hY hYsym hzero N n hN hn hcap
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact expectedCappedCost_le A hsym hA N n hN hn _ (physicalDensity_mem_Icc A hsym hA)

/-- The same actual cost convergence has the full value as its limit when
finite-order stabilization identifies the target capped value with F. -/
theorem expectedCappedCost_tendsto_densityLimit (A : Ω → Ω → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0) (N : ℕ) (hN : 2 ≤ N)
    (hcap : ∀ k, 2 ≤ k → k ≤ N → FiniteArity.FeasibleOrder μ A Y k)
    (hobjective : physicalObjective μ Y = FractionalGraph.densityLimit (physicalDensity μ A))
    (hvalue : capValue Ω μ N (physicalDensity μ A) =
      FractionalGraph.densityLimit (physicalDensity μ A)) :
    Tendsto (fun n => expectedCappedCost μ A hsym N n) atTop
      (𝓝 (FractionalGraph.densityLimit (physicalDensity μ A))) := by
  rw [← hobjective]
  exact expectedCappedCost_tendsto A hsym hA Y hY hYsym hzero N hN hcap
    (hobjective.trans hvalue.symm)

end CappedComparison

end Erdos1017.FiniteCappedSamplingCost
