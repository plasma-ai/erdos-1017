module

public import Erdos1017.Models.Capped.CappedTransport
public import Erdos1017.Models.Capped.CappedColorConfiguration
public import Erdos1017.Models.FiniteGraphCliqueViolation
public import Erdos1017.LowerBound.WeightedGraphDual
public import Erdos1017.LowerBound.WeightedGraphRealization
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Capped realization of a finite graph dual

A finite bounded graph dual has an all-orders-feasible capped realization on any
atomless compact metric Borel probability space
(`exists_fullyFeasible_realization`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

variable {n : ℕ}

/-- Uniform latent labels for a finite graph. -/
private def labelMeasure (n : ℕ) : Measure (Fin n) := uniformOn Set.univ

private theorem labelMeasure_real_singleton (i : Fin n) :
    (labelMeasure n).real {i} = 1 / (n : ℝ) := by
  rw [Measure.real, labelMeasure, uniformOn_univ]
  simp [Fintype.card_fin]

private theorem integral_labelMeasure (hn : 0 < n) (f : Fin n → ℝ) :
    (∫ i, f i ∂labelMeasure n) = (∑ i, f i) / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : IsProbabilityMeasure (labelMeasure n) := by unfold labelMeasure; infer_instance
  have hf : Integrable f (labelMeasure n) := Integrable.of_finite
  rw [integral_fintype hf]
  simp_rw [labelMeasure_real_singleton, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

private theorem integral_labelPair (hn : 0 < n) (f : Fin n × Fin n → ℝ) :
    (∫ p, f p ∂(labelMeasure n).prod (labelMeasure n)) =
      (∑ i : Fin n, ∑ j : Fin n, f (i, j)) / (n : ℝ) ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : IsProbabilityMeasure (labelMeasure n) := by unfold labelMeasure; infer_instance
  have hf : Integrable f ((labelMeasure n).prod (labelMeasure n)) := Integrable.of_finite
  rw [integral_prod _ hf]
  simp_rw [integral_labelMeasure hn]
  rw [← Finset.sum_div]
  ring

/-- The deterministic color of a pair of finite graph labels. -/
private def graphColor (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (i j : Fin n) : CappedColor := by
  classical
  exact if h : G.Adj i j then CappedColor.present (y i j) (hyIcc i j)
    else CappedColor.absent

private theorem graphColor_symm (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ)
    (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (i j : Fin n) :
    graphColor G y hyIcc i j = graphColor G y hyIcc j i := by
  classical
  by_cases hij : G.Adj i j
  · have hji : G.Adj j i := G.adj_symm hij
    simp [graphColor, hij, hji, hy.1 i j]
  · have hji : ¬G.Adj j i := fun h => hij (G.adj_symm h)
    simp [graphColor, hij, hji]

private theorem graphColor_adjacency (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1)
    (i j : Fin n) : CappedColor.adjacency (graphColor G y hyIcc i j) =
      if G.Adj i j then 1 else 0 := by
  classical
  split_ifs with hij <;>
    simp [graphColor, hij, CappedColor.adjacency, CappedColor.present, CappedColor.absent]

private theorem graphColor_charge (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (i j : Fin n) :
    CappedColor.charge (graphColor G y hyIcc i j) = y i j := by
  classical
  by_cases hij : G.Adj i j
  · simp [graphColor, hij, CappedColor.charge, CappedColor.present]
  · simp [graphColor, hij, hy.2.1 i j hij]

/-- The finite-label decorated kernel records one actual bounded dual
coefficient on every graph edge. -/
private def graphModel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) : Model (Fin n × Ω) μ := by
  let labels : ((Fin n × Ω) × (Fin n × Ω)) → Fin n × Fin n :=
    fun p => (p.1.1, p.2.1)
  have hlabels : Measurable labels :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  let color : ((Fin n × Ω) × (Fin n × Ω)) → CappedColor :=
    fun p => graphColor G y hyIcc p.1.1 p.2.1
  have hcolor : Measurable color :=
    (measurable_of_finite (fun q : Fin n × Fin n => graphColor G y hyIcc q.1 q.2)).comp hlabels
  exact {
    kernel := Kernel.deterministic color hcolor
    markov := by infer_instance
    symm := Filter.Eventually.of_forall (fun p => by
      simp only [Kernel.deterministic_apply]
      exact congrArg Measure.dirac (graphColor_symm G y hy hyIcc p.1.1 p.2.1).symm) }

private theorem graphModel_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1)
    (f : CappedColor → ℝ) (p : (Fin n × Ω) × (Fin n × Ω)) :
    (graphModel μ G y hy hyIcc).moment f p =
      f (graphColor G y hyIcc p.1.1 p.2.1) := by
  simp [DecoratedKernel.moment, graphModel, Kernel.deterministic_apply]

private def sampledGraphColors {k : ℕ} (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1)
    (π : Fin k → Fin n) (e : CliquePair k) : CappedColor :=
  graphColor G y hyIcc (π e.val.1) (π e.val.2)

private theorem pairColor_sampledGraphColors {k : ℕ} (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (π : Fin k → Fin n)
    (i j : Fin k) :
    pairColor (sampledGraphColors G y hyIcc π) i j =
      graphColor G y hyIcc (π i) (π j) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [pairColor, sampledGraphColors, hij]
  · simp [pairColor, graphColor]
  · rw [pairColor_symm]
    rw [graphColor_symm G y hy hyIcc (π i) (π j)]
    simp [pairColor, sampledGraphColors, hji]

private theorem sampledGraphColors_dualFeasible {k : ℕ} (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (π : Fin k → Fin n) :
    WeightedGraph.DualFeasible
      (configurationGraph (sampledGraphColors G y hyIcc π))
      (chargeMatrix (sampledGraphColors G y hyIcc π)) := by
  have hgraph : configurationGraph (sampledGraphColors G y hyIcc π) = G.comap π := by
    ext i j
    change CappedColor.adjacency
      (pairColor (sampledGraphColors G y hyIcc π) i j) = 1 ↔ G.Adj (π i) (π j)
    rw [pairColor_sampledGraphColors G y hy hyIcc π i j,
      graphColor_adjacency]
    simp
  have hmatrix : chargeMatrix (sampledGraphColors G y hyIcc π) =
      (fun i j => y (π i) (π j)) := by
    funext i j
    rw [chargeMatrix, pairColor_sampledGraphColors G y hy hyIcc π i j,
      graphColor_charge G y hy hyIcc]
  rw [hgraph, hmatrix]
  exact WeightedGraph.dualFeasible_comap G π y hy

private theorem graphModel_cliqueLaw_ae {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (x : Fin k → Fin n × Ω) :
    ∀ᵐ c ∂cliqueLaw (graphModel μ G y hy hyIcc) x,
      c = sampledGraphColors G y hyIcc (fun i => (x i).1) := by
  change ∀ᵐ c ∂Measure.pi (fun e : CliquePair k =>
      Measure.dirac (sampledGraphColors G y hyIcc (fun i => (x i).1) e)),
    c = sampledGraphColors G y hyIcc (fun i => (x i).1)
  have h := Measure.ae_eq_pi
    (μ := fun e : CliquePair k =>
      Measure.dirac (sampledGraphColors G y hyIcc (fun i => (x i).1) e))
    (f := fun _ => id)
    (f' := fun e _ => sampledGraphColors G y hyIcc (fun i => (x i).1) e)
    (fun _ => ae_eq_dirac (fun c : CappedColor => c))
  filter_upwards [h] with c hc
  exact hc

/-- The finite-label decorated model passes every imposed capped clique
test, at every clique order. -/
private theorem graphModel_feasible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (r : ℕ) :
    Feasible r (graphModel μ G y hy hyIcc) := by
  intro k _ _
  filter_upwards with x
  filter_upwards [graphModel_cliqueLaw_ae μ G y hy hyIcc x] with c hc
  subst c
  exact violation_eq_zero_of_configuration_dualFeasible _
    (sampledGraphColors_dualFeasible G y hy hyIcc (fun i => (x i).1))

private theorem integral_labelProduct {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hn : 0 < n)
    (f : Fin n × Fin n → ℝ) :
    (∫ p : (Fin n × Ω) × (Fin n × Ω), f (p.1.1, p.2.1)
      ∂((labelMeasure n).prod μ).prod ((labelMeasure n).prod μ)) =
      (∑ i : Fin n, ∑ j : Fin n, f (i, j)) / (n : ℝ) ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : IsProbabilityMeasure (labelMeasure n) := by unfold labelMeasure; infer_instance
  let ν : Measure (Fin n × Ω) := (labelMeasure n).prod μ
  have hfst : MeasurePreserving (fun p : Fin n × Ω => p.1) ν (labelMeasure n) :=
    measurePreserving_fst
  have hpair := hfst.prod hfst
  have hf : StronglyMeasurable f := (measurable_of_finite f).stronglyMeasurable
  have he := integral_map_of_stronglyMeasurable (μ := ν.prod ν) hpair.measurable hf
  rw [hpair.map_eq] at he
  exact he.symm.trans (integral_labelPair hn f)

private theorem graphModel_density {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G : SimpleGraph (Fin n))
    (hn : 0 < n) (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) :
    density (graphModel ((labelMeasure n).prod μ) G y hy hyIcc) =
      (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (1 : ℝ) else 0) / 2 =
      (G.edgeSet.ncard : ℝ) := by
    simpa [WeightedGraph.objective, WeightedGraph.adjacencyMatrix] using
      WeightedGraph.adjacency_objective G
  calc
    density (graphModel ((labelMeasure n).prod μ) G y hy hyIcc) =
        ((∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (1 : ℝ) else 0) /
          (n : ℝ) ^ 2) / 2 := by
      unfold density
      simp_rw [graphModel_moment, graphColor_adjacency]
      exact congrArg (fun z : ℝ => z / 2)
        (integral_labelProduct (Ω := Ω) (μ := μ) hn
          (fun p : Fin n × Fin n => if G.Adj p.1 p.2 then 1 else 0))
    _ = (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 := by
      rw [← hsum]
      ring

private theorem graphModel_objective {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G : SimpleGraph (Fin n))
    (hn : 0 < n) (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) :
    objective (graphModel ((labelMeasure n).prod μ) G y hy hyIcc) =
      WeightedGraph.objective (fun _ => 1) y / (n : ℝ) ^ 2 := by
  calc
    objective (graphModel ((labelMeasure n).prod μ) G y hy hyIcc) =
        ((∑ i : Fin n, ∑ j : Fin n, y i j) / (n : ℝ) ^ 2) / 2 := by
      unfold objective
      simp_rw [graphModel_moment, graphColor_charge G y hy hyIcc]
      exact congrArg (fun z : ℝ => z / 2)
        (integral_labelProduct (Ω := Ω) (μ := μ) hn
          (fun p : Fin n × Fin n => y p.1 p.2))
    _ = WeightedGraph.objective (fun _ => 1) y / (n : ℝ) ^ 2 := by
      simp [WeightedGraph.objective]
      ring

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- A finite bounded graph dual has an actual all-orders-feasible capped
realization on any atomless compact metric Borel probability space. -/
theorem exists_fullyFeasible_realization (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) :
    ∃ W : Model Ω μ, (∀ r, Feasible r W) ∧
      density W = (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 ∧
      objective W = WeightedGraph.objective (fun _ => 1) y / (n : ℝ) ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : IsProbabilityMeasure (labelMeasure n) := by unfold labelMeasure; infer_instance
  let ν : Measure (Fin n × Ω) := (labelMeasure n).prod μ
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have : NullSingletonClass ν := by dsimp [ν]; infer_instance
  obtain ⟨h, hh⟩ := exists_measurePreserving (μ := μ) (ν := ν)
  let W₀ : Model (Fin n × Ω) ν := graphModel ν G y hy hyIcc
  let W : Model Ω μ := W₀.pullback h hh
  refine ⟨W, ?_, ?_, ?_⟩
  · intro r
    exact feasible_pullback W₀ (graphModel_feasible ν G y hy hyIcc r) h hh
  · exact (density_pullback W₀ h hh).trans
      (graphModel_density (μ := μ) G hn y hy hyIcc)
  · exact (objective_pullback W₀ h hh).trans
      (graphModel_objective (μ := μ) G hn y hy hyIcc)

end Erdos1017.CappedModel
