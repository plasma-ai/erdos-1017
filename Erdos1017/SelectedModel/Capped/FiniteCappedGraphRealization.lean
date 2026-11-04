module

public import Erdos1017.Models.Capped.CappedTransport
public import Erdos1017.Models.Capped.CappedColorConfiguration
public import Erdos1017.SelectedModel.Capped.FractionalCappedBoundedDual
public import Erdos1017.Models.Capped.CappedAttainment
public import Erdos1017.LowerBound.WeightedGraphRealization
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Realizing a finite capped dual as a decorated competitor

A bounded finite capped dual has a tested-order realization on any atomless
compact metric Borel probability space, so the restricted finite clique LP
realizes a feasible decorated competitor at the exact normalized graph density
(`value_le_capValue`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.FiniteCappedRealization

variable {n N : ℕ}

variable {k : ℕ}

/-- An actually feasible finite charge matrix makes the full-clique test vanish. -/
theorem violation_eq_zero_of_capped_configuration
    (c : CliquePair k → CappedColor) (hkN : k ≤ N)
    (hc : WeightedGraph.CappedDualFeasible (configurationGraph c) N (chargeMatrix c)) :
    violation c = 0 := by
  classical
  by_cases hz : ∃ p, CappedColor.adjacency (c p) = 0
  · obtain ⟨p, hp⟩ := hz
    have hprod : (∏ q, CappedColor.adjacency (c q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hp
    simp only [violation, hprod, mul_zero]
  · have hA (p : CliquePair k) : CappedColor.adjacency (c p) = 1 :=
      (CappedColor.adjacency_eq_zero_or_one _).resolve_left (fun hp => hz ⟨p, hp⟩)
    have hclique : (configurationGraph c).IsClique
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
      intro i _ j _ hij
      change CappedColor.adjacency (pairColor c i j) = 1
      rcases lt_or_gt_of_ne hij with h | h
      · rw [pairColor_lt c i j h]
        exact hA _
      · rw [pairColor_symm, pairColor_lt c j i h]
        exact hA _
    have hcharge := hc.2.2 Finset.univ (by simpa using hkN) hclique
    have hobj : WeightedGraph.charge (chargeMatrix c) Finset.univ =
        WeightedGraph.objective (fun _ => 1) (chargeMatrix c) := by
      simp [WeightedGraph.charge_eq_sum, WeightedGraph.objective]
    rw [hobj, chargeMatrix_objective] at hcharge
    simp only [violation, hA, Finset.prod_const_one, mul_one,
      max_eq_right (sub_nonpos.mpr hcharge)]

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
    (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) (π : Fin k → Fin n) :
    WeightedGraph.CappedDualFeasible
      (configurationGraph (sampledGraphColors G y hyIcc π)) N
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
  exact WeightedGraph.capped_dualFeasible_comap G N π y hy

private theorem graphModel_cliqueLaw_ae {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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

/-- The finite-label decorated model passes precisely the imposed capped
clique tests, using no larger-order dual constraints. -/
private theorem graphModel_feasible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Fin n × Ω)) (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) :
    Feasible N (graphModel μ G y hy hyIcc) := by
  intro k _ hkN
  filter_upwards with x
  filter_upwards [graphModel_cliqueLaw_ae μ G y hy hyIcc x] with c hc
  subst c
  exact violation_eq_zero_of_capped_configuration _ hkN
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
    (hn : 0 < n) (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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
    (hn : 0 < n) (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
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

/-- A bounded finite capped dual has an actual tested-order realization
on any atomless compact metric Borel probability space. -/
theorem exists_capped_realization (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.CappedDualFeasible G N y)
    (hyIcc : ∀ i j, y i j ∈ Icc (-3 : ℝ) 1) :
    ∃ W : Model Ω μ, Feasible N W ∧
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
  · exact feasible_pullback W₀ (graphModel_feasible ν G y hy hyIcc) h hh
  · exact (density_pullback W₀ h hh).trans
      (graphModel_density (μ := μ) G hn y hy hyIcc)
  · exact (objective_pullback W₀ h hh).trans
      (graphModel_objective (μ := μ) G hn y hy hyIcc)

end Erdos1017.CappedModel.FiniteCappedRealization

namespace Erdos1017.FractionalCappedGraph

open CappedModel

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The actual bounded dual of the restricted finite clique LP realizes an
N-feasible decorated competitor at the exact normalized graph density.
No larger clique constraint is used in this comparison. -/
theorem value_le_capValue (G : SimpleGraph (Fin n)) (hn : 0 < n) (N : ℕ) (hN : 2 ≤ N) :
    value G N / (n : ℝ) ^ 2 ≤ capValue Ω μ N ((G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2) := by
  obtain ⟨y, hy, hIcc, hopt⟩ := exists_bounded_dual G N hN
  obtain ⟨W, hW, hdW, hoW⟩ := FiniteCappedRealization.exists_capped_realization (μ := μ) G hn y hy hIcc
  obtain ⟨V, _, hdV, hoV, hmax⟩ := exists_fixedMeasureMaximizer (μ := μ) N (density W) (density_mem W)
  have hcompare := hmax.2 W hW hdV.symm
  rw [hoV, hdW, hoW, hopt] at hcompare
  exact hcompare

end Erdos1017.FractionalCappedGraph
