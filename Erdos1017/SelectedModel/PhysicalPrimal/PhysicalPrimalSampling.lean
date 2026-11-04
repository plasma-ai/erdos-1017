module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalSymmetrization
public import Erdos1017.FractionalLimit.FractionalGraphEdit
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Balanced physical measures from finite partitions

Averaging finite fractional partitions gives exactly balanced physical measures.
Occupation here counts both orientations, so its demand is `G * μ²`; dividing
this identity by two gives the unordered normalization. No finite capped LP or
optimality assertion is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos1017.PhysicalPrimalSampling

open PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

attribute [local instance] Classical.propDecidable

/-- The actual labeled graph induced by one physical sample. -/
def sampleGraph {n : ℕ} (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (v : Fin n → V) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A (v i) (v j) = true
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [hsym (v j) (v i)] using h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem sampleGraph_event_measurable {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A))
    (G : SimpleGraph (Fin n)) :
    MeasurableSet {v : Fin n → V | sampleGraph A hsym v = G} := by
  have heq : {v : Fin n → V | sampleGraph A hsym v = G} =
      {v | ∀ i j, (i ≠ j ∧ A (v i) (v j) = true) ↔ G.Adj i j} := by
    ext v
    exact ⟨fun h i j => by rw [← h]; rfl,
      fun h => SimpleGraph.ext (funext₂ fun i j => propext (h i j))⟩
  rw [heq]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact ((MeasurableSet.const (i ≠ j)).inter
    ((hA.comp (show Measurable (fun v : Fin n → V => (v i, v j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)))
        (measurableSet_singleton true))).iff (MeasurableSet.const (G.Adj i j))

/-- Restrict the independent sample to one of its finitely many graph outcomes. -/
def graphEventLaw (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (G : SimpleGraph (Fin n)) : Measure (Fin n → V) :=
  (Measure.pi (fun _ : Fin n => μ)).restrict {v | sampleGraph A hsym v = G}

instance graphEventLaw_finite (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x) (G : SimpleGraph (Fin n)) :
    IsFiniteMeasure (graphEventLaw μ A hsym G) := by
  unfold graphEventLaw
  infer_instance

private theorem graphEventLaw_sum (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (hA : Measurable (Function.uncurry A)) :
    (∑ G : SimpleGraph (Fin n), graphEventLaw μ A hsym G) =
      Measure.pi (fun _ : Fin n => μ) := by
  have hdisj : Pairwise (fun G H : SimpleGraph (Fin n) => Disjoint
      {v : Fin n → V | sampleGraph A hsym v = G}
      {v : Fin n → V | sampleGraph A hsym v = H}) := by
    intro G H hGH
    apply Set.disjoint_left.mpr
    intro v hvG hvH
    exact hGH (hvG.symm.trans hvH)
  have hunion : (⋃ G : SimpleGraph (Fin n), {v : Fin n → V | sampleGraph A hsym v = G}) =
      Set.univ := by ext v; simp
  rw [← Measure.sum_fintype]
  change (Measure.sum (fun G : SimpleGraph (Fin n) =>
    (Measure.pi (fun _ : Fin n => μ)).restrict {v | sampleGraph A hsym v = G})) = _
  simpa only [hunion, Measure.restrict_univ] using
    (Measure.restrict_iUnion (μ := Measure.pi (fun _ : Fin n => μ)) hdisj
      (sampleGraph_event_measurable A hsym hA)).symm

/-- Increasing enumeration of the vertices of an actual finite clique. -/
def subsetTuple {n : ℕ} (S : Finset (Fin n)) (v : Fin n → V) : Fin S.card → V :=
  fun i => v (S.orderEmbOfFin rfl i)

theorem subsetTuple_measurable {n : ℕ} (S : Finset (Fin n)) :
    Measurable (subsetTuple (V := V) S) :=
  Measurable.of_eval (fun i => measurable_pi_apply (S.orderEmbOfFin rfl i))

/-- The exact finite-sample normalization, with both edge orientations retained. -/
def normalization (n : ℕ) : ℝ≥0 := Real.toNNReal (((n * (n - 1) : ℕ) : ℝ)⁻¹)

/-- One actual subset law averaged over every graph outcome. -/
def subsetLaw (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    Measure (Fin S.card → V) :=
  normalization n • ∑ G : SimpleGraph (Fin n),
    Real.toNNReal (w G S) • (graphEventLaw μ A hsym G).map (subsetTuple S)

instance subsetLaw_finite (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    IsFiniteMeasure (subsetLaw μ A hsym w S) := by
  unfold subsetLaw normalization
  infer_instance

/-- Keep the actual joint subset laws at their genuine orders, then average
their coordinate orders. -/
def sampledLaws (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) : Laws V :=
  fun k => symmetrize k (assemble Finset.card (subsetLaw μ A hsym w) k)

instance sampledLaws_finite (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (k : ℕ) :
    IsFiniteMeasure (sampledLaws μ A hsym w k) := by
  have := assemble_finite Finset.card (subsetLaw μ A hsym w) k
  exact symmetrize_finite _ _

theorem sampledLaws_symmetric (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    (sampledLaws μ A hsym w k).map (fun v => v ∘ σ) = sampledLaws μ A hsym w k :=
  symmetrize_invariant k _ σ

private theorem sum_subset_enumeration {n : ℕ} {M : Type*} [AddCommMonoid M]
    (S : Finset (Fin n)) (f : Fin n → M) :
    (∑ i : Fin S.card, f (S.orderEmbOfFin rfl i)) = ∑ i ∈ S, f i := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
  rw [Finset.sum_map]
  rfl

private theorem orderOccupation_subset {n : ℕ} (ρ : Measure (Fin n → V))
    (S : Finset (Fin n)) :
    orderOccupation S.card (ρ.map (subsetTuple S)) =
      ∑ i, ∑ j, if i ≠ j ∧ i ∈ S ∧ j ∈ S then
        ρ.map (fun v => (v i, v j)) else 0 := by
  classical
  rw [orderOccupation_eq_sum]
  simp_rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    (subsetTuple_measurable S)]
  change (∑ i : Fin S.card, ∑ j : Fin S.card, if i ≠ j then
    ρ.map (fun v => (v (S.orderEmbOfFin rfl i), v (S.orderEmbOfFin rfl j))) else 0) = _
  have hfirst : (∑ i : Fin S.card, ∑ j : Fin S.card, if i ≠ j then
      ρ.map (fun v => (v (S.orderEmbOfFin rfl i), v (S.orderEmbOfFin rfl j))) else 0) =
      ∑ i : Fin S.card, ∑ j ∈ S, if S.orderEmbOfFin rfl i ≠ j then
        ρ.map (fun v => (v (S.orderEmbOfFin rfl i), v j)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    convert sum_subset_enumeration S (fun j => if S.orderEmbOfFin rfl i ≠ j then
      ρ.map (fun v => (v (S.orderEmbOfFin rfl i), v j)) else 0) using 1
    simp only [(S.orderEmbOfFin rfl).injective.ne_iff]
  rw [hfirst, sum_subset_enumeration S (fun i =>
    ∑ j ∈ S, if i ≠ j then ρ.map (fun v => (v i, v j)) else 0)]
  have hind (f : Fin n → Measure (V × V)) : (∑ i ∈ S, f i) =
      ∑ i, if i ∈ S then f i else 0 := by simp
  simp_rw [hind]
  clear hind hfirst
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  · simp [hi]

private theorem subsetLaw_zero (μ : Measure V) {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (S : Finset (Fin n))
    (hzero : ∀ G, w G S = 0) : subsetLaw μ A hsym w S = 0 := by
  simp [subsetLaw, hzero]

theorem sampledLaws_zero_of_order (μ : Measure V) {n N : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hw : ∀ G, FractionalGraph.SubsetFeasible G (w G))
    (hcap : ∀ G S, w G S ≠ 0 → S.card ≤ N) (k : ℕ) (hk : k < 2 ∨ N < k) :
    sampledLaws μ A hsym w k = 0 := by
  unfold sampledLaws assemble
  have hsum : (∑ S : Finset (Fin n), singleOrder S.card (subsetLaw μ A hsym w S) k) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    by_cases hSk : S.card = k
    · have hzero : ∀ G, w G S = 0 := by
        intro G
        by_contra hz
        have hsize := (hw G).2.1 S hz
        have hN := hcap G S hz
        omega
      rw [subsetLaw_zero μ A hsym w S hzero, singleOrder_zero]
    · exact singleOrder_ne _ _ _ hSk
  rw [hsum, symmetrize_zero]

private theorem subsetLaw_absolutelyContinuous (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    subsetLaw μ A hsym w S ≪ Measure.pi (fun _ : Fin S.card => μ) := by
  unfold subsetLaw
  apply Measure.AbsolutelyContinuous.smul_left
  rw [← Measure.sum_fintype]
  apply Measure.absolutelyContinuous_sum_left
  intro G
  apply Measure.AbsolutelyContinuous.smul_left
  have h := (Measure.absolutelyContinuous_restrict
    (μ := Measure.pi (fun _ : Fin n => μ))
    (s := {v | sampleGraph A hsym v = G})).map (subsetTuple_measurable S)
  have heq := (FiniteArity.measurePreserving_subtuple μ (S.orderEmbOfFin rfl).toEmbedding).map_eq
  change (Measure.pi (fun _ : Fin n => μ)).map (subsetTuple S) = _ at heq
  rwa [heq] at h

/-- Every approximating parent law is jointly absolutely continuous with
respect to the independent product law at its own order. -/
theorem sampledLaws_absolutelyContinuous (μ : Measure V) [IsProbabilityMeasure μ]
    {n : ℕ} (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (k : ℕ) :
    sampledLaws μ A hsym w k ≪ Measure.pi (fun _ : Fin k => μ) := by
  apply symmetrize_absolutelyContinuous
  unfold assemble
  rw [← Measure.sum_fintype]
  apply Measure.absolutelyContinuous_sum_left
  intro S
  by_cases hSk : S.card = k
  · subst k
    simpa only [singleOrder_self] using subsetLaw_absolutelyContinuous μ A hsym w S
  · rw [singleOrder_ne _ _ _ hSk]
    exact Measure.AbsolutelyContinuous.zero _

omit [MeasurableSpace V] in
private theorem graph_observable_expansion {n : ℕ} (A : V → V → Bool)
    (hsym : ∀ x y, A x y = A y x) (f : SimpleGraph (Fin n) → ℝ) :
    (fun v : Fin n → V => f (sampleGraph A hsym v)) =
      (fun v => ∑ G : SimpleGraph (Fin n),
        {v : Fin n → V | sampleGraph A hsym v = G}.indicator (fun _ => f G) v) := by
  funext v
  simp only [Set.indicator_apply]
  rw [Finset.sum_eq_single (sampleGraph A hsym v)]
  · simp
  · intro G _ hG
    simp [Ne.symm hG]
  · simp

/-- Every scalar function of the finite sampled graph is a measurable bounded
observable. Its coefficients need not be chosen measurably in an LP space. -/
theorem graph_observable_integrable (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (f : SimpleGraph (Fin n) → ℝ) :
    Integrable (fun v : Fin n → V => f (sampleGraph A hsym v))
      (Measure.pi (fun _ : Fin n => μ)) := by
  rw [graph_observable_expansion A hsym f]
  exact integrable_finsetSum Finset.univ (fun G _ =>
    (integrable_const (μ := Measure.pi (fun _ : Fin n => μ)) (f G)).indicator
      (sampleGraph_event_measurable A hsym hA G))

theorem integral_graph_observable (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (f : SimpleGraph (Fin n) → ℝ) :
    (∫ v, f (sampleGraph A hsym v) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ G : SimpleGraph (Fin n), f G * (graphEventLaw μ A hsym G).real Set.univ := by
  rw [graph_observable_expansion A hsym f]
  rw [integral_finsetSum Finset.univ (fun G _ =>
    (integrable_const (μ := Measure.pi (fun _ : Fin n => μ)) (f G)).indicator
      (sampleGraph_event_measurable A hsym hA G))]
  apply Finset.sum_congr rfl
  intro G _
  rw [integral_indicator (sampleGraph_event_measurable A hsym hA G), integral_const]
  simp only [graphEventLaw, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  ring

private theorem subsetLaw_mass (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hw : ∀ G S, 0 ≤ w G S) (S : Finset (Fin n)) :
    (subsetLaw μ A hsym w S).real Set.univ =
      (normalization n : ℝ) * ∑ G : SimpleGraph (Fin n),
        w G S * (graphEventLaw μ A hsym G).real Set.univ := by
  rw [subsetLaw, measureReal_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  congr 1
  rw [Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun G _ => measure_ne_top
    (Real.toNNReal (w G S) • (graphEventLaw μ A hsym G).map (subsetTuple S)) _)]
  apply Finset.sum_congr rfl
  intro G _
  rw [Measure.smul_apply, Measure.map_apply (subsetTuple_measurable S) MeasurableSet.univ]
  simp [Real.coe_toNNReal _ (hw G S), ENNReal.smul_def, measureReal_def]

/-- The normalized cost is exactly the expected cost of the supplied actual
finite fractional partitions. This identity precedes any limiting argument. -/
theorem sampledLaws_cost (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hw : ∀ G S, 0 ≤ w G S) :
    cost (sampledLaws μ A hsym w) =
      (∫ v, ∑ S, w (sampleGraph A hsym v) S
        ∂Measure.pi (fun _ : Fin n => μ)) / ((n * (n - 1) : ℕ) : ℝ) := by
  have hraw : cost (sampledLaws μ A hsym w) =
      cost (assemble Finset.card (subsetLaw μ A hsym w)) := by
    unfold cost sampledLaws
    congr 1
    funext k
    simp only [measureReal_def, symmetrize_univ]
  rw [hraw, cost_assemble]
  simp_rw [subsetLaw_mass μ A hsym w hw]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [integral_graph_observable μ A hsym hA (fun G => ∑ S, w G S)]
  simp_rw [Finset.sum_mul]
  simp only [normalization, Real.coe_toNNReal _ (inv_nonneg.mpr (Nat.cast_nonneg _))]
  ring

private theorem orderOccupation_nnreal_smul (k : ℕ) (c : ℝ≥0)
    (ρ : Measure (Fin k → V)) : orderOccupation k (c • ρ) = c • orderOccupation k ρ := by
  simpa only [ENNReal.smul_def] using orderOccupation_smul k (c : ℝ≥0∞) ρ

private theorem pairLoad_exact {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Finset (Fin n) → ℝ) (hw : FractionalGraph.SubsetFeasible G w)
    (i j : Fin n) (hij : i ≠ j) :
    FractionalGraph.pairLoad w i j = if G.Adj i j then 1 else 0 := by
  split_ifs with hG
  · exact hw.2.2 i j hG
  · unfold FractionalGraph.pairLoad
    apply Finset.sum_eq_zero
    intro S _
    by_cases hS : i ∈ S ∧ j ∈ S
    · have hz : w S = 0 := by
        by_contra hzero
        exact hG ((hw.2.1 S hzero).2 hS.1 hS.2 hij)
      simp [hS, hz]
    · simp [hS]

private theorem weighted_subset_occupation {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Finset (Fin n) → ℝ) (hw : FractionalGraph.SubsetFeasible G w)
    (ρ : Measure (Fin n → V)) :
    (∑ S : Finset (Fin n), orderOccupation S.card
      (Real.toNNReal (w S) • ρ.map (subsetTuple S))) =
      ∑ i, ∑ j, if G.Adj i j then ρ.map (fun v => (v i, v j)) else 0 := by
  classical
  simp_rw [orderOccupation_nnreal_smul, orderOccupation_subset, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · have hcoeff : (∑ S : Finset (Fin n),
        if i ∈ S ∧ j ∈ S then Real.toNNReal (w S) else 0) =
        if G.Adj i j then (1 : ℝ≥0) else 0 := by
      have hterm (S : Finset (Fin n)) :
          (if i ∈ S ∧ j ∈ S then Real.toNNReal (w S) else 0) =
            Real.toNNReal (if i ∈ S ∧ j ∈ S then w S else 0) := by
        split_ifs <;> simp
      simp_rw [hterm]
      rw [← Real.toNNReal_sum_of_nonneg (by
        intro S _; split_ifs; exact hw.1 S; exact le_rfl)]
      change Real.toNNReal (FractionalGraph.pairLoad w i j) = _
      rw [pairLoad_exact G w hw i j hij]
      split_ifs <;> norm_num
    have hterm (S : Finset (Fin n)) :
        Real.toNNReal (w S) • (if i ≠ j ∧ i ∈ S ∧ j ∈ S then
          ρ.map (fun v => (v i, v j)) else 0) =
        (if i ∈ S ∧ j ∈ S then Real.toNNReal (w S) else 0) •
          ρ.map (fun v => (v i, v j)) := by
      split_ifs <;> simp_all
    simp_rw [hterm]
    rw [← Finset.sum_smul, hcoeff]
    split_ifs <;> simp

private theorem graphEventLaw_edge_sum (μ : Measure V) {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (i j : Fin n) (hij : i ≠ j) :
    (∑ G : SimpleGraph (Fin n), if G.Adj i j then graphEventLaw μ A hsym G else 0) =
      (Measure.pi (fun _ : Fin n => μ)).restrict {v | A (v i) (v j) = true} := by
  let E : Set (Fin n → V) := {v | A (v i) (v j) = true}
  have hE : MeasurableSet E :=
    (hA.comp (show Measurable (fun v : Fin n → V => (v i, v j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)))
        (measurableSet_singleton true)
  have hrestrict (G : SimpleGraph (Fin n)) :
      (graphEventLaw μ A hsym G).restrict E =
        if G.Adj i j then graphEventLaw μ A hsym G else 0 := by
    unfold graphEventLaw
    rw [Measure.restrict_restrict hE]
    by_cases hG : G.Adj i j
    · rw [ite_eq_left hG]
      congr 1
      ext v
      constructor
      · exact fun h => h.2
      · intro hv
        refine ⟨?_, hv⟩
        have h : (sampleGraph A hsym v).Adj i j := hv.symm ▸ hG
        exact h.2
    · rw [ite_eq_right hG]
      have he : E ∩ {v : Fin n → V | sampleGraph A hsym v = G} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have h : (sampleGraph A hsym v).Adj i j := ⟨hij, hv.1⟩
        exact hG (hv.2 ▸ h)
      rw [he, Measure.restrict_empty]
  calc
    _ = ∑ G : SimpleGraph (Fin n), (graphEventLaw μ A hsym G).restrict E := by
      simp_rw [hrestrict]
    _ = (∑ G : SimpleGraph (Fin n), graphEventLaw μ A hsym G).restrict E := by
      ext B hB
      simp [Measure.finsetSum_apply, Measure.restrict_apply hB]
    _ = _ := by rw [graphEventLaw_sum μ A hsym hA]

private theorem averaged_edge_map (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (i j : Fin n) (hij : i ≠ j) :
    (∑ G : SimpleGraph (Fin n), if G.Adj i j then
      (graphEventLaw μ A hsym G).map (fun v => (v i, v j)) else 0) =
      (μ.prod μ).restrict {p | A p.1 p.2 = true} := by
  have hf : Measurable (fun v : Fin n → V => (v i, v j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hcomm : (∑ G : SimpleGraph (Fin n),
      if G.Adj i j then graphEventLaw μ A hsym G else 0).map (fun v => (v i, v j)) =
      ∑ G : SimpleGraph (Fin n), if G.Adj i j then
        (graphEventLaw μ A hsym G).map (fun v => (v i, v j)) else 0 := by
    rw [Measure.map_finset_sum hf.aemeasurable]
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> simp
  rw [← hcomm, graphEventLaw_edge_sum μ A hsym hA i j hij]
  have hrestrict := Measure.restrict_map (μ := Measure.pi (fun _ : Fin n => μ)) hf
    (hA (measurableSet_singleton true))
  change ((Measure.pi (fun _ : Fin n => μ)).map (fun v => (v i, v j))).restrict
      {p | A p.1 p.2 = true} =
    ((Measure.pi (fun _ : Fin n => μ)).restrict {v | A (v i) (v j) = true}).map
      (fun v => (v i, v j)) at hrestrict
  rw [(FiniteArity.measurePreserving_pair μ i j hij).map_eq] at hrestrict
  exact hrestrict.symm

private theorem ordered_constant_sum (n : ℕ) (ν : Measure (V × V)) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then ν else 0) = (n * (n - 1)) • ν := by
  have hinner (i : Fin n) : (∑ j : Fin n, if i ≠ j then ν else 0) = (n - 1) • ν := by
    rw [← Finset.sum_filter, Finset.sum_const]
    have heq : (Finset.univ.filter (fun j : Fin n => i ≠ j)) = Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_fin, smul_smul]

/-- Averaging actual finite partitions gives the complete physical pair
measure exactly, on every measurable set of ordered pairs. -/
theorem sampledLaws_occupation (μ : Measure V) [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 2 ≤ n) (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hw : ∀ G, FractionalGraph.SubsetFeasible G (w G)) :
    occupation (sampledLaws μ A hsym w) =
      (μ.prod μ).restrict {p | A p.1 p.2 = true} := by
  have hraw : occupation (sampledLaws μ A hsym w) =
      ∑ S : Finset (Fin n), orderOccupation S.card (subsetLaw μ A hsym w S) := by
    unfold occupation sampledLaws
    simp_rw [orderOccupation_symmetrize]
    exact occupation_assemble Finset.card (subsetLaw μ A hsym w)
  rw [hraw]
  simp_rw [subsetLaw, orderOccupation_nnreal_smul, orderOccupation_finsetSum]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [weighted_subset_occupation _ _ (hw _)]
  have hedge : (∑ G : SimpleGraph (Fin n), ∑ i : Fin n, ∑ j : Fin n,
      if G.Adj i j then (graphEventLaw μ A hsym G).map (fun v => (v i, v j)) else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then
        (μ.prod μ).restrict {p | A p.1 p.2 = true} else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · rw [ite_eq_left hij]
      exact averaged_edge_map μ A hsym hA i j hij
  rw [hedge, ordered_constant_sum]
  have hpos : (0 : ℝ) < (n * (n - 1) : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hscalar : normalization n * (n * (n - 1) : ℕ) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simp only [normalization, NNReal.coe_mul, NNReal.coe_natCast,
      Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le), NNReal.coe_one]
    exact inv_mul_cancel₀ hpos.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul, hscalar, one_smul]

/-- The laws obtained from actual finite partitions satisfy the unrestricted
physical constraints and retain the supplied finite order cap. -/
theorem sampledLaws_feasible (μ : Measure V) [IsProbabilityMeasure μ] {n N : ℕ}
    (hn : 2 ≤ n) (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hw : ∀ G, FractionalGraph.SubsetFeasible G (w G))
    (hcap : ∀ G S, w G S ≠ 0 → S.card ≤ N) :
    Feasible (fun x y => A x y = true)
      ((μ.prod μ).restrict {p | A p.1 p.2 = true}) (sampledLaws μ A hsym w) := by
  have hbalance := sampledLaws_occupation μ hn A hsym hA w hw
  refine ⟨sampledLaws_zero_of_order μ A hsym w hw hcap 0 (Or.inl (by omega)),
    sampledLaws_zero_of_order μ A hsym w hw hcap 1 (Or.inl (by omega)), ?_, hbalance⟩
  intro k
  exact ae_all_pairs_of_balance (sampledLaws μ A hsym w)
    ((μ.prod μ).restrict {p | A p.1 p.2 = true}) hbalance
    (fun p => A p.1 p.2 = true) (ae_restrict_mem (hA (measurableSet_singleton true))) k

/-- Independent physical sampling on an atomless carrier yields actual
distinct vertices, even though the finite graph uses only distinct labels. -/
theorem sampledLaws_distinct [MeasurableEq V] (μ : Measure V)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {n : ℕ}
    (A : V → V → Bool) (hsym : ∀ x y, A x y = A y x)
    (w : SimpleGraph (Fin n) → Finset (Fin n) → ℝ) (k : ℕ) :
    ∀ᵐ v ∂sampledLaws μ A hsym w k, Function.Injective v := by
  have hdiag : (μ.prod μ) (Set.diagonal V) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    have hpre (x : V) : Prod.mk x ⁻¹' Set.diagonal V = {x} := by
      ext y
      simp [Set.diagonal, eq_comm]
    simp_rw [hpre, measure_singleton]
    simp
  have hp : ∀ᵐ p : V × V ∂μ.prod μ, p.1 ≠ p.2 := by
    simpa only [ae_iff, not_not, Set.diagonal] using hdiag
  have htuples := FiniteArity.ae_all_pairs μ k (fun p => p.1 ≠ p.2) hp
  have htuples' : ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ), Function.Injective v := by
    filter_upwards [htuples] with v hv
    intro i j hij
    by_contra hne
    exact hv i j hne hij
  exact (sampledLaws_absolutelyContinuous μ A hsym w k).ae_le htuples'

end Erdos1017.PhysicalPrimalSampling
