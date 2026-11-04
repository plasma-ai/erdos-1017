module

public import Erdos1017.Multipartite.Physical.PhysicalPairRepair

/-!
# Transporting joint laws along a vertex map

Applying one measurable vertex map to every coordinate of every joint law
preserves exact ordered pair balance, cost and support, so feasibility is
transported (`mapLaws_feasible`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalPrimal

open MeasureTheory

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

/-- Apply one measurable vertex map to every coordinate of every genuine joint law. -/
def mapLaws (f : V → W) (μ : Laws V) : Laws W :=
  fun n => (μ n).map (fun v => f ∘ v)

theorem tupleMap_measurable {f : V → W} (hf : Measurable f) (n : ℕ) :
    Measurable (fun v : Fin n → V => f ∘ v) :=
  Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i))

theorem mapLaws_finite (f : V → W) (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)] (n : ℕ) :
    IsFiniteMeasure (mapLaws f μ n) := Measure.isFiniteMeasure_map _ _

theorem orderOccupation_map {f : V → W} (hf : Measurable f) (n : ℕ)
    (ρ : Measure (Fin n → V)) :
    orderOccupation n (ρ.map (fun v => f ∘ v)) = (orderOccupation n ρ).map (Prod.map f f) := by
  unfold orderOccupation
  rw [Measure.map_finset_sum (hf.prodMap hf).aemeasurable]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
      (tupleMap_measurable hf n), Measure.map_map (hf.prodMap hf)
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))]
  rfl

/-- Exact ordered pair balance is preserved under a common measurable vertex map. -/
theorem occupation_mapLaws {f : V → W} (hf : Measurable f) (μ : Laws V) :
    occupation (mapLaws f μ) = (occupation μ).map (Prod.map f f) := by
  unfold occupation mapLaws
  simp_rw [orderOccupation_map hf]
  exact (Measure.map_sum (hf.prodMap hf).aemeasurable).symm

theorem cost_mapLaws {f : V → W} (hf : Measurable f) (μ : Laws V) :
    cost (mapLaws f μ) = cost μ := by
  unfold cost mapLaws
  congr 1
  funext n
  simp [measureReal_def, Measure.map_apply (tupleMap_measurable hf n)]

/-- Support transport is proved under each original law, including singular laws. -/
theorem mapLaws_feasible {f : V → W} (hf : Measurable f) (μ : Laws V)
    (A : V → V → Prop) (B : W → W → Prop) (demand : Measure (V × V))
    (hμ : Feasible A demand μ) (hB : MeasurableSet {z : W × W | B z.1 z.2})
    (hAB : ∀ x y, A x y → B (f x) (f y)) :
    Feasible B (demand.map (Prod.map f f)) (mapLaws f μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mapLaws, hμ.1]
  · simp [mapLaws, hμ.2.1]
  · intro n
    apply (ae_map_iff (tupleMap_measurable hf n).aemeasurable ?_).mpr
    · filter_upwards [hμ.2.2.1 n] with v hv
      exact fun i j hij => hAB _ _ (hv i j hij)
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun _ => hB.preimage
          (show Measurable (fun v : Fin n → W => (v i, v j)) from
            (measurable_pi_apply i).prodMk (measurable_pi_apply j))
  · rw [occupation_mapLaws hf, hμ.2.2.2]

end Erdos1017.PhysicalPrimal
