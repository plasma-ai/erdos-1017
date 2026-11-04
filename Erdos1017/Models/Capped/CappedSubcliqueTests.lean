module

public import Erdos1017.Models.Capped.CappedModel
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Subclique tests on one sampled configuration

Injectively selecting coordinates of a finite product law gives the selected
product law, a selected subclique keeps its conditionally independent color law
and pair orientations, and all capped subclique tests hold on one common sampled
configuration, including subcliques chosen after observing its colors.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Injectively selecting coordinates of a finite product of possibly
different probability laws gives their exact selected product law. -/
theorem measurePreserving_select {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ρ : κ → Measure C) [∀ i, IsProbabilityMeasure (ρ i)] (e : ι ↪ κ) :
    MeasurePreserving (fun c : κ → C => fun i => c (e i))
      (Measure.pi ρ) (Measure.pi (fun i => ρ (e i))) := by
  have hind : iIndepFun (fun i (c : κ → C) => c i) (Measure.pi ρ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have he := hind.precomp e.injective
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply (e i)), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable) he]
  congr 1
  funext i
  exact (measurePreserving_eval ρ (e i)).map_eq

/-- Increasing vertex embeddings preserve the chosen orientation of every
unordered pair. -/
def pairEmbedding {k n : ℕ} (e : Fin k ↪o Fin n) : CliquePair k ↪ CliquePair n where
  toFun p := ⟨(e p.val.1, e p.val.2), e.strictMono p.property⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext (e.injective (congrArg (fun p : CliquePair n => p.val.1) hpq))
      (e.injective (congrArg (fun p : CliquePair n => p.val.2) hpq))

omit [IsProbabilityMeasure μ] in
/-- A selected subclique has exactly its old conditionally independent
color law, without changing pair orientations or adding randomness. -/
theorem measurePreserving_cliqueRestriction (W : Model Ω μ) {n k : ℕ}
    (x : Fin n → Ω) (e : Fin k ↪o Fin n) :
    MeasurePreserving (fun c : CliquePair n → CappedColor =>
      fun p => c (pairEmbedding e p)) (cliqueLaw W x) (cliqueLaw W (fun i => x (e i))) :=
  measurePreserving_select (fun p : CliquePair n => W.kernel (x p.val.1, x p.val.2))
    (pairEmbedding e)

/-- All capped subclique tests hold on one common sampled colored
configuration, including subcliques chosen after observing its colors. -/
theorem ae_all_subclique_tests (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ᵐ c ∂cliqueLaw W x,
      ∀ k, 2 ≤ k → k ≤ r → ∀ e : Fin k ↪o Fin n,
        violation (fun p => c (pairEmbedding e p)) = 0 := by
  simp only [ae_all_iff]
  intro k hk hkr e
  have hv := (FiniteArity.measurePreserving_subtuple μ e.toEmbedding).quasiMeasurePreserving.ae
    (hW k hk hkr)
  filter_upwards [hv] with x hx
  exact (measurePreserving_cliqueRestriction W x e).quasiMeasurePreserving.ae hx

end Erdos1017.CappedModel
