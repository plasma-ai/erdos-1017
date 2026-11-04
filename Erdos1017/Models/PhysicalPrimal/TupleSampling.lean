module

public import Erdos1017.Models.PhysicalPrimal.FiniteArityParameters
public import Mathlib.Data.Finset.Sort

/-!
# Subtuples of independent samples

Injective coordinate selection preserves the independent product sampling law,
so bounded-order subtuple tests hold simultaneously on almost every larger
sample, capped clique tests cover every subset of almost every larger clique,
and root sections and distinct pairs inherit the product laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Injective coordinate selection preserves the independent product sampling law. -/
theorem measurePreserving_subtuple {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ↪ κ) :
    MeasurePreserving (fun v : κ → Ω => fun i => v (e i))
      (Measure.pi (fun _ : κ => μ)) (Measure.pi (fun _ : ι => μ)) := by
  have hind : iIndepFun (fun i (v : κ → Ω) => v i) (Measure.pi (fun _ : κ => μ)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hind' := hind.precomp e.injective
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply (e i)), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable) hind']
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : κ => μ) (e i)).map_eq

/-- Every bounded-order subtuple test holds simultaneously on almost every
larger independent sample, even when the subtuple is selected after sampling. -/
theorem ae_all_subtuples (N n : ℕ) (P : ∀ r : ℕ, (Fin r → Ω) → Prop)
    (hP : ∀ r, r ≤ N → ∀ᵐ v ∂Measure.pi (fun _ : Fin r => μ), P r v) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      ∀ r, r ≤ N → ∀ e : Fin r ↪ Fin n, P r (fun i => v (e i)) := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro hr
  apply ae_all_iff.mpr
  intro e
  exact (measurePreserving_subtuple μ e).quasiMeasurePreserving.ae (hP r hr)

/-- Clique membership for an ordered physical sample. -/
def TupleClique {n : ℕ} (A : Ω → Ω → Bool) (v : Fin n → Ω) : Prop :=
  ∀ i j, i ≠ j → A (v i) (v j) = true

/-- Diagonal-free charge of an ordered physical sample. -/
def tupleCharge {n : ℕ} (Y : Ω → Ω → ℝ) (v : Fin n → Ω) : ℝ :=
  pairCharge Finset.univ (fun i j => if i = j then 0 else Y (v i) (v j))

/-- The physical clique test at one order, with its precise product-null quantifier. -/
def FeasibleOrder (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (n : ℕ) : Prop :=
  ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v → tupleCharge Y v ≤ 1

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
theorem tupleCharge_small {n : ℕ} (hn : n ≤ 1) (Y : Ω → Ω → ℝ) (v : Fin n → Ω) :
    tupleCharge Y v = 0 := by
  unfold tupleCharge
  rw [pairCharge_eq_sum_pairs _ _ (by intro i; simp)]
  have he : (Finset.univ : Finset (Fin n)).powersetCard 2 = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using (show n < 2 by omega))
  rw [he, Finset.sum_empty]

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
theorem TupleClique.subtuple {n r : ℕ} {A : Ω → Ω → Bool} {v : Fin n → Ω}
    (hv : TupleClique A v) (e : Fin r ↪ Fin n) : TupleClique A (fun i => v (e i)) := by
  intro i j hij
  exact hv (e i) (e j) (fun heq => hij (e.injective heq))

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
theorem tupleCharge_subtuple {n r : ℕ} (Y : Ω → Ω → ℝ) (v : Fin n → Ω) (e : Fin r ↪ Fin n) :
    tupleCharge Y (fun i => v (e i)) =
      pairCharge (Finset.univ.map e) (fun i j => if i = j then 0 else Y (v i) (v j)) := by
  rw [pairCharge_map]
  unfold tupleCharge
  congr 1
  funext i j
  simp only [e.injective.eq_iff]

/-- Capped clique tests license every subset of almost every larger clique. -/
theorem ae_small_subsets (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (N n : ℕ)
    (hcap : ∀ r, 2 ≤ r → r ≤ N → FeasibleOrder μ A Y r) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), TupleClique A v →
      ∀ S : Finset (Fin n), S.card ≤ N →
        pairCharge S (fun i j => if i = j then 0 else Y (v i) (v j)) ≤ 1 := by
  have htests : ∀ r, r ≤ N → ∀ᵐ v ∂Measure.pi (fun _ : Fin r => μ),
      TupleClique A v → tupleCharge Y v ≤ 1 := by
    intro r hr
    by_cases h2 : 2 ≤ r
    · exact hcap r h2 hr
    · exact Filter.Eventually.of_forall (fun v _ => by
        rw [tupleCharge_small (by omega) Y v]
        norm_num)
  have hsub := ae_all_subtuples μ N n (fun r v => TupleClique A v → tupleCharge Y v ≤ 1) htests
  filter_upwards [hsub] with v hv hclique S hS
  let e := (S.orderEmbOfFin rfl).toEmbedding
  have ht := hv S.card hS e (hclique.subtuple e)
  rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ S rfl] at ht
  exact ht

/-- Splitting one coordinate off an independent sample licenses almost every root section. -/
theorem ae_root_sections (k : ℕ) (P : (Fin (k + 1) → Ω) → Prop)
    (hP : ∀ᵐ v ∂Measure.pi (fun _ : Fin (k + 1) => μ), P v) :
    ∀ᵐ x ∂μ, ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ), P (Fin.cons x v) := by
  have hmp := MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Ω) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0)
  have hp := hmp.quasiMeasurePreserving.ae hP
  have hcons : ∀ᵐ p ∂μ.prod (Measure.pi (fun _ : Fin k => μ)), P (Fin.cons p.1 p.2) := by
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hp
  exact Measure.ae_ae_of_ae_prod hcons

/-- Distinct coordinates have exactly the physical product-pair law. -/
theorem measurePreserving_pair {ι : Type*} [Fintype ι] (i j : ι) (hij : i ≠ j) :
    MeasurePreserving (fun v : ι → Ω => (v i, v j))
      (Measure.pi (fun _ : ι => μ)) (μ.prod μ) := by
  have hind : iIndepFun (fun i (v : ι → Ω) => v i) (Measure.pi (fun _ : ι => μ)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun _ : ι => μ) i).map_eq,
    (measurePreserving_eval (fun _ : ι => μ) j).map_eq]

/-- One physical pair-null set is avoided simultaneously by all distinct sample coordinates. -/
theorem ae_all_pairs (n : ℕ) (P : Ω × Ω → Prop) (hP : ∀ᵐ z ∂μ.prod μ, P z) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i j, i ≠ j → P (v i, v j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro hij
  exact (measurePreserving_pair μ i j hij).quasiMeasurePreserving.ae hP

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
theorem TupleClique.cons {n : ℕ} {A : Ω → Ω → Bool} {v : Fin n → Ω} (x : Ω)
    (hv : TupleClique A v) (hl : ∀ i, A x (v i) = true) (hr : ∀ i, A (v i) x = true) :
    TupleClique A (Fin.cons x v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => simpa using hl j
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa using hr i
    | succ j =>
      exact hv i j (fun h => hij (congrArg Fin.succ h))

omit [IsProbabilityMeasure μ] [MeasurableSpace Ω] in
theorem tupleCharge_cons {n : ℕ} (Y : Ω → Ω → ℝ) (x : Ω) (v : Fin n → Ω)
    (hsym : ∀ i, Y (v i) x = Y x (v i)) :
    tupleCharge Y (Fin.cons x v) = (∑ i, Y x (v i)) + tupleCharge Y v := by
  have hzero (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  unfold tupleCharge pairCharge crossSum
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hzero,
    Fin.succ_ne_zero, Fin.succ_inj, ite_true, ite_false, zero_add]
  simp only [hsym, Finset.sum_add_distrib]
  ring

end Erdos1017.FiniteArity
