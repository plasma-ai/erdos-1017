module

public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalOccupation
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalBalancedSupport
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalRootLeaves
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Independent replacement of a class root

Independent replacement of a homogeneous-class root in physical parent laws.
Pair and coordinate absolute continuity suffice; the original joint parent laws
may be singular.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalRootReplacement

open PhysicalPrimal

variable {Ω C : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual uniform probability law inside a positive-mass physical class. -/
def rootLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω) (hI0 : μ I ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨PhysicalCliqueRepresentative.cellLaw μ I,
    PhysicalCliqueRepresentative.cellLaw_probability μ I hI0⟩

/-- Restrict the actual parent law to roots in the chosen coordinate. -/
def rootedLaw {n : ℕ} (ρ : Measure (Fin n → Ω)) (I : Set Ω) (i : Fin n) :
    Measure (Fin n → Ω) := ρ.restrict {v | v i ∈ I}

instance rootedLaw_finite {n : ℕ} (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (I : Set Ω) (i : Fin n) : IsFiniteMeasure (rootedLaw ρ I i) := by
  unfold rootedLaw
  infer_instance

/-- The explicit independent coupling retains every old coordinate. -/
def coupling {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) (i : Fin n) : Measure (Ω × (Fin n → Ω)) :=
  (rootLaw μ I hI0 : Measure Ω).prod (rootedLaw ρ I i)

instance coupling_finite {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Set Ω) (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i : Fin n) :
    IsFiniteMeasure (coupling μ I hI0 ρ i) := by
  unfold coupling
  infer_instance

/-- Replace exactly the marked old root by the independently sampled point. -/
def replaceTuple {n : ℕ} (i : Fin n) (p : Ω × (Fin n → Ω)) : Fin n → Ω :=
  Function.update p.2 i p.1

theorem measurable_replaceTuple {n : ℕ} (i : Fin n) : Measurable (replaceTuple (Ω := Ω) i) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa only [replaceTuple, Function.update_self] using
      (measurable_fst : Measurable (Prod.fst : Ω × (Fin n → Ω) → Ω))
  · have heq : (fun p : Ω × (Fin n → Ω) => replaceTuple i p j) = fun p => p.2 j := by
      funext p
      exact Function.update_of_ne h _ _
    rw [heq]
    exact (measurable_pi_apply j).comp measurable_snd

/-- The genuine marked-root replacement law. -/
def replacedLaw {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) (i : Fin n) : Measure (Fin n → Ω) :=
  (coupling μ I hI0 ρ i).map (replaceTuple i)

instance replacedLaw_finite {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Set Ω) (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i : Fin n) :
    IsFiniteMeasure (replacedLaw μ I hI0 ρ i) := by
  unfold replacedLaw
  infer_instance

/-- Independent root replacement changes no marked-parent mass. -/
theorem replacedLaw_mass {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i : Fin n) :
    replacedLaw μ I hI0 ρ i univ = ρ {v | v i ∈ I} := by
  rw [replacedLaw, Measure.map_apply (measurable_replaceTuple i) MeasurableSet.univ]
  simp only [preimage_univ, coupling]
  rw [← univ_prod_univ, Measure.prod_prod]
  simp only [measure_univ, one_mul, rootedLaw, Measure.restrict_apply_univ]

/-- Both directed rows are homogeneous on the original physical class. -/
def HomogeneousRows (μ : Measure Ω) (I : Set Ω) (R : Ω × Ω → C) (row : Ω → C) : Prop :=
  ∀ᵐ p ∂(μ.restrict I).prod μ, R (p.1, p.2) = row p.2 ∧ R (p.2, p.1) = row p.2

/-- An original homogeneous outgoing row and product-almost-everywhere
symmetry give both directed homogeneous rows needed by replacement. -/
theorem homogeneousRows_of_row (I : Set Ω) (R : Ω × Ω → C) (row : Ω → C)
    (hrow : ∀ᵐ p ∂(μ.restrict I).prod μ, R (p.1, p.2) = row p.2)
    (hsym : ∀ᵐ p ∂μ.prod μ, R (p.1, p.2) = R (p.2, p.1)) :
    HomogeneousRows μ I R row := by
  have hac : (μ.restrict I).prod μ ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict.prod Measure.AbsolutelyContinuous.rfl
  filter_upwards [hrow, hac.ae_le hsym] with p hp hsym
  exact ⟨hp, hsym.symm.trans hp⟩

private theorem homogeneous_rows_imp (I : Set Ω) (hI : MeasurableSet I)
    (R : Ω × Ω → C) (row : Ω → C) (hrow : HomogeneousRows μ I R row) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → R (p.1, p.2) = row p.2 ∧ R (p.2, p.1) = row p.2 := by
  have hrestrict : ∀ᵐ p ∂(μ.prod μ).restrict (I ×ˢ univ),
      R (p.1, p.2) = row p.2 ∧ R (p.2, p.1) = row p.2 := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hrow
  have h := (ae_restrict_iff' (hI.prod MeasurableSet.univ)).mp hrestrict
  filter_upwards [h] with p hp hi
  exact hp ⟨hi, mem_univ _⟩

private theorem original_rows_ae {n : ℕ} (I : Set Ω) (hI : MeasurableSet I)
    (ρ : Measure (Fin n → Ω))
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i j : Fin n) (hij : i ≠ j) (R : Ω × Ω → C) (row : Ω → C)
    (hrow : HomogeneousRows μ I R row) :
    ∀ᵐ v ∂rootedLaw ρ I i, R (v i, v j) = row (v j) ∧ R (v j, v i) = row (v j) := by
  have hr := (hpair i j hij).ae_le (homogeneous_rows_imp I hI R row hrow)
  have hp := ae_of_ae_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hr
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem ((measurable_pi_apply i) hI)] with v hv hi
  exact hv hi

private theorem rooted_coordinate_absolutelyContinuous {n : ℕ} (hn : 2 ≤ n)
    (I : Set Ω) (ρ : Measure (Fin n → Ω))
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ) (i j : Fin n) :
    (rootedLaw ρ I i).map (fun v => v j) ≪ μ := by
  exact ((Measure.absolutelyContinuous_restrict (μ := ρ) (s := {v | v i ∈ I})).map
    (measurable_pi_apply j)).trans
      (PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs μ hn ρ hpair j)

private theorem fresh_rows_ae {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i j : Fin n) (R : Ω × Ω → C) (row : Ω → C) (hrow : HomogeneousRows μ I R row) :
    ∀ᵐ p ∂coupling μ I hI0 ρ i,
      R (p.1, p.2 j) = row (p.2 j) ∧ R (p.2 j, p.1) = row (p.2 j) := by
  have hroot : (rootLaw μ I hI0 : Measure Ω) ≪ μ.restrict I :=
    (Measure.AbsolutelyContinuous.rfl).smul_left ((μ I)⁻¹)
  have hcoord := rooted_coordinate_absolutelyContinuous hn I ρ hpair i j
  have hmap : (coupling μ I hI0 ρ i).map (fun p => (p.1, p.2 j)) =
      (rootLaw μ I hI0 : Measure Ω).prod ((rootedLaw ρ I i).map (fun v => v j)) := by
    have h := Measure.map_prod_map (rootLaw μ I hI0 : Measure Ω) (rootedLaw ρ I i)
      measurable_id (measurable_pi_apply j)
    have heq : Prod.map (id : Ω → Ω) (fun v : Fin n → Ω => v j) =
        (fun p : Ω × (Fin n → Ω) => (p.1, p.2 j)) := by
      funext p
      rfl
    rw [Measure.map_id, heq] at h
    exact h.symm
  have hpair' : (coupling μ I hI0 ρ i).map (fun p => (p.1, p.2 j)) ≪ (μ.restrict I).prod μ := by
    rw [hmap]
    exact hroot.prod hcoord
  exact ae_of_ae_map (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)).aemeasurable
    (hpair'.ae_le hrow)

/-- Every distinct pair retains both its adjacency and its charge in this
explicit independent coupling. Homogeneity is used only on the actual class
and pair laws; no joint density of the original parent is assumed. -/
theorem ae_pairs_preserved {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i : Fin n) (R : Ω × Ω → C) (row : Ω → C) (hrow : HomogeneousRows μ I R row) :
    ∀ᵐ p ∂coupling μ I hI0 ρ i, ∀ a b, a ≠ b →
      R (replaceTuple i p a, replaceTuple i p b) = R (p.2 a, p.2 b) := by
  have hold : ∀ j : Fin n, ∀ᵐ p ∂coupling μ I hI0 ρ i,
      i ≠ j → R (p.2 i, p.2 j) = row (p.2 j) ∧ R (p.2 j, p.2 i) = row (p.2 j) := by
    intro j
    have hr : ∀ᵐ v ∂rootedLaw ρ I i,
        i ≠ j → R (v i, v j) = row (v j) ∧ R (v j, v i) = row (v j) := by
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
      · exact (original_rows_ae I hI ρ hpair i j hij R row hrow).mono (fun _ h _ => h)
    exact (measurePreserving_snd (μ := (rootLaw μ I hI0 : Measure Ω))
      (ν := rootedLaw ρ I i)).quasiMeasurePreserving.ae hr
  have hnew : ∀ j : Fin n, ∀ᵐ p ∂coupling μ I hI0 ρ i,
      R (p.1, p.2 j) = row (p.2 j) ∧ R (p.2 j, p.1) = row (p.2 j) :=
    fun j => fresh_rows_ae hn I hI0 ρ hpair i j R row hrow
  filter_upwards [ae_all_iff.mpr hold, ae_all_iff.mpr hnew] with p hold hnew
  intro a b hab
  by_cases ha : a = i
  · subst a
    have hb : b ≠ i := Ne.symm hab
    simp only [replaceTuple, Function.update_self, Function.update_of_ne hb]
    exact (hnew b).1.trans (hold b hab).1.symm
  · by_cases hb : b = i
    · subst b
      simp only [replaceTuple, Function.update_self, Function.update_of_ne ha]
      exact (hnew a).2.trans (hold a (Ne.symm hab)).2.symm
    · simp only [replaceTuple, Function.update_of_ne ha, Function.update_of_ne hb]

/-- Exact pair balance supplies the only absolute-continuity hypotheses
needed for the actual independent root replacement. -/
theorem ae_pairs_preserved_of_balance {n : ℕ} (hn : 2 ≤ n)
    (η : Laws Ω) [∀ k, IsFiniteMeasure (η k)] (E : Set (Ω × Ω))
    (hbalance : occupation η = graphDemand μ E)
    (J : Set Ω) (hJ : MeasurableSet J) (hJ0 : μ J ≠ 0)
    (i : Fin n) (R : Ω × Ω → C) (row : Ω → C) (hrow : HomogeneousRows μ J R row) :
    ∀ᵐ p ∂coupling μ J hJ0 (η n) i, ∀ a b, a ≠ b →
      R (replaceTuple i p a, replaceTuple i p b) = R (p.2 a, p.2 b) := by
  apply ae_pairs_preserved hn J hJ hJ0 (η n) _ i R row hrow
  intro a b hab
  exact (pair_marginal_absolutelyContinuous_of_balance η _ hbalance n ⟨(a, b), hab⟩).trans
    Measure.absolutelyContinuous_restrict

private theorem measurableSet_clique (A : Ω × Ω → Bool) (hA : Measurable A) (n : ℕ) :
    MeasurableSet {v : Fin n → Ω | PhysicalCliqueRepresentative.Clique A v} := by
  simp only [PhysicalCliqueRepresentative.Clique, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hij
  exact (hA.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)))
    (measurableSet_singleton true)

private theorem measurable_charge (Y : Ω × Ω → ℝ) (hY : Measurable Y) (n : ℕ) :
    Measurable (PhysicalPrimal.charge Y (n := n)) := by
  unfold PhysicalPrimal.charge
  exact (Finset.measurable_sum _ (fun ij _ =>
    hY.comp ((measurable_pi_apply ij.val.1).prodMk (measurable_pi_apply ij.val.2)))).div_const 2

/-- The replaced marked-root law remains on actual physical cliques. -/
theorem replacedLaw_clique {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i : Fin n) (A : Ω × Ω → Bool) (hA : Measurable A) (row : Ω → Bool)
    (hrow : HomogeneousRows μ I A row)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique A v) :
    ∀ᵐ v ∂replacedLaw μ I hI0 ρ i, PhysicalCliqueRepresentative.Clique A v := by
  apply (ae_map_iff (measurable_replaceTuple i).aemeasurable (measurableSet_clique A hA n)).mpr
  have hold : ∀ᵐ p ∂coupling μ I hI0 ρ i, PhysicalCliqueRepresentative.Clique A p.2 :=
    (measurePreserving_snd (μ := (rootLaw μ I hI0 : Measure Ω))
      (ν := rootedLaw ρ I i)).quasiMeasurePreserving.ae (ae_restrict_of_ae hclique)
  filter_upwards [hold, ae_pairs_preserved hn I hI hI0 ρ hpair i A row hrow] with p hp hpair'
  intro a b hab
  exact (hpair' a b hab).trans (hp a b hab)

/-- The original and replaced marked parent have exactly the same charge
in the explicit independent coupling, not merely the same expected charge. -/
theorem ae_charge_preserved {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i : Fin n) (Y : Ω × Ω → ℝ) (row : Ω → ℝ) (hrow : HomogeneousRows μ I Y row) :
    ∀ᵐ p ∂coupling μ I hI0 ρ i,
      PhysicalPrimal.charge Y (replaceTuple i p) = PhysicalPrimal.charge Y p.2 := by
  filter_upwards [ae_pairs_preserved hn I hI hI0 ρ hpair i Y row hrow] with p hp
  unfold PhysicalPrimal.charge
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  exact hp ij.val.1 ij.val.2 ij.property

/-- Independent replacement preserves the entire distribution of the
marked parent's actual charge. -/
theorem replacedLaw_charge_map {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i : Fin n) (Y : Ω × Ω → ℝ) (hY : Measurable Y) (row : Ω → ℝ)
    (hrow : HomogeneousRows μ I Y row) :
    (replacedLaw μ I hI0 ρ i).map (PhysicalPrimal.charge Y) =
      (rootedLaw ρ I i).map (PhysicalPrimal.charge Y) := by
  rw [replacedLaw, Measure.map_map (measurable_charge Y hY n) (measurable_replaceTuple i)]
  have heq : (coupling μ I hI0 ρ i).map (fun p => PhysicalPrimal.charge Y (replaceTuple i p)) =
      (coupling μ I hI0 ρ i).map (fun p => PhysicalPrimal.charge Y p.2) :=
    Measure.map_congr (ae_charge_preserved hn I hI hI0 ρ hpair i Y row hrow)
  change (coupling μ I hI0 ρ i).map (fun p => PhysicalPrimal.charge Y (replaceTuple i p)) = _
  rw [heq]
  change (coupling μ I hI0 ρ i).map ((PhysicalPrimal.charge Y) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_charge Y hY n) measurable_snd, coupling,
    (measurePreserving_snd (μ := (rootLaw μ I hI0 : Measure Ω))
      (ν := rootedLaw ρ I i)).map_eq]

/-- Tight marked parents remain tight under the actual replacement law. -/
theorem replacedLaw_tight {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (i : Fin n) (Y : Ω × Ω → ℝ) (hY : Measurable Y) (row : Ω → ℝ)
    (hrow : HomogeneousRows μ I Y row)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge Y v = 1) :
    ∀ᵐ v ∂replacedLaw μ I hI0 ρ i, PhysicalPrimal.charge Y v = 1 := by
  apply (ae_map_iff (measurable_replaceTuple i).aemeasurable
    ((measurable_charge Y hY n) (measurableSet_singleton 1))).mpr
  have hold : ∀ᵐ p ∂coupling μ I hI0 ρ i, PhysicalPrimal.charge Y p.2 = 1 :=
    (measurePreserving_snd (μ := (rootLaw μ I hI0 : Measure Ω))
      (ν := rootedLaw ρ I i)).quasiMeasurePreserving.ae (ae_restrict_of_ae htight)
  filter_upwards [hold, ae_charge_preserved hn I hI hI0 ρ hpair i Y row hrow] with p hp hcharge
  exact hcharge.trans hp

/-- Retain the original parents with no point in the root class. -/
def noRootLaw {n : ℕ} (ρ : Measure (Fin n → Ω)) (I : Set Ω) : Measure (Fin n → Ω) :=
  ρ.restrict {v | ∀ i, v i ∉ I}

instance noRootLaw_finite {n : ℕ} (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (I : Set Ω) : IsFiniteMeasure (noRootLaw ρ I) := by
  unfold noRootLaw
  infer_instance

/-- Replace the unique class root wherever it occurs, retaining no-root parents. -/
def replacedAllLaw {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) : Measure (Fin n → Ω) :=
  noRootLaw ρ I + ∑ i : Fin n, replacedLaw μ I hI0 ρ i

instance replacedAllLaw_finite {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Set Ω) (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (replacedAllLaw μ I hI0 ρ) := by
  unfold replacedAllLaw
  infer_instance

/-- At most one root partitions the actual parent law into its no-root
restriction and the restrictions at its genuine root coordinates. -/
theorem rootedLaw_decomposition {n : ℕ} (I : Set Ω) (hI : MeasurableSet I)
    (ρ : Measure (Fin n → Ω))
    (hunique : ∀ᵐ v ∂ρ, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    noRootLaw ρ I + ∑ i : Fin n, rootedLaw ρ I i = ρ := by
  let S : Fin n → Set (Fin n → Ω) := fun i => {v | v i ∈ I}
  have hS (i : Fin n) : MeasurableSet (S i) := (measurable_pi_apply i) hI
  have hd : Pairwise (fun i j => AEDisjoint ρ (S i) (S j)) := by
    intro i j hij
    have hnot : ∀ᵐ v ∂ρ, ¬(v i ∈ I ∧ v j ∈ I) := by
      filter_upwards [hunique] with v hv h
      exact hij (hv i j h.1 h.2)
    change ρ {v | v i ∈ I ∧ v j ∈ I} = 0
    simpa only [ae_iff, not_not] using hnot
  have hcomp : (⋃ i, S i)ᶜ = {v | ∀ i, v i ∉ I} := by
    ext v
    simp only [mem_compl_iff, mem_iUnion, not_exists, S, mem_ofPred_eq]
  have h := Measure.restrict_compl_add_restrict (μ := ρ) (MeasurableSet.iUnion hS)
  rw [hcomp, Measure.restrict_iUnion_ae hd (fun i => (hS i).nullMeasurableSet),
    Measure.sum_fintype] at h
  exact h

/-- Reassembling the actual independent root replacements preserves the
entire parent mass, using uniqueness rather than a normalization assumption. -/
theorem replacedAllLaw_mass {n : ℕ} (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hunique : ∀ᵐ v ∂ρ, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    replacedAllLaw μ I hI0 ρ univ = ρ univ := by
  have h := congrArg (fun ν : Measure (Fin n → Ω) => ν univ)
    (rootedLaw_decomposition I hI ρ hunique)
  simp only [replacedAllLaw, Measure.add_apply, Measure.finsetSum_apply] at h ⊢
  simp only [replacedLaw_mass, rootedLaw, Measure.restrict_apply_univ] at h ⊢
  exact h

/-- Apply the actual root replacement separately at every original order. -/
def replacedLaws (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω) (hI0 : μ I ≠ 0)
    (η : Laws Ω) : Laws Ω := fun n => replacedAllLaw μ I hI0 (η n)

instance replacedLaws_finite (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set Ω)
    (hI0 : μ I ≠ 0) (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (n : ℕ) :
    IsFiniteMeasure (replacedLaws μ I hI0 η n) := by
  unfold replacedLaws
  infer_instance

/-- The physical objective counts parent masses, which are preserved at
every order by the actual independent class-root replacement. -/
theorem replacedLaws_cost (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    cost (replacedLaws μ I hI0 η) = cost η := by
  unfold cost
  apply tsum_congr
  intro n
  simp only [replacedLaws, measureReal_def, replacedAllLaw_mass I hI hI0 (η n) (hunique n)]

/-- Zero parent laws stay zero under the actual replacement operation. -/
theorem replacedAllLaw_zero {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0) :
    replacedAllLaw μ I hI0 (0 : Measure (Fin n → Ω)) = 0 := by
  simp only [replacedAllLaw, noRootLaw, rootedLaw, Measure.restrict_zero,
    replacedLaw, coupling, Measure.prod_zero, Measure.map_zero, Finset.sum_const_zero, add_zero]

/-- The actual replacement retains every original order cutoff. -/
theorem replacedLaws_zero_of_order (I : Set Ω) (hI0 : μ I ≠ 0) (η : Laws Ω)
    (n : ℕ) (hn : η n = 0) : replacedLaws μ I hI0 η n = 0 := by
  rw [replacedLaws, hn]
  exact replacedAllLaw_zero I hI0

/-- Reassembling over the actual root indices preserves physical clique support. -/
theorem replacedAllLaw_clique {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (A : Ω × Ω → Bool) (hA : Measurable A) (row : Ω → Bool)
    (hrow : HomogeneousRows μ I A row)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique A v) :
    ∀ᵐ v ∂replacedAllLaw μ I hI0 ρ, PhysicalCliqueRepresentative.Clique A v := by
  rw [replacedAllLaw, ae_add_measure_iff, ← Measure.sum_fintype, Measure.ae_sum_iff]
  exact ⟨ae_restrict_of_ae hclique, fun i => replacedLaw_clique hn I hI hI0 ρ hpair i A hA row hrow hclique⟩

/-- Reassembling over the actual root indices preserves original charge tightness. -/
theorem replacedAllLaw_tight {n : ℕ} (hn : 2 ≤ n) (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hpair : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (row : Ω → ℝ)
    (hrow : HomogeneousRows μ I Y row)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge Y v = 1) :
    ∀ᵐ v ∂replacedAllLaw μ I hI0 ρ, PhysicalPrimal.charge Y v = 1 := by
  rw [replacedAllLaw, ae_add_measure_iff, ← Measure.sum_fintype, Measure.ae_sum_iff]
  exact ⟨ae_restrict_of_ae htight, fun i => replacedLaw_tight hn I hI hI0 ρ hpair i Y hY row hrow htight⟩

/-- Graph-demand balance and independence of the class give uniqueness of
its root and hence preserve the cost of the entire original parent family. -/
theorem replacedLaws_cost_of_balance (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (E : Set (Ω × Ω))
    (hbalance : occupation η = graphDemand μ E)
    (hindependent : (μ.prod μ) (E ∩ (I ×ˢ I)) = 0) :
    cost (replacedLaws μ I hI0 η) = cost η := by
  apply replacedLaws_cost I hI hI0 η
  exact ae_at_most_one_root_graphDemand η μ E hbalance I hI hindependent

/-- The full replaced family keeps the original clique support, with its
pair absolute continuity derived from exact original balance. -/
theorem replacedLaws_clique_of_balance (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (E : Set (Ω × Ω))
    (hbalance : occupation η = graphDemand μ E) (hzero : η 0 = 0) (hone : η 1 = 0)
    (A : Ω × Ω → Bool) (hA : Measurable A) (row : Ω → Bool)
    (hrow : HomogeneousRows μ I A row)
    (hclique : ∀ n, ∀ᵐ v ∂η n, PhysicalCliqueRepresentative.Clique A v) :
    ∀ n, ∀ᵐ v ∂replacedLaws μ I hI0 η n, PhysicalCliqueRepresentative.Clique A v := by
  intro n
  by_cases hn : 2 ≤ n
  · apply replacedAllLaw_clique hn I hI hI0 (η n) _ A hA row hrow (hclique n)
    intro i j hij
    exact (pair_marginal_absolutelyContinuous_of_balance η _ hbalance n ⟨(i, j), hij⟩).trans
      Measure.absolutelyContinuous_restrict
  · have hη : η n = 0 := by interval_cases n <;> assumption
    rw [replacedLaws_zero_of_order I hI0 η n hη]
    simp

/-- The full replaced family keeps original physical dual tightness, using
only exact original balance and homogeneous original charge rows. -/
theorem replacedLaws_tight_of_balance (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)] (E : Set (Ω × Ω))
    (hbalance : occupation η = graphDemand μ E) (hzero : η 0 = 0) (hone : η 1 = 0)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (row : Ω → ℝ) (hrow : HomogeneousRows μ I Y row)
    (htight : ∀ n, ∀ᵐ v ∂η n, PhysicalPrimal.charge Y v = 1) :
    ∀ n, ∀ᵐ v ∂replacedLaws μ I hI0 η n, PhysicalPrimal.charge Y v = 1 := by
  intro n
  by_cases hn : 2 ≤ n
  · apply replacedAllLaw_tight hn I hI hI0 (η n) _ Y hY row hrow (htight n)
    intro i j hij
    exact (pair_marginal_absolutelyContinuous_of_balance η _ hbalance n ⟨(i, j), hij⟩).trans
      Measure.absolutelyContinuous_restrict
  · have hη : η n = 0 := by interval_cases n <;> assumption
    rw [replacedLaws_zero_of_order I hI0 η n hη]
    simp

end Erdos1017.PhysicalRootReplacement
