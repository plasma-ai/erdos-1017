module

public import Erdos1017.Exclusions.Common.FullScalarSamplingComparison
public import Erdos1017.Models.Decorated.DecoratedKernel
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# The dispersed edit of the missing region

The edit deletes every edge inside the missing region and joins every
missing-region point to the outside body, with charge bounds and measurability.
One collection of tests licenses it under every absolutely continuous original
vertex law, and the bounded competitor obeys the scalar density limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.DispersedMissingEdit

variable {Ω : Type*}

/-- Every edge inside the entire missing region is deleted. -/
def removed (J : Set Ω) (x y : Ω) : Prop := x ∈ J ∧ y ∈ J

/-- Every missing-region point joins the whole outside body. -/
def filled (J N : Set Ω) (x y : Ω) : Prop := (x ∈ J ∧ y ∈ N) ∨ (y ∈ J ∧ x ∈ N)

/-- Both endpoints lie in the outside body. -/
def body (N : Set Ω) (x y : Ω) : Prop := x ∈ N ∧ y ∈ N

def adjacency (A : Ω → Ω → Bool) (J N : Set Ω) (x y : Ω) : Bool :=
  if removed J x y then false else if filled J N x y then true else A x y

/-- Missing-region charges are removed, the entire body charge is replaced by
its negative part, and every other old charge is retained. A newly filled
pair keeps its old absent charge zero. -/
def charge (Y : Ω → Ω → ℝ) (J N : Set Ω) (x y : Ω) : ℝ :=
  if removed J x y then 0 else if body N x y then min (Y x y) 0 else Y x y

theorem removed_symm (J : Set Ω) (x y : Ω) : removed J x y ↔ removed J y x := and_comm

theorem filled_symm (J N : Set Ω) (x y : Ω) : filled J N x y ↔ filled J N y x := or_comm

theorem body_symm (N : Set Ω) (x y : Ω) : body N x y ↔ body N y x := and_comm

theorem adjacency_symm (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : ∀ x y, A x y = A y x) (x y : Ω) :
    adjacency A J N x y = adjacency A J N y x := by
  simp only [adjacency, removed_symm J x y, filled_symm J N x y, hA x y]

theorem charge_symm (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hY : ∀ x y, Y x y = Y y x) (x y : Ω) :
    charge Y J N x y = charge Y J N y x := by
  simp only [charge, removed_symm J x y, body_symm N x y, hY x y]

theorem charge_bound (Y : Ω → Ω → ℝ) (J N : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω) : ‖charge Y J N x y‖ ≤ B := by
  unfold charge
  split_ifs
  · simpa using hB
  · have h := hY x y
    rw [Real.norm_eq_abs] at h ⊢
    rw [abs_of_nonpos (min_le_right _ _), neg_le]
    exact le_min (neg_le_of_abs_le h) (by linarith)
  · exact hY _ _

theorem charge_zero_of_nonedge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω)
    (h : adjacency A J N x y = false) : charge Y J N x y = 0 := by
  unfold adjacency at h
  unfold charge
  split_ifs at h ⊢ <;> first | rfl | contradiction | simp [hzero _ _ h]

theorem charge_le (Y : Ω → Ω → ℝ) (J N : Set Ω) (x y : Ω) (h : ¬removed J x y) :
    charge Y J N x y ≤ Y x y := by
  unfold charge
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

private theorem pairCharge_le_filter {α : Type*} [Fintype α] [DecidableEq α]
    (y Y : α → α → ℝ) (P : α → Prop) [DecidablePred P]
    (hkeep : ∀ i j, P i ∧ P j → y i j ≤ Y i j) (hdrop : ∀ i j, ¬(P i ∧ P j) → y i j ≤ 0) :
    FiniteArity.pairCharge Finset.univ y ≤ FiniteArity.pairCharge (Finset.univ.filter P) Y := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold FiniteArity.crossSum
  calc
    _ ≤ ∑ i, ∑ j, if P i ∧ P j then Y i j else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : P i ∧ P j
      · rw [ite_eq_left h]
        exact hkeep i j h
      · rw [ite_eq_right h]
        exact hdrop i j h
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i <;> simp [hi]

/-- A clique with a missing-region root has no other missing-region or
complement point. Deleting its body points originally missing that root
removes only nonpositive body charges and zero root charges; the retained
vertices form an old clique. A clique avoiding the missing region only
loses charges. -/
theorem tuple_test {n : ℕ} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (v : Fin n → Ω)
    (hmiss : ∀ i j, i ≠ j → v i ∈ J → v j ∉ J ∪ N → A (v i) (v j) = false)
    (hzero : ∀ i j, i ≠ j → A (v i) (v j) = false → Y (v i) (v j) = 0)
    (hfull : ∀ k, k ≤ n → ∀ e : Fin k ↪ Fin n,
      FiniteArity.TupleClique A (fun i => v (e i)) →
        FiniteArity.tupleCharge Y (fun i => v (e i)) ≤ 1)
    (hv : FiniteArity.TupleClique (adjacency A J N) v) :
    FiniteArity.tupleCharge (charge Y J N) v ≤ 1 := by
  have hrem {i j : Fin n} (hij : i ≠ j) : ¬removed J (v i) (v j) := by
    intro h
    have hc := hv i j hij
    simp only [adjacency, h, ite_true, Bool.false_eq_true] at hc
  have hother {r i : Fin n} (hr : v r ∈ J) (hir : i ≠ r) : v i ∈ N := by
    have hiJ : v i ∉ J := fun hiJ => hrem hir.symm ⟨hr, hiJ⟩
    by_contra hiN
    have hfill : ¬filled J N (v r) (v i) := fun h => h.elim
      (fun h => hiN h.2) (fun h => hiJ h.1)
    have hc := hv r i hir.symm
    have hz := hmiss r i hir.symm hr (by simpa only [mem_union, not_or] using ⟨hiJ, hiN⟩)
    simp only [adjacency, hrem hir.symm, hfill, ite_false, hz, Bool.false_eq_true] at hc
  let P : Fin n → Prop := fun i => ∀ r, v r ∈ J → i = r ∨ A (v r) (v i) = true
  let T := Finset.univ.filter P
  let e := (T.orderEmbOfFin rfl).toEmbedding
  have he (i : Fin T.card) : P (e i) := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).2
  have hold : FiniteArity.TupleClique A (fun i => v (e i)) := by
    intro i j hij
    change A (v (e i)) (v (e j)) = true
    have heij : e i ≠ e j := fun h => hij (e.injective h)
    by_cases hi : v (e i) ∈ J
    · exact (he j (e i) hi).resolve_left heij.symm
    · by_cases hj : v (e j) ∈ J
      · rw [hAsym]
        exact (he i (e j) hj).resolve_left heij
      · have hfill : ¬filled J N (v (e i)) (v (e j)) := fun h => h.elim
          (fun h => hi h.1) (fun h => hj h.1)
        simpa only [adjacency, hrem heij, hfill, ite_false] using hv (e i) (e j) heij
  have ht := hfull T.card (by simpa using Finset.card_le_univ T) e hold
  rw [FiniteArity.tupleCharge_subtuple Y v e, Finset.map_orderEmbOfFin_univ T rfl] at ht
  refine (pairCharge_le_filter _ _ P ?_ ?_).trans ht
  · intro i j _
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false]
      exact charge_le Y J N _ _ (hrem hij)
  have hrow {i : Fin n} (hi : ¬P i) (j : Fin n) :
      (if i = j then 0 else charge Y J N (v i) (v j)) ≤ 0 := by
    by_cases hij : i = j
    · simp [hij]
    · rw [ite_eq_right hij]
      obtain ⟨r, hP⟩ := not_forall.mp hi
      obtain ⟨hr, hP⟩ := not_imp.mp hP
      obtain ⟨hir, hA⟩ := not_or.mp hP
      have hNi := hother hr hir
      by_cases hjr : j = r
      · subst j
        have hz : Y (v i) (v r) = 0 := by
          rw [hYsym]
          exact hzero r i (Ne.symm hir) (Bool.eq_false_iff.mpr hA)
        unfold charge
        split_ifs <;> simp [hz]
      · have hbody : body N (v i) (v j) := ⟨hNi, hother hr hjr⟩
        simp only [charge, hrem hij, hbody, ite_true, ite_false]
        exact min_le_right _ _
  intro i j hij
  by_cases hi : P i
  · have hj : ¬P j := fun hj => hij ⟨hi, hj⟩
    have h := hrow hj i
    simpa only [eq_comm, charge_symm Y J N hYsym] using h
  · exact hrow hi j

variable [MeasurableSpace Ω]

private theorem measurableSet_removed (J : Set Ω) (hJ : MeasurableSet J) :
    MeasurableSet {p : Ω × Ω | removed J p.1 p.2} :=
  (hJ.preimage measurable_fst).inter (hJ.preimage measurable_snd)

private theorem measurableSet_filled (J N : Set Ω) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    MeasurableSet {p : Ω × Ω | filled J N p.1 p.2} :=
  ((hJ.preimage measurable_fst).inter (hN.preimage measurable_snd)).union
    ((hJ.preimage measurable_snd).inter (hN.preimage measurable_fst))

private theorem measurableSet_body (N : Set Ω) (hN : MeasurableSet N) :
    MeasurableSet {p : Ω × Ω | body N p.1 p.2} :=
  (hN.preimage measurable_fst).inter (hN.preimage measurable_snd)

theorem measurable_adjacency (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    Measurable (Function.uncurry (adjacency A J N)) := by
  exact measurable_const.ite (measurableSet_removed J hJ)
    (measurable_const.ite (measurableSet_filled J N hJ hN) hA)

theorem measurable_charge (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    Measurable (Function.uncurry (charge Y J N)) := by
  exact measurable_const.ite (measurableSet_removed J hJ)
    ((hY.min measurable_const).ite (measurableSet_body N hN) hY)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One original collection of actual tests licenses the dispersed edit
under every absolutely continuous old vertex law. No body sign is assumed. -/
theorem feasibleOrder_ac (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (n : ℕ) :
    FiniteArity.FeasibleOrder ν (adjacency A J N) (charge Y J N) n := by
  have hfull' (k : ℕ) : FiniteArity.FeasibleOrder ν A Y k :=
    (DecoratedKernel.pi_absolutelyContinuous hac k).ae_le (hfull k)
  have hpairs := FiniteArity.ae_all_pairs ν n _
    ((hac.prod hac).ae_le (hmiss.and hzero))
  have hsub := FiniteArity.ae_all_subtuples ν n n
    (fun _ v => FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) (fun k _ => hfull' k)
  filter_upwards [hpairs, hsub] with v hp hs hv
  apply tuple_test A Y J N hAsym hYsym v
    (fun i j hij => (hp i j hij).1)
    (fun i j hij => (hp i j hij).2) _ hv
  intro k hk e
  exact hs k hk e

/-- The actual bounded dispersed competitor obeys the full scalar limit. -/
theorem objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hY : Measurable (Function.uncurry Y))
    (hJ : MeasurableSet J) (hN : MeasurableSet N)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) :
    FiniteCappedSamplingCost.physicalObjective ν (charge Y J N) ≤
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity ν
        (adjacency A J N)) := by
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (adjacency_symm A J N hAsym) (measurable_adjacency A J N hA hJ hN)
    _ (measurable_charge Y J N hY hJ hN) B (fun p => charge_bound Y J N B hB hbound p.1 p.2)
    (Eventually.of_forall (fun p => charge_symm Y J N hYsym p.1 p.2))
    (Eventually.of_forall (fun p => charge_zero_of_nonedge A Y J N hzero p.1 p.2))
    (fun n => feasibleOrder_ac A Y J N hAsym hYsym hmiss
      (Eventually.of_forall (fun p => hzero p.1 p.2)) hfull ν hac n)

end Erdos1017.DispersedMissingEdit
