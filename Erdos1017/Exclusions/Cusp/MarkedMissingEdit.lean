module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyReweight
public import Erdos1017.Exclusions.Common.Physical.IndependentPositiveCoverCompletion

/-!
# The marked edit of the missing region

A mark acts only on a vertex in the designated source: every source-source edge
with a marked endpoint is deleted and a marked source joins the designated body.
One collection of tests licenses the edit at every mass under every absolutely
continuous original law, and the bounded competitor obeys the scalar limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.MarkedMissingEdit

variable {Ω : Type*}

/-- A mark acts only on a vertex in the entire designated source. -/
def active (J : Set Ω) (x : Ω × Bool) : Prop := x.1 ∈ J ∧ x.2 = true

/-- Every source-source edge with a marked endpoint is deleted. -/
def removed (J : Set Ω) (x y : Ω × Bool) : Prop :=
  x.1 ∈ J ∧ y.1 ∈ J ∧ (x.2 = true ∨ y.2 = true)

/-- A marked source joins the designated body. -/
def filled (J N : Set Ω) (x y : Ω × Bool) : Prop :=
  (active J x ∧ y.1 ∈ N) ∨ (active J y ∧ x.1 ∈ N)

def adjacency (A : Ω → Ω → Bool) (J N : Set Ω) (x y : Ω × Bool) : Bool :=
  if removed J x y then false else if filled J N x y then true else A x.1 y.1

/-- Old present cross charges are retained; a newly filled pair has its
old absent charge zero. Only the deleted source-source charges are removed. -/
def charge (Y : Ω → Ω → ℝ) (J : Set Ω) (x y : Ω × Bool) : ℝ :=
  if removed J x y then 0 else Y x.1 y.1

theorem removed_symm (J : Set Ω) (x y : Ω × Bool) : removed J x y ↔ removed J y x := by
  simp only [removed]
  tauto

theorem filled_symm (J N : Set Ω) (x y : Ω × Bool) : filled J N x y ↔ filled J N y x := by
  exact or_comm

theorem adjacency_symm (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : ∀ x y, A x y = A y x) (x y : Ω × Bool) :
    adjacency A J N x y = adjacency A J N y x := by
  simp only [adjacency, removed_symm J x y, filled_symm J N x y, hA x.1 y.1]

theorem charge_symm (Y : Ω → Ω → ℝ) (J : Set Ω)
    (hY : ∀ x y, Y x y = Y y x) (x y : Ω × Bool) :
    charge Y J x y = charge Y J y x := by
  simp only [charge, removed_symm J x y, hY x.1 y.1]

theorem charge_bound (Y : Ω → Ω → ℝ) (J : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω × Bool) : ‖charge Y J x y‖ ≤ B := by
  unfold charge
  split_ifs <;> first | simpa using hB | exact hY _ _

theorem charge_zero_of_nonedge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω × Bool)
    (h : adjacency A J N x y = false) : charge Y J x y = 0 := by
  unfold adjacency at h
  unfold charge
  split_ifs at h ⊢ <;> first | rfl | contradiction | exact hzero _ _ h

private theorem pairCharge_le_filter {α : Type*} [Fintype α] [DecidableEq α]
    (Y : α → α → ℝ) (P : α → Prop) [DecidablePred P]
    (hdrop : ∀ i j, ¬(P i ∧ P j) → Y i j ≤ 0) :
    FiniteArity.pairCharge Finset.univ Y ≤ FiniteArity.pairCharge (Finset.univ.filter P) Y := by
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
      · rw [ite_eq_right h]
        exact hdrop i j h
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i <;> simp [hi]

/-- A clique with a marked source has no other source or exterior point.
Deleting its old nonneighbors removes only nonpositive body charges and
zero source charges; the retained vertices form an old clique. -/
theorem tuple_test {n : ℕ} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hdis : Disjoint J N) (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (v : Fin n → Ω × Bool)
    (hmiss : ∀ i j, i ≠ j → (v i).1 ∈ J → (v j).1 ∉ J ∪ N → A (v i).1 (v j).1 = false)
    (hbody : ∀ i j, i ≠ j → (v i).1 ∈ N → (v j).1 ∈ N → Y (v i).1 (v j).1 ≤ 0)
    (hzero : ∀ i j, i ≠ j → A (v i).1 (v j).1 = false → Y (v i).1 (v j).1 = 0)
    (hfull : ∀ k, k ≤ n → ∀ e : Fin k ↪ Fin n,
      FiniteArity.TupleClique A (fun i => (v (e i)).1) →
        FiniteArity.tupleCharge Y (fun i => (v (e i)).1) ≤ 1)
    (hv : FiniteArity.TupleClique (adjacency A J N) v) :
    FiniteArity.tupleCharge (charge Y J) v ≤ 1 := by
  have hsep {x : Ω} (hx : x ∈ J) : x ∉ N := fun hn => disjoint_left.mp hdis hx hn
  by_cases hex : ∃ r, active J (v r)
  · obtain ⟨r, hr⟩ := hex
    have hother {i : Fin n} (hir : i ≠ r) : (v i).1 ∈ N := by
      have hc := hv r i hir.symm
      by_cases hiJ : (v i).1 ∈ J
      · have hrem : removed J (v r) (v i) := ⟨hr.1, hiJ, Or.inl hr.2⟩
        simp only [adjacency, hrem, ite_true, Bool.false_eq_true] at hc
      · by_contra hiN
        have hrem : ¬removed J (v r) (v i) := fun h => hiJ h.2.1
        have hfill : ¬filled J N (v r) (v i) := fun h => h.elim
          (fun h => hiN h.2) (fun h => hsep hr.1 h.2)
        have hzero := hmiss r i hir.symm hr.1 (by simpa only [mem_union, not_or] using ⟨hiJ, hiN⟩)
        simp only [adjacency, hrem, hfill, ite_false, hzero, Bool.false_eq_true] at hc
    have hcharge : FiniteArity.tupleCharge (charge Y J) v =
        FiniteArity.tupleCharge Y (fun i => (v i).1) := by
      unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · have hrem : ¬removed J (v i) (v j) := by
          intro h
          have hc := hv i j hij
          simp only [adjacency, h, ite_true, Bool.false_eq_true] at hc
        simp only [hij, ite_false, charge, hrem]
    rw [hcharge]
    let P : Fin n → Prop := fun i => i = r ∨ A (v r).1 (v i).1 = true
    let T := Finset.univ.filter P
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : P (e i) := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).2
    have hold : FiniteArity.TupleClique A (fun i => (v (e i)).1) := by
      intro i j hij
      change A (v (e i)).1 (v (e j)).1 = true
      have heij : e i ≠ e j := fun h => hij (e.injective h)
      by_cases hi : e i = r
      · rw [hi]
        exact (he j).resolve_left (fun h => heij (hi.trans h.symm))
      · by_cases hj : e j = r
        · rw [hj, hAsym]
          exact (he i).resolve_left hi
        · have hNi := hother hi
          have hNj := hother hj
          have hnJi : (v (e i)).1 ∉ J := disjoint_right.mp hdis hNi
          have hnJj : (v (e j)).1 ∉ J := disjoint_right.mp hdis hNj
          simpa only [adjacency, removed, filled, active, hnJi, hnJj, false_and,
            and_false, false_or, or_false, ite_false] using hv (e i) (e j) heij
    have ht := hfull T.card (by simpa using Finset.card_le_univ T) e hold
    rw [FiniteArity.tupleCharge_subtuple Y (fun i => (v i).1) e,
      Finset.map_orderEmbOfFin_univ T rfl] at ht
    change FiniteArity.pairCharge Finset.univ
      (fun i j => if i = j then 0 else Y (v i).1 (v j).1) ≤ 1
    refine (pairCharge_le_filter _ P ?_).trans ht
    have hrow {i : Fin n} (hi : ¬P i) (j : Fin n) :
        (if i = j then 0 else Y (v i).1 (v j).1) ≤ 0 := by
      by_cases hij : i = j
      · simp [hij]
      · rw [ite_eq_right hij]
        have hir : i ≠ r := fun he => hi (Or.inl he)
        by_cases hjr : j = r
        · subst j
          have hz : A (v r).1 (v i).1 = false := Bool.eq_false_iff.mpr (fun h => hi (Or.inr h))
          rw [hYsym, hzero r i hir.symm hz]
        · exact hbody i j hij (hother hir) (hother hjr)
    intro i j hij
    by_cases hi : P i
    · have hj : ¬P j := fun hj => hij ⟨hi, hj⟩
      have h := hrow hj i
      simpa only [eq_comm, hYsym] using h
    · exact hrow hi j
  · have hactive (i : Fin n) : ¬active J (v i) := fun h => hex ⟨i, h⟩
    have hrem (i j : Fin n) : ¬removed J (v i) (v j) := by
      rintro ⟨hi, hj, hm | hm⟩
      · exact hactive i ⟨hi, hm⟩
      · exact hactive j ⟨hj, hm⟩
    have hfill (i j : Fin n) : ¬filled J N (v i) (v j) := fun h => h.elim
      (fun h => hactive i h.1) (fun h => hactive j h.1)
    have hold : FiniteArity.TupleClique A (fun i => (v i).1) := by
      intro i j hij
      simpa only [adjacency, hrem i j, hfill i j, ite_false] using hv i j hij
    have ht := hfull n le_rfl (Function.Embedding.refl _) hold
    change FiniteArity.tupleCharge Y (fun i => (v i).1) ≤ 1 at ht
    simpa only [FiniteArity.tupleCharge, charge, hrem, ite_false] using ht

variable [MeasurableSpace Ω]

private theorem measurableSet_removed (J : Set Ω) (hJ : MeasurableSet J) :
    MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | removed J p.1 p.2} := by
  have hJ1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.1 ∈ J} :=
    hJ.preimage (measurable_fst.comp measurable_fst)
  have hJ2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.1 ∈ J} :=
    hJ.preimage (measurable_fst.comp measurable_snd)
  have hb1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hb2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact hJ1.inter (hJ2.inter (hb1.union hb2))

private theorem measurableSet_filled (J N : Set Ω) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | filled J N p.1 p.2} := by
  have hJ1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.1 ∈ J} :=
    hJ.preimage (measurable_fst.comp measurable_fst)
  have hJ2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.1 ∈ J} :=
    hJ.preimage (measurable_fst.comp measurable_snd)
  have hN1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.1 ∈ N} :=
    hN.preimage (measurable_fst.comp measurable_fst)
  have hN2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.1 ∈ N} :=
    hN.preimage (measurable_fst.comp measurable_snd)
  have hb1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hb2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact ((hJ1.inter hb1).inter hN2).union ((hJ2.inter hb2).inter hN1)

theorem measurable_adjacency (A : Ω → Ω → Bool) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hJ : MeasurableSet J) (hN : MeasurableSet N) :
    Measurable (Function.uncurry (adjacency A J N)) := by
  exact measurable_const.ite (measurableSet_removed J hJ)
    (measurable_const.ite (measurableSet_filled J N hJ hN)
      (hA.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))))

theorem measurable_charge (Y : Ω → Ω → ℝ) (J : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hJ : MeasurableSet J) :
    Measurable (Function.uncurry (charge Y J)) := by
  exact measurable_const.ite (measurableSet_removed J hJ)
    (hY.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One original collection of actual tests licenses the marked edit at
every mass and under every absolutely continuous old vertex law. -/
theorem feasibleOrder_ac (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hdis : Disjoint J N) (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∈ N → p.2 ∈ N → Y p.1 p.2 ≤ 0)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (alpha : unitInterval) (n : ℕ) :
    FiniteArity.FeasibleOrder (CappedModel.universalMeasure ν alpha)
      (adjacency A J N) (charge Y J) n := by
  have hfull' (k : ℕ) : FiniteArity.FeasibleOrder ν A Y k :=
    (DecoratedKernel.pi_absolutelyContinuous hac k).ae_le (hfull k)
  have hpairs := FiniteArity.ae_all_pairs ν n _
    ((hac.prod hac).ae_le (hmiss.and (hbody.and hzero)))
  have hsub := FiniteArity.ae_all_subtuples ν n n
    (fun _ v => FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) (fun k _ => hfull' k)
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure ν alpha)
    (fun _ => ν) (fun _ => CappedModel.universal_fst_measurePreserving (μ := ν) alpha)
  filter_upwards [hmp.quasiMeasurePreserving.ae hpairs,
    hmp.quasiMeasurePreserving.ae hsub] with v hp hs hv
  apply tuple_test A Y J N hdis hAsym hYsym v
    (fun i j hij => (hp i j hij).1)
    (fun i j hij => (hp i j hij).2.1)
    (fun i j hij => (hp i j hij).2.2) _ hv
  intro k hk e
  exact hs k hk e

/-- The actual bounded marked competitor obeys the full scalar limit. -/
theorem objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (J N : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hY : Measurable (Function.uncurry Y))
    (hJ : MeasurableSet J) (hN : MeasurableSet N)
    (hdis : Disjoint J N) (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∉ J ∪ N → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∈ N → p.2 ∈ N → Y p.1 p.2 ≤ 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (alpha : unitInterval) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure ν alpha) (charge Y J) ≤
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
        (CappedModel.universalMeasure ν alpha) (adjacency A J N)) := by
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (adjacency_symm A J N hAsym) (measurable_adjacency A J N hA hJ hN)
    _ (measurable_charge Y J hY hJ) B (fun p => charge_bound Y J B hB hbound p.1 p.2)
    (Eventually.of_forall (fun p => charge_symm Y J hYsym p.1 p.2))
    (Eventually.of_forall (fun p => charge_zero_of_nonedge A Y J N hzero p.1 p.2))
    (fun n => feasibleOrder_ac A Y J N hdis hAsym hYsym hmiss hbody
      (Eventually.of_forall (fun p => hzero p.1 p.2)) hfull ν hac alpha n)

end Erdos1017.MarkedMissingEdit
