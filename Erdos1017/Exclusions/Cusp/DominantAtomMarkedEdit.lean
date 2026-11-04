module

public import Erdos1017.Exclusions.Cusp.MarkedMissingEdit

/-!
# The marked edit for a dominant atom

The edit pays the exterior of the two independent atoms, with filled and clipped
charges, a clique test, measurability and charge bounds. The product event
licenses every finite test under every absolutely continuous original law and
marking probability, and the paid mixed-remainder edit is a bounded feasible
competitor obeying the scalar density limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.DominantAtomMarkedEdit

variable {Ω : Type*}

/-- The entire exterior of the original two independent atoms is paid. -/
def exterior (I P : Set Ω) : Set Ω := (I ∪ P)ᶜ

def filled (P U : Set Ω) (x y : Ω × Bool) : Prop :=
  (MarkedMissingEdit.active U x ∧ y.1 ∈ P) ∨
    (MarkedMissingEdit.active U y ∧ x.1 ∈ P)

def clipped (I P U : Set Ω) (x y : Ω × Bool) : Prop :=
  (MarkedMissingEdit.active U x ∧ y.1 ∈ exterior I P) ∨
    (MarkedMissingEdit.active U y ∧ x.1 ∈ exterior I P)

def adjacency (A : Ω → Ω → Bool) (P U : Set Ω) (x y : Ω × Bool) : Bool :=
  if filled P U x y then true else A x.1 y.1

/-- Filling costs zero; clipping pays every mixed exterior charge as well
as every body charge with a marked endpoint. Original I rows are kept. -/
def charge (Y : Ω → Ω → ℝ) (I P U : Set Ω) (x y : Ω × Bool) : ℝ :=
  if filled P U x y then 0 else if clipped I P U x y then min (Y x.1 y.1) 0 else Y x.1 y.1

theorem filled_symm (P U : Set Ω) (x y : Ω × Bool) : filled P U x y ↔ filled P U y x := or_comm

theorem clipped_symm (I P U : Set Ω) (x y : Ω × Bool) :
    clipped I P U x y ↔ clipped I P U y x := or_comm

theorem adjacency_symm (A : Ω → Ω → Bool) (P U : Set Ω)
    (hA : ∀ x y, A x y = A y x) (x y : Ω × Bool) :
    adjacency A P U x y = adjacency A P U y x := by
  simp only [adjacency, filled_symm P U x y, hA x.1 y.1]

theorem charge_symm (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hY : ∀ x y, Y x y = Y y x) (x y : Ω × Bool) :
    charge Y I P U x y = charge Y I P U y x := by
  simp only [charge, filled_symm P U x y, clipped_symm I P U x y, hY x.1 y.1]

theorem charge_le_old (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hmiss : ∀ x y, x ∈ U → y ∈ P → A x y = false)
    (hAsym : ∀ x y, A x y = A y x)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω × Bool) :
    charge Y I P U x y ≤ Y x.1 y.1 := by
  unfold charge
  split_ifs with hfill hclip
  · rcases hfill with h | h
    · rw [hzero _ _ (hmiss _ _ h.1.1 h.2)]
    · rw [hzero _ _ ((hAsym _ _).trans (hmiss _ _ h.1.1 h.2))]
  · exact min_le_left _ _
  · exact le_rfl

theorem charge_zero_of_nonedge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hzero : ∀ x y, A x y = false → Y x y = 0) (x y : Ω × Bool)
    (h : adjacency A P U x y = false) : charge Y I P U x y = 0 := by
  have hfill : ¬filled P U x y := by
    intro hf
    simp [adjacency, hf] at h
  have hold : A x.1 y.1 = false := by simpa [adjacency, hfill] using h
  simp [charge, hfill, hzero _ _ hold]

theorem charge_bound (Y : Ω → Ω → ℝ) (I P U : Set Ω) (B : ℝ)
    (hB : 0 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (x y : Ω × Bool) :
    ‖charge Y I P U x y‖ ≤ B := by
  have h := hY x.1 y.1
  rw [Real.norm_eq_abs, abs_le] at h ⊢
  unfold charge
  split_ifs
  · exact ⟨by linarith, hB⟩
  · exact ⟨le_min h.1 (by linarith), (min_le_right _ _).trans hB⟩
  · exact h

private theorem pairCharge_le_filter {α : Type*} [Fintype α] [DecidableEq α]
    (Y Z : α → α → ℝ) (P : α → Prop) [DecidablePred P]
    (hkeep : ∀ i j, P i → P j → Y i j ≤ Z i j)
    (hdrop : ∀ i j, ¬(P i ∧ P j) → Y i j ≤ 0) :
    FiniteArity.pairCharge Finset.univ Y ≤ FiniteArity.pairCharge (Finset.univ.filter P) Z := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold FiniteArity.crossSum
  calc
    _ ≤ ∑ i, ∑ j, if P i ∧ P j then Z i j else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : P i ∧ P j
      · rw [ite_eq_left h]
        exact hkeep i j h.1 h.2
      · rw [ite_eq_right h]
        exact hdrop i j h
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i <;> simp [hi]

/-- A new P clique excludes I. Deleting all marked U vertices removes
only charges clipped to nonpositive values, leaving one actual old clique. -/
theorem tuple_test {n : ℕ} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hU : U ⊆ exterior I P) (hIP : Disjoint I P)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (v : Fin n → Ω × Bool)
    (hIPmiss : ∀ i j, i ≠ j → (v i).1 ∈ I → (v j).1 ∈ P → A (v i).1 (v j).1 = false)
    (hUPmiss : ∀ i j, i ≠ j → (v i).1 ∈ U → (v j).1 ∈ P → A (v i).1 (v j).1 = false)
    (hzero : ∀ i j, i ≠ j → A (v i).1 (v j).1 = false → Y (v i).1 (v j).1 = 0)
    (hfull : ∀ k, k ≤ n → ∀ e : Fin k ↪ Fin n,
      FiniteArity.TupleClique A (fun i => (v (e i)).1) →
        FiniteArity.tupleCharge Y (fun i => (v (e i)).1) ≤ 1)
    (hv : FiniteArity.TupleClique (adjacency A P U) v) :
    FiniteArity.tupleCharge (charge Y I P U) v ≤ 1 := by
  have hUnI {x : Ω} (hx : x ∈ U) : x ∉ I := fun hi => hU hx (Or.inl hi)
  have hUnP {x : Ω} (hx : x ∈ U) : x ∉ P := fun hp => hU hx (Or.inr hp)
  have hle (i j : Fin n) (hij : i ≠ j) :
      charge Y I P U (v i) (v j) ≤ Y (v i).1 (v j).1 := by
    unfold charge
    split_ifs with hf hc
    · rcases hf with hf | hf
      · rw [hzero i j hij (hUPmiss i j hij hf.1.1 hf.2)]
      · rw [hzero i j hij ((hAsym _ _).trans (hUPmiss j i hij.symm hf.1.1 hf.2))]
    · exact min_le_left _ _
    · exact le_rfl
  by_cases hex : ∃ p, (v p).1 ∈ P
  · obtain ⟨p, hp⟩ := hex
    have hnoI (i : Fin n) : (v i).1 ∉ I := by
      by_cases hip : i = p
      · subst i
        exact disjoint_right.mp hIP hp
      · intro hi
        have hf : ¬filled P U (v i) (v p) := by
          rintro (hf | hf)
          · exact hUnI hf.1.1 hi
          · exact hUnP hf.1.1 hp
        have hc := hv i p hip
        simp [adjacency, hf, hIPmiss i p hip hi hp] at hc
    let Q : Fin n → Prop := fun i => ¬MarkedMissingEdit.active U (v i)
    let T := Finset.univ.filter Q
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : Q (e i) := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).2
    have hold : FiniteArity.TupleClique A (fun i => (v (e i)).1) := by
      intro i j hij
      have hf : ¬filled P U (v (e i)) (v (e j)) := by
        rintro (h | h)
        · exact he i h.1
        · exact he j h.1
      simpa only [adjacency, hf, ite_false] using hv (e i) (e j) (fun h => hij (e.injective h))
    have ht := hfull T.card (by simpa using Finset.card_le_univ T) e hold
    rw [FiniteArity.tupleCharge_subtuple Y (fun i => (v i).1) e,
      Finset.map_orderEmbOfFin_univ T rfl] at ht
    have hrow {i : Fin n} (hi : ¬Q i) (j : Fin n) : charge Y I P U (v i) (v j) ≤ 0 := by
      have hactive : MarkedMissingEdit.active U (v i) := not_not.mp hi
      by_cases hjP : (v j).1 ∈ P
      · have hf : filled P U (v i) (v j) := Or.inl ⟨hactive, hjP⟩
        simp [charge, hf]
      · have hc : clipped I P U (v i) (v j) :=
          Or.inl ⟨hactive, fun h => h.elim (hnoI j) hjP⟩
        unfold charge
        split_ifs <;> first | exact le_rfl | exact min_le_right _ _
    change FiniteArity.pairCharge Finset.univ
      (fun i j => if i = j then 0 else charge Y I P U (v i) (v j)) ≤ 1
    refine (pairCharge_le_filter _ (fun i j => if i = j then 0 else Y (v i).1 (v j).1) Q ?_ ?_).trans ht
    · intro i j _ _
      by_cases hij : i = j
      · simp [hij]
      · simpa [hij] using hle i j hij
    · intro i j hij
      by_cases heq : i = j
      · simp [heq]
      · rw [ite_eq_right heq]
        by_cases hi : Q i
        · have hj : ¬Q j := fun hj => hij ⟨hi, hj⟩
          rw [charge_symm Y I P U hYsym]
          exact hrow hj i
        · exact hrow hi j
  · have hnP (i : Fin n) : (v i).1 ∉ P := fun hp => hex ⟨i, hp⟩
    have hf (i j : Fin n) : ¬filled P U (v i) (v j) := by
      rintro (h | h)
      · exact hnP j h.2
      · exact hnP i h.2
    have hold : FiniteArity.TupleClique A (fun i => (v i).1) := by
      intro i j hij
      simpa [adjacency, hf i j] using hv i j hij
    have ht := hfull n le_rfl (Function.Embedding.refl _) hold
    refine le_trans ?_ ht
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using hle i j hij

variable [MeasurableSpace Ω]

private theorem measurableSet_incidence (U E : Set Ω) (hU : MeasurableSet U) (hE : MeasurableSet E) :
    MeasurableSet {p : (Ω × Bool) × (Ω × Bool) |
      (MarkedMissingEdit.active U p.1 ∧ p.2.1 ∈ E) ∨
        (MarkedMissingEdit.active U p.2 ∧ p.1.1 ∈ E)} := by
  have hU1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.1 ∈ U} :=
    hU.preimage (measurable_fst.comp measurable_fst)
  have hU2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.1 ∈ U} :=
    hU.preimage (measurable_fst.comp measurable_snd)
  have hE1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.1 ∈ E} :=
    hE.preimage (measurable_fst.comp measurable_fst)
  have hE2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.1 ∈ E} :=
    hE.preimage (measurable_fst.comp measurable_snd)
  have hb1 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hb2 : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  exact ((hU1.inter hb1).inter hE2).union ((hU2.inter hb2).inter hE1)

theorem measurable_adjacency (A : Ω → Ω → Bool) (P U : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hP : MeasurableSet P) (hU : MeasurableSet U) :
    Measurable (Function.uncurry (adjacency A P U)) := by
  exact measurable_const.ite (measurableSet_incidence U P hU hP)
    (hA.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))

theorem measurable_charge (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hY : Measurable (Function.uncurry Y))
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hU : MeasurableSet U) :
    Measurable (Function.uncurry (charge Y I P U)) := by
  have h : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => Y p.1.1 p.2.1) :=
    hY.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  exact measurable_const.ite (measurableSet_incidence U P hU hP)
    ((h.min measurable_const).ite (measurableSet_incidence U (exterior I P) hU (hI.union hP).compl) h)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original product event licenses every finite test under every
absolutely continuous old law and every independent marking probability. -/
theorem feasibleOrder_ac (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hU : U ⊆ exterior I P) (hIP : Disjoint I P)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (hIPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ P → A p.1 p.2 = false)
    (hUPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ U → p.2 ∈ P → A p.1 p.2 = false)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (alpha : unitInterval) (n : ℕ) :
    FiniteArity.FeasibleOrder (CappedModel.universalMeasure ν alpha)
      (adjacency A P U) (charge Y I P U) n := by
  have hfull' (k : ℕ) : FiniteArity.FeasibleOrder ν A Y k :=
    (DecoratedKernel.pi_absolutelyContinuous hac k).ae_le (hfull k)
  have hpairs := FiniteArity.ae_all_pairs ν n _
    ((hac.prod hac).ae_le (hIPmiss.and (hUPmiss.and hzero)))
  have hsub := FiniteArity.ae_all_subtuples ν n n
    (fun _ v => FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) (fun k _ => hfull' k)
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure ν alpha)
    (fun _ => ν) (fun _ => CappedModel.universal_fst_measurePreserving (μ := ν) alpha)
  filter_upwards [hmp.quasiMeasurePreserving.ae hpairs,
    hmp.quasiMeasurePreserving.ae hsub] with v hp hs hv
  apply tuple_test A Y I P U hU hIP hAsym hYsym v
    (fun i j hij => (hp i j hij).1)
    (fun i j hij => (hp i j hij).2.1)
    (fun i j hij => (hp i j hij).2.2) _ hv
  intro k hk e
  exact hs k hk e

/-- The paid mixed-remainder edit is an actual bounded fully feasible
physical competitor, so its value obeys the scalar density limit. -/
theorem objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I P U : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hY : Measurable (Function.uncurry Y))
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hUmeas : MeasurableSet U)
    (hU : U ⊆ exterior I P) (hIP : Disjoint I P)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hIPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ P → A p.1 p.2 = false)
    (hUPmiss : ∀ᵐ p ∂μ.prod μ, p.1 ∈ U → p.2 ∈ P → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (alpha : unitInterval) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure ν alpha) (charge Y I P U) ≤
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
        (CappedModel.universalMeasure ν alpha) (adjacency A P U)) := by
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (adjacency_symm A P U hAsym) (measurable_adjacency A P U hA hP hUmeas)
    _ (measurable_charge Y I P U hY hI hP hUmeas) B (fun p => charge_bound Y I P U B hB hbound p.1 p.2)
    (Eventually.of_forall (fun p => charge_symm Y I P U hYsym p.1 p.2))
    (Eventually.of_forall (fun p => charge_zero_of_nonedge A Y I P U hzero p.1 p.2))
    (fun n => feasibleOrder_ac A Y I P U hU hIP hAsym hYsym hIPmiss hUPmiss
      (Eventually.of_forall (fun p => hzero p.1 p.2)) hfull ν hac alpha n)

end Erdos1017.DominantAtomMarkedEdit
