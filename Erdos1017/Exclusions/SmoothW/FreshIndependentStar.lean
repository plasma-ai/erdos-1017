module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyReweight
public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyValues

/-!
# Fresh independent star competitor

A fresh type is joined exactly to the old independent set (`adjacency`), old
charges are retained and a fresh-old edge carries charge one (`charge`); every
marked finite clique test holds under every absolutely continuous old law, and
the marked scalar competitor obeys the full density limit
(`objective_le_densityLimit_ac`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.FreshIndependentStar

variable {Ω : Type*}

/-- The fresh type joins exactly the old independent set. -/
def adjacency (A : Ω → Ω → Bool) (D : Set Ω) (z w : Ω × Bool) : Bool :=
  if z.2 then (if w.2 then false else decide (w.1 ∈ D))
  else if w.2 then decide (z.1 ∈ D) else A z.1 w.1

/-- Old charges are retained; a fresh-old edge carries charge one. -/
def charge (Y : Ω → Ω → ℝ) (D : Set Ω) : Ω × Bool → Ω × Bool → ℝ :=
  IndependentAtomCopy.extension (Function.uncurry Y) (D.indicator (fun _ => (1 : ℝ)))

theorem adjacency_symm (A : Ω → Ω → Bool) (D : Set Ω)
    (hA : ∀ x y, A x y = A y x) (z w : Ω × Bool) :
    adjacency A D z w = adjacency A D w z := by
  cases hz : z.2 <;> cases hw : w.2 <;> simp [adjacency, hz, hw, hA]

theorem charge_symm (Y : Ω → Ω → ℝ) (D : Set Ω)
    (hY : ∀ x y, Y x y = Y y x) (z w : Ω × Bool) :
    charge Y D z w = charge Y D w z := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    simp [charge, IndependentAtomCopy.extension, hz, hw, hY]

theorem charge_bound (Y : Ω → Ω → ℝ) (D : Set Ω) (B : ℝ)
    (hB : 1 ≤ B) (hY : ∀ x y, ‖Y x y‖ ≤ B) (z w : Ω × Bool) :
    ‖charge Y D z w‖ ≤ B := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    simp [charge, IndependentAtomCopy.extension, hz, hw]
  all_goals by_cases h : z.1 ∈ D <;> by_cases h' : w.1 ∈ D <;>
    simp [Set.indicator, h, h'] at * <;> first | exact hY _ _ | linarith

theorem charge_zero_of_nonedge (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (D : Set Ω) (hzero : ∀ x y, A x y = false → Y x y = 0)
    (z w : Ω × Bool) (h : adjacency A D z w = false) :
    charge Y D z w = 0 := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    simp [adjacency, charge, IndependentAtomCopy.extension, hz, hw] at h ⊢
  · exact hzero _ _ h
  all_goals by_cases hzD : z.1 ∈ D <;> by_cases hwD : w.1 ∈ D <;>
    simp [hzD, hwD] at h ⊢

/-- A fresh clique has at most one old vertex, by actual independence. -/
theorem tuple_test {n : ℕ} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (D : Set Ω) (v : Fin n → Ω × Bool)
    (hold : FiniteArity.TupleClique A (fun i => (v i).1) →
      FiniteArity.tupleCharge Y (fun i => (v i).1) ≤ 1)
    (hind : ∀ i j : Fin n, i ≠ j →
      (v i).1 ∈ D → (v j).1 ∈ D → A (v i).1 (v j).1 = false)
    (hv : FiniteArity.TupleClique (adjacency A D) v) :
    FiniteArity.tupleCharge (charge Y D) v ≤ 1 := by
  by_cases hfresh : ∃ r : Fin n, (v r).2 = true
  · obtain ⟨r, hr⟩ := hfresh
    have hother : ∀ i : Fin n, i ≠ r → (v i).2 = false := by
      intro i hir
      cases hi : (v i).2
      · rfl
      · have h := hv i r hir
        simp [adjacency, hi, hr] at h
    have hn : n ≤ 2 := by
      by_contra hnot
      have hthree : 2 < n := by omega
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨s, hs⟩ := exists_ne r
      obtain ⟨t, htr, hts⟩ := Fin.exists_ne_and_ne_of_two_lt r s hthree
      have hsD : (v s).1 ∈ D := by
        have h := hv r s hs.symm
        simpa [adjacency, hr, hother s hs] using h
      have htD : (v t).1 ∈ D := by
        have h := hv r t htr.symm
        simpa [adjacency, hr, hother t htr] using h
      have hst := hv s t hts.symm
      have hA : A (v s).1 (v t).1 = true := by
        simpa [adjacency, hother s hs, hother t htr] using hst
      exact Bool.false_ne_true ((hind s t hts.symm hsD htD).symm.trans hA)
    interval_cases n
    · rw [FiniteArity.tupleCharge_small (by omega : 0 ≤ 1)]
      norm_num
    · rw [FiniteArity.tupleCharge_small (by omega : 1 ≤ 1)]
      norm_num
    · have hr0 : r = 0 ∨ r = 1 := by fin_cases r <;> simp
      rcases hr0 with rfl | rfl
      · have hD : (v 1).1 ∈ D := by
          have h := hv 0 1 (by decide)
          simpa [adjacency, hr, hother 1 (by decide)] using h
        simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
          FiniteArity.crossSum, Fin.sum_univ_two, charge,
          IndependentAtomCopy.extension, hr, hother 1 (by decide),
          Set.indicator_of_mem hD]
      · have hD : (v 0).1 ∈ D := by
          have h := hv 1 0 (by decide)
          simpa [adjacency, hr, hother 0 (by decide)] using h
        simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
          FiniteArity.crossSum, Fin.sum_univ_two, charge,
          IndependentAtomCopy.extension, hr, hother 0 (by decide),
          Set.indicator_of_mem hD]
  · have hmark : ∀ i : Fin n, (v i).2 = false := by
      intro i
      cases hi : (v i).2
      · rfl
      · exact (hfresh ⟨i, hi⟩).elim
    have hclique : FiniteArity.TupleClique A (fun i => (v i).1) := by
      intro i j hij
      simpa [adjacency, hmark i, hmark j] using hv i j hij
    have heq : FiniteArity.tupleCharge (charge Y D) v =
        FiniteArity.tupleCharge Y (fun i => (v i).1) := by
      unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
      simp [charge, IndependentAtomCopy.extension, hmark]
    rw [heq]
    exact hold hclique

variable [MeasurableSpace Ω]

theorem measurable_adjacency (A : Ω → Ω → Bool) (D : Set Ω)
    (hA : Measurable (Function.uncurry A)) (hD : MeasurableSet D) :
    Measurable (Function.uncurry (adjacency A D)) := by
  have hfst : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hsnd : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hm1 : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hm2 : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hD1 : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => decide (p.1.1 ∈ D)) := by
    have he : (fun p : (Ω × Bool) × (Ω × Bool) => decide (p.1.1 ∈ D)) =
        fun p => if p.1.1 ∈ D then true else false := by
      funext p
      by_cases hp : p.1.1 ∈ D <;> simp [hp]
    rw [he]
    exact Measurable.ite (hD.preimage hfst) measurable_const measurable_const
  have hD2 : Measurable (fun p : (Ω × Bool) × (Ω × Bool) => decide (p.2.1 ∈ D)) := by
    have he : (fun p : (Ω × Bool) × (Ω × Bool) => decide (p.2.1 ∈ D)) =
        fun p => if p.2.1 ∈ D then true else false := by
      funext p
      by_cases hp : p.2.1 ∈ D <;> simp [hp]
    rw [he]
    exact Measurable.ite (hD.preimage hsnd) measurable_const measurable_const
  change Measurable (fun p : (Ω × Bool) × (Ω × Bool) =>
    if p.1.2 then (if p.2.2 then false else decide (p.2.1 ∈ D))
    else if p.2.2 then decide (p.1.1 ∈ D) else A p.1.1 p.2.1)
  exact Measurable.ite (measurableSet_eq_fun hm1 measurable_const)
    (Measurable.ite (measurableSet_eq_fun hm2 measurable_const) measurable_const hD2)
    (Measurable.ite (measurableSet_eq_fun hm2 measurable_const) hD1
      (hA.comp (hfst.prodMk hsnd)))

theorem measurable_charge (Y : Ω → Ω → ℝ) (D : Set Ω)
    (hY : Measurable (Function.uncurry Y)) (hD : MeasurableSet D) :
    Measurable (Function.uncurry (charge Y D)) := by
  have hf : Measurable (D.indicator (fun _ : Ω => (1 : ℝ))) :=
    measurable_const.indicator hD
  have hl : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.1.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const
  have hr : MeasurableSet {p : (Ω × Bool) × (Ω × Bool) | p.2.2 = true} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const
  change Measurable (fun p : (Ω × Bool) × (Ω × Bool) =>
    if p.1.2 = true then (if p.2.2 = true then 0 else D.indicator (fun _ => 1) p.2.1)
    else if p.2.2 = true then D.indicator (fun _ => 1) p.1.1 else Y p.1.1 p.2.1)
  exact Measurable.ite hl
    (Measurable.ite hr measurable_const (hf.comp (measurable_fst.comp measurable_snd)))
    (Measurable.ite hr (hf.comp (measurable_fst.comp measurable_fst))
      (hY.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))))

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independence of the old star neighborhood proves every marked
finite clique test under every absolutely continuous old law. -/
theorem feasibleOrder_ac (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (D : Set Ω)
    (hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ)
    (t : unitInterval) (n : ℕ) :
    FiniteArity.FeasibleOrder (CappedModel.universalMeasure ν t)
      (adjacency A D) (charge Y D) n := by
  have h_old : FiniteArity.FeasibleOrder ν A Y n :=
    (DecoratedKernel.pi_absolutelyContinuous hac n).ae_le (hfull n)
  have h_ind : ∀ᵐ p ∂ν.prod ν, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false :=
    (hac.prod hac).ae_le hind
  have h_pairs := FiniteArity.ae_all_pairs ν n
    (fun p => p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false) h_ind
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure ν t)
    (fun _ => ν) (fun _ => CappedModel.universal_fst_measurePreserving (μ := ν) t)
  filter_upwards [hmp.quasiMeasurePreserving.ae h_old,
    hmp.quasiMeasurePreserving.ae h_pairs] with v hv hp
  exact tuple_test A Y D v hv hp

/-- The genuine marked scalar competitor obeys the full density limit
for every absolutely continuous reweighting and fresh mass. -/
theorem objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (hYsym : ∀ x y, Y x y = Y y x)
    (D : Set Ω) (hD : MeasurableSet D)
    (B : ℝ) (hB : 1 ≤ B) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hac : ν ≪ μ) (t : unitInterval) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure ν t)
        (charge Y D) ≤
      FractionalGraph.densityLimit
        (FiniteCappedSamplingCost.physicalDensity (CappedModel.universalMeasure ν t)
          (adjacency A D)) := by
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    (adjacency A D) (adjacency_symm A D hsym) (measurable_adjacency A D hA hD)
    (charge Y D) (measurable_charge Y D hY hD) B
    (fun p => charge_bound Y D B hB hbound p.1 p.2)
    (Eventually.of_forall (fun p => charge_symm Y D hYsym p.1 p.2))
    (Eventually.of_forall (fun p => charge_zero_of_nonedge A Y D hzero p.1 p.2))
    (fun n => feasibleOrder_ac A Y D hind hfull ν hac t n)

end Erdos1017.FreshIndependentStar
