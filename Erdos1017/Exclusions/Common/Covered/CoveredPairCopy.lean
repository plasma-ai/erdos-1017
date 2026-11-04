module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyReweight

/-!
# Feasibility of covered pair copies

With a nonpositive body, copying two adjacent exterior points is feasible for
either sign of their charge, every absolutely continuous reweighting and fresh
independent mass keeps all scalar orders on one source-pair event, and the
bounded full scalar comparison applies to every covered copy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.IndependentAtomCopy

/-- With a nonpositive body, copying two exterior adjacent points is
feasible for either sign of their charge. A rooted leaf tuple pays the
copied edge exactly once; a rootless tuple has nonpositive total charge. -/
theorem tupleCharge_covered_copy_le_one {Ω : Type*} {n : ℕ}
    (Y : Ω → Ω → ℝ) (I : Set Ω) (x y : Ω) (v : Fin n → Ω)
    (hxy : Y y x = Y x y) (hx : ∀ i, Y (v i) x = Y x (v i))
    (hy : ∀ i, Y (v i) y = Y y (v i))
    (hindependent : ∀ i j, i ≠ j → ¬(v i ∈ I ∧ v j ∈ I))
    (hbody : ∀ i j, i ≠ j → v i ∉ I → v j ∉ I → Y (v i) (v j) ≤ 0)
    (hxbody : ∀ i, v i ∉ I → Y x (v i) ≤ 0)
    (hybody : ∀ i, v i ∉ I → Y y (v i) ≤ 0)
    (hfull : FiniteArity.tupleCharge Y (Fin.cons x (Fin.cons y v)) ≤ 1) :
    FiniteArity.tupleCharge (charge Y I x y)
      (Fin.cons none (fun i => some (v i))) ≤ 1 := by
  by_cases hroot : ∃ i, v i ∈ I
  · obtain ⟨i, hi⟩ := hroot
    have hsum : (∑ j, I.indicator (fun _ => (1 : ℝ)) (v j)) = 1 := by
      rw [Finset.sum_eq_single i]
      · exact indicator_of_mem hi _
      · intro j _ hji
        exact indicator_of_notMem (fun hj => hindependent j i hji ⟨hj, hi⟩) _
      · simp
    rw [tupleCharge_copy_root]
    rw [FiniteArity.tupleCharge_cons _ x _ (fun i => Fin.cases hxy hx i),
      FiniteArity.tupleCharge_cons _ y _ hy] at hfull
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at hfull ⊢
    linarith
  · have hnone : ∀ i, v i ∉ I := fun i hi => hroot ⟨i, hi⟩
    have hbase : FiniteArity.tupleCharge Y v ≤ 0 := by
      unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      apply Finset.sum_nonpos
      intro i _
      apply Finset.sum_nonpos
      intro j _
      dsimp only
      split_ifs with hij
      · rfl
      · exact hbody i j hij (hnone i) (hnone j)
    rw [tupleCharge_copy_root]
    have hsum : (∑ i, (Y x (v i) + Y y (v i) +
        Y x y * I.indicator (fun _ => 1) (v i))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      rw [indicator_of_notMem (hnone i)]
      simpa using add_nonpos (hxbody i (hnone i)) (hybody i (hnone i))
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual old independent sample law gives a common section license
for every order of a covered pair copy, including negative source charges. -/
theorem ae_all_covered_copy_root_tests
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → Y p.1 p.2 ≤ 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      p.1 ∉ I → p.2 ∉ I → A p.1 p.2 = true →
      FiniteArity.TupleClique A v →
      (∀ i, A p.1 (v i) = true ∧ A p.2 (v i) = true) →
      FiniteArity.tupleCharge (charge Y I p.1 p.2)
        (Fin.cons none (fun i => some (v i))) ≤ 1 := by
  have hpair : ∀ᵐ p ∂μ.prod μ,
      Y p.1 p.2 = Y p.2 p.1 ∧
      (p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false) ∧
      (p.1 ∉ I → p.2 ∉ I → Y p.1 p.2 ≤ 0) := by
    filter_upwards [hYsym, hI, hbody] with p hs hi hb
    exact ⟨hs, hi, hb⟩
  have hsections := ae_all_pair_sections
    (fun n v => (FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) ∧
      (∀ i j, i ≠ j → Y (v i) (v j) = Y (v j) (v i) ∧
        (v i ∈ I → v j ∈ I → A (v i) (v j) = false) ∧
        (v i ∉ I → v j ∉ I → Y (v i) (v j) ≤ 0)))
    (fun n => by
      filter_upwards [hfull (n + 2), FiniteArity.ae_all_pairs μ (n + 2) _ hpair]
        with v hv hp
      exact ⟨hv, hp⟩)
  filter_upwards [hsections] with p hp n
  filter_upwards [hp n] with v hv hxI hyI hxy hc hn
  have hclique : FiniteArity.TupleClique A (Fin.cons p.1 (Fin.cons p.2 v)) := by
    apply FiniteArity.TupleClique.cons p.1
    · exact hc.cons p.2 (fun i => (hn i).2) (fun i => (hsym _ _).trans (hn i).2)
    · exact fun i => Fin.cases hxy (fun j => (hn j).1) i
    · exact fun i => Fin.cases ((hsym _ _).trans hxy) (fun j => (hsym _ _).trans (hn j).1) i
  apply tupleCharge_covered_copy_le_one Y I p.1 p.2 v
  · exact (hv.2 0 (0 : Fin (n + 1)).succ (Fin.succ_ne_zero _).symm).1.symm
  · exact fun i => (hv.2 i.succ.succ 0 (by simp)).1
  · exact fun i => (hv.2 i.succ.succ (0 : Fin (n + 1)).succ
      (fun he => Fin.succ_ne_zero i (Fin.succ_inj.mp he))).1
  · intro i j hij hboth
    have hz := (hv.2 i.succ.succ j.succ.succ (by simpa using hij)).2.1 hboth.1 hboth.2
    change A (v i) (v j) = false at hz
    rw [hc i j hij] at hz
    exact Bool.noConfusion hz
  · exact fun i j hij => (hv.2 i.succ.succ j.succ.succ (by simpa using hij)).2.2
  · exact fun i hi => (hv.2 0 i.succ.succ (Fin.succ_ne_zero _).symm).2.2 hxI hi
  · exact fun i hi => (hv.2 (0 : Fin (n + 1)).succ i.succ.succ
      (fun he => Fin.succ_ne_zero i (Fin.succ_inj.mp he).symm)).2.2 hyI hi
  · exact hv.1 hclique

/-- Every absolutely continuous reweighting and every fresh independent
mass preserves all scalar orders on the one original source-pair event. -/
theorem ae_all_covered_marked_feasibleOrder_ac
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → Y p.1 p.2 ≤ 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → A p.1 p.2 = true →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval, ∀ n,
        FiniteArity.FeasibleOrder (CappedModel.universalMeasure ν t)
          (markedAdjacency A p.1 p.2) (markedCharge A Y I p.1 p.2) n := by
  filter_upwards [ae_all_covered_copy_root_tests A hsym Y I hYsym hI hbody hfull]
    with p hp hxI hyI hxy
  intro ν _ hν t n
  have hsub := FiniteArity.ae_all_subtuples μ n n
    (fun _ v => FiniteArity.TupleClique A v →
      (∀ i, A p.1 (v i) = true ∧ A p.2 (v i) = true) →
      FiniteArity.tupleCharge (charge Y I p.1 p.2)
        (Fin.cons none (fun i => some (v i))) ≤ 1)
    (fun k _ => (hp k).mono (fun v hv => hv hxI hyI hxy))
  have hac := DecoratedKernel.pi_absolutelyContinuous hν n
  have hmp := measurePreserving_pi (fun _ : Fin n => CappedModel.universalMeasure ν t)
    (fun _ => ν) (fun _ => CappedModel.universal_fst_measurePreserving (μ := ν) t)
  filter_upwards [hmp.quasiMeasurePreserving.ae (hac.ae_le (hfull n)),
    hmp.quasiMeasurePreserving.ae (hac.ae_le hsub)] with v hv hs
  apply marked_tuple_test A Y I p.1 p.2 v hv
  intro k e
  have hk : k ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  exact hs k hk e

/-- Actual bounded full scalar comparison applies to all covered copies,
without placing the new row in the original compact color box. -/
theorem ae_covered_copy_objective_le_densityLimit_ac
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (hA : Measurable (Function.uncurry A)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hYsym : ∀ x y, Y x y = Y y x)
    (I : Set Ω) (hI : MeasurableSet I) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → Y p.1 p.2 ≤ 0)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I → A p.1 p.2 = true →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval,
        FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure ν t)
            (markedCharge A Y I p.1 p.2) ≤
          FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
            (CappedModel.universalMeasure ν t) (markedAdjacency A p.1 p.2)) := by
  filter_upwards [ae_all_covered_marked_feasibleOrder_ac A hsym Y I
    (Eventually.of_forall (fun p => hYsym p.1 p.2)) hindependent hbody hfull]
    with p hp hxI hyI hxy
  intro ν _ hν t
  exact FiniteCappedSamplingCost.physicalObjective_le_densityLimit_of_bounded_full_scalar_tests
    _ (markedAdjacency_symm A hsym p.1 p.2) (measurable_markedAdjacency A hA p.1 p.2)
    _ (measurable_markedCharge A hA Y hY I hI p.1 p.2) (3 * B)
    (fun z => markedCharge_bound A Y I B hB hbound p.1 p.2 z.1 z.2)
    (Eventually.of_forall (fun z => markedCharge_symm A hsym Y hYsym I p.1 p.2 z.1 z.2))
    (Eventually.of_forall (fun z => markedCharge_zero_of_nonedge A Y I p.1 p.2 z.1 z.2))
    (hp hxI hyI hxy ν hν t)

end Erdos1017.IndependentAtomCopy
