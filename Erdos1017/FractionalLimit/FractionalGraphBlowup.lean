module

public import Erdos1017.FractionalLimit.FractionalGraphDelete
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Blowups of fractional graphs

This module defines the `blowup` of a graph by independent clones and transports
fractional partition weights to it (`blowupWeights`), giving the upper bound
`value_blowup_le` on the value of the blowup.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n t : ℕ}

/-- Independent clones have the adjacency relation of their original vertices. -/
def blowup (G : SimpleGraph (Fin n)) (t : ℕ) : SimpleGraph (Fin (n * t)) :=
  G.comap (fun z => (finProdFinEquiv.symm z).1)

def uniformAssignments (_X : Fin n → Fin t) : ℝ := ∏ _i : Fin n, (t : ℝ)⁻¹

theorem uniformAssignments_nonneg (X : Fin n → Fin t) : 0 ≤ uniformAssignments X := by
  exact Finset.prod_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem uniformAssignments_product (h : Fin n → Fin t → ℝ) :
    (∑ X : Fin n → Fin t, uniformAssignments X * ∏ i, h i (X i)) =
      ∏ i, ∑ a : Fin t, (t : ℝ)⁻¹ * h i a := by
  simp only [uniformAssignments, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : Fin t) => (t : ℝ)⁻¹ * h i a)).symm

theorem uniformAssignments_moment (ht : 0 < t) (S : Finset (Fin n))
    (a : Fin n → Fin t) :
    (∑ X : Fin n → Fin t, uniformAssignments X *
      ∏ i ∈ S, (if X i = a i then (1 : ℝ) else 0)) = ∏ _i ∈ S, (t : ℝ)⁻¹ := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have h := uniformAssignments_product (fun i b => if i ∈ S then
    (if b = a i then (1 : ℝ) else 0) else 1)
  have hfactor (i : Fin n) :
      (∑ b : Fin t, (t : ℝ)⁻¹ *
        (if i ∈ S then (if b = a i then (1 : ℝ) else 0) else 1)) =
        if i ∈ S then (t : ℝ)⁻¹ else 1 := by
    by_cases hi : i ∈ S <;> simp [hi, mul_ite, ht']
  simp only [hfactor] at h
  simpa only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] using h

theorem uniformAssignments_total (ht : 0 < t) :
    (∑ X : Fin n → Fin t, uniformAssignments X) = 1 := by
  let a : Fin n → Fin t := fun _ => ⟨0, ht⟩
  simpa using uniformAssignments_moment ht ∅ a

theorem uniformAssignments_pair (ht : 0 < t) (i j : Fin n) (hij : i ≠ j)
    (a b : Fin t) :
    (∑ X : Fin n → Fin t, uniformAssignments X *
      (if X i = a ∧ X j = b then (1 : ℝ) else 0)) = (t : ℝ)⁻¹ * (t : ℝ)⁻¹ := by
  let f : Fin n → Fin t := fun k => if k = i then a else b
  have h := uniformAssignments_moment ht {i, j} f
  simp only [Finset.prod_pair hij, f, ite_eq_right (Ne.symm hij)] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro X _
  split_ifs <;> simp_all

def cloneSet (S : Finset (Fin n)) (X : Fin n → Fin t) : Finset (Fin (n * t)) :=
  S.image (fun i => finProdFinEquiv (i, X i))

@[simp] theorem mem_cloneSet (S : Finset (Fin n)) (X : Fin n → Fin t)
    (i : Fin n) (a : Fin t) :
    finProdFinEquiv (i, a) ∈ cloneSet S X ↔ i ∈ S ∧ X i = a := by
  simp [cloneSet, Prod.mk.injEq]

theorem cloneSet_clique (G : SimpleGraph (Fin n)) (K : Clique G)
    (X : Fin n → Fin t) : (blowup G t).IsClique (cloneSet K.val X : Set _) := by
  intro u hu v hv huv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have hij : i ≠ j := by intro h; subst j; exact huv rfl
  change G.Adj (finProdFinEquiv.symm (finProdFinEquiv (i, X i))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j, X j))).1
  simpa only [Equiv.symm_apply_apply] using K.property.2 hi hj hij

def blowupMass (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (ω : Clique G × (Fin n → Fin t)) : ℝ :=
  (t : ℝ) ^ 2 * w ω.1 * uniformAssignments ω.2

def blowupWeights (G : SimpleGraph (Fin n)) (w : Clique G → ℝ) (t : ℕ) :
    Finset (Fin (n * t)) → ℝ :=
  sampleWeights (blowupMass G w) (fun ω => cloneSet ω.1.val ω.2)

theorem blowupMass_nonneg (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (hw : ∀ K, 0 ≤ w K) (ω : Clique G × (Fin n → Fin t)) :
    0 ≤ blowupMass G w ω :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (hw _)) (uniformAssignments_nonneg _)

theorem blowupWeights_cost_le (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (hw : ∀ K, 0 ≤ w K) (ht : 0 < t) :
    (∑ S, blowupWeights G w t S) ≤ (t : ℝ) ^ 2 * FinitePrimal.cost w := by
  apply (sampleWeights_cost_le _ _ (blowupMass_nonneg G w hw)).trans_eq
  simp only [blowupMass, Fintype.sum_prod_type, ← Finset.mul_sum,
    uniformAssignments_total ht, mul_one, FinitePrimal.cost]

theorem blowupWeights_feasible (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (hw : Feasible G w) (ht : 0 < t) : SubsetFeasible (blowup G t) (blowupWeights G w t) := by
  refine ⟨sampleWeights_nonneg _ _ (blowupMass_nonneg G w hw.1), ?_, ?_⟩
  · exact sampleWeights_supported _ _ _ (fun ω => cloneSet_clique G ω.1 ω.2)
  · intro u v huv
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective v
    have hij : G.Adj i j := by
      change G.Adj (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
        (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1 at huv
      simpa only [Equiv.symm_apply_apply] using huv
    rw [blowupWeights, sampleWeights_pairLoad _ _ _ _ huv.ne, Fintype.sum_prod_type]
    have hinner (K : Clique G) :
        (∑ X : Fin n → Fin t, blowupMass G w (K, X) *
          (if finProdFinEquiv (i, a) ∈ cloneSet K.val X ∧
            finProdFinEquiv (j, b) ∈ cloneSet K.val X then (1 : ℝ) else 0)) =
          w K * (if i ∈ K.val ∧ j ∈ K.val then 1 else 0) := by
      by_cases hK : i ∈ K.val ∧ j ∈ K.val
      · simp only [blowupMass, mem_cloneSet, hK.1, hK.2, true_and]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum,
          uniformAssignments_pair ht i j hij.ne a b]
        have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
        field_simp
        simp
      · have hzero (X : Fin n → Fin t) :
            ¬(finProdFinEquiv (i, a) ∈ cloneSet K.val X ∧
              finProdFinEquiv (j, b) ∈ cloneSet K.val X) := by
          simp only [mem_cloneSet]
          exact fun h => hK ⟨h.1.1, h.2.1⟩
        simp only [ite_eq_right (hzero _), mul_zero, Finset.sum_const_zero,
          ite_eq_right hK]
    simp_rw [hinner]
    have hm := (moment_apply G w ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr hij⟩).symm.trans
      (congrFun hw.2 ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr hij⟩)
    simpa [column, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using hm

theorem value_blowup_le (G : SimpleGraph (Fin n)) (ht : 0 < t) :
    value (blowup G t) ≤ (t : ℝ) ^ 2 * value G := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G w hw hmin]
  exact (value_le_subset_cost _ _ (blowupWeights_feasible G w hw ht)).trans
    (blowupWeights_cost_le G w hw.1 ht)

end Erdos1017.FractionalGraph
