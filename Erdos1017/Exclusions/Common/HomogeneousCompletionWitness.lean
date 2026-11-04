module

public import Erdos1017.Exclusions.Common.Covered.CoveredRepeatCompression
public import Erdos1017.Exclusions.Common.Covered.CoveredAtomCompletion

/-!
# Two-copy witnesses in homogeneous cells

On one product-almost-everywhere event, every violating completed clique in a
homogeneous independent cell has a two-copy violating subset with the same
exterior.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.FiniteArity

/-- On one genuine product-AE event, every violating completed clique in
a homogeneous independent cell has a two-copy violating subset with the
same exterior. Only original independent-sample subset tests are used. -/
theorem ae_two_copy_subset_of_homogeneous_completion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (hupper : ∀ x y, Y x y ≤ 1)
    (R D : Set Ω) [DecidablePred (· ∈ D)]
    (hdisj : Disjoint R D) (ell : ℝ) (hell : 1 / 2 < ell)
    (w : Ω → ℝ)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hcell : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → Y p.1 p.2 = w p.2)
    (hfull : ∀ n, FeasibleOrder μ A Y n) (n : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      TupleClique (completeAdjacency A D) v →
      1 < tupleCharge (completeCharge A Y D ell) v →
      ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => v i ∈ D) ∧ T.card = 2 ∧
        1 < pairCharge (T ∪ Finset.univ.filter (fun i => v i ∉ D))
          (fun i j => if i = j then 0 else completeCharge A Y D ell (v i) (v j)) ∧
        ell < ∑ i ∈ Finset.univ.filter (fun i => v i ∉ D), w (v i) := by
  have hpairs := ae_all_pairs μ n _ (hroot.and (hcell.and (hbody.and hrow)))
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun k _ => hfull k)
  filter_upwards [hpairs, hsub] with v hp hv hclique hbad
  let C := Finset.univ.filter (fun i : Fin n => v i ∈ D)
  let E := Finset.univ.filter (fun i : Fin n => v i ∉ D)
  let Z := completeCharge A Y D ell
  let z (i j : Fin n) : ℝ := if i = j then 0 else Z (v i) (v j)
  have hCE : Disjoint C E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  have hCEuniv : C ∪ E = Finset.univ := by
    ext i
    simp [C, E]
    tauto
  have hC (i : Fin n) (hi : i ∈ C) : v i ∈ D := (Finset.mem_filter.mp hi).2
  have hE (i : Fin n) (hi : i ∈ E) : v i ∉ D := (Finset.mem_filter.mp hi).2
  have hsep {x : Ω} (hx : x ∈ D) : x ∉ R := fun hr => Set.disjoint_left.mp hdisj hr hx
  have hnot {i j : Fin n} (hi : i ∈ C) (hj : j ∈ E) : i ≠ j := by
    intro heq
    exact hE j hj (heq ▸ hC i hi)
  have hzsym (i j : Fin n) : z i j = z j i := by
    by_cases hij : i = j
    · simp [z, hij]
    · simp only [z, hij, Ne.symm hij, ite_false, Z, completeCharge,
        hAsym (v i) (v j), hYsym (v i) (v j)]
      congr 1
      exact propext (by tauto)
  have hsmall (T : Finset (Fin n)) (_hTC : T ⊆ C) (hcard : T.card ≤ 1) :
      pairCharge (T ∪ E) z ≤ 1 := by
    let U := T ∪ E
    have hsingle {i j : Fin n} (hi : i ∈ U) (hj : j ∈ U)
        (hiD : v i ∈ D) (hjD : v j ∈ D) : i = j := by
      have hiT : i ∈ T := (Finset.mem_union.mp hi).resolve_right (fun he => hE i he hiD)
      have hjT : j ∈ T := (Finset.mem_union.mp hj).resolve_right (fun he => hE j he hjD)
      exact Finset.card_le_one.mp hcard i hiT j hjT
    let e := (U.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin U.card) : e i ∈ U := U.orderEmbOfFin_mem rfl i
    have hn : U.card ≤ n := by simpa using Finset.card_le_univ U
    have hold : TupleClique A (fun i => v (e i)) := by
      intro i j hij
      have heij : e i ≠ e j := fun heq => hij (e.injective heq)
      have hDD : ¬(v (e i) ∈ D ∧ v (e j) ∈ D) :=
        fun h => heij (hsingle (he i) (he j) h.1 h.2)
      simpa only [completeAdjacency, ite_eq_right hDD] using hclique (e i) (e j) heij
    have ht := hv U.card hn e hold
    rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ U rfl] at ht
    convert ht using 1
    unfold pairCharge crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [z, hij]
    · simp only [z, hij, ite_false, Z, completeCharge]
      rw [ite_eq_right (fun h => hij (hsingle hi hj h.1 h.2.1))]
  have hbad' : 1 < pairCharge (C ∪ E) z := by
    rw [hCEuniv]
    exact hbad
  have hCpos : C.Nonempty := by
    by_contra hempty
    have hz := hsmall C Finset.Subset.rfl (by simp [Finset.not_nonempty_iff_eq_empty.mp hempty])
    linarith
  obtain ⟨a, ha⟩ := hCpos
  have hrootUnique : ∀ i ∈ E, ∀ j ∈ E, v i ∈ R → v j ∈ R → i = j := by
    intro i hi j _hj hiR hjR
    by_contra hij
    have hz := (hp i j hij).1 hiR hjR
    have hDD : ¬(v i ∈ D ∧ v j ∈ D) := fun h => hE i hi h.1
    have ht := hclique i j hij
    simp only [completeAdjacency, ite_eq_right hDD, hz] at ht
    contradiction
  have hincidence : (∑ i ∈ E, w (v i)) ≤ 1 := by
    apply incidence_le_one_of_single_root E (v ⁻¹' R) (fun i => w (v i)) hrootUnique
    · intro i hi _
      rw [← (hp a i (hnot ha hi)).2.2.2 (hC a ha)]
      exact hupper (v a) (v i)
    · intro i hi hiR
      rw [← (hp a i (hnot ha hi)).2.2.2 (hC a ha)]
      exact (hp a i (hnot ha hi)).2.2.1 (hsep (hC a ha)) hiR
  exact exists_two_copy_violating_subset C E hCE z (fun i => by simp [z]) hzsym ell
    (fun i => w (v i)) hell
    (fun i hi j hj hij => by
      have hz := (hp i j hij).2.1 (hC i hi) (hC j hj)
      simp [z, Z, completeCharge, hij, hC i hi, hC j hj, hz])
    (fun i hi j hj => by
      have hij := hnot hi hj
      simp only [z, hij, ite_false, Z, completeCharge, hE j hj, and_false, false_and]
      exact (hp i j hij).2.2.2 (hC i hi)) hincidence hsmall hbad'

end Erdos1017.FiniteArity
