module

public import Erdos1017.Exclusions.Common.FiniteRepeatContextShape
public import Erdos1017.Exclusions.Common.SelectedHomogeneousRepeatWitness
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredCopyBonuses

/-!
# Shape of the repeat context in the selected model

An exterior independent atom forces the optimum's own `ell` below one, and the
pointwise copy bonus narrows a two-copy witness to one root and at most one
other exterior vertex.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- An exterior independent atom forces the original optimum's own
ell below one, using its derived strict star floor and actual charge cap. -/
theorem ell_lt_one_of_exterior_atom
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) : -m < 1 := by
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne'
    (S.ae_rootChargeRow_gt_of_zero_body r u hru hW hd hgap hzero)
  exact hx.trans_le (S.rootChargeRow_mem_Icc r x).2

/-- The actual pointwise copy bonus narrows a two-copy witness to one
root and at most one other exterior vertex. No regional averaging or
assumed context-shape certificate is used, and an extra AE event survives. -/
theorem exists_small_exterior_completion_witness
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (Good : ∀ n, (Fin n → Ω) → Prop)
    (hGood : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v) :
    let A := PhysicalRepresentative.adjacency W m
    let Y := PhysicalRepresentative.charge W m
    let D := {x | S.ρ x = u.val}
    ∃ n, 2 ≤ n ∧ ∃ v : Fin n → Ω,
      FiniteArity.TupleClique (FiniteArity.completeAdjacency A D) v ∧ Good n v ∧
      ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => v i ∈ D) ∧ T.card = 2 ∧
        1 < FiniteArity.pairCharge (T ∪ Finset.univ.filter (fun i => v i ∉ D))
          (fun i j => if i = j then 0 else FiniteArity.completeCharge A Y D (-m) (v i) (v j)) ∧
        -m < ∑ i ∈ Finset.univ.filter (fun i => v i ∉ D), S.rootChargeRow u (v i) ∧
        (∃ b ∈ Finset.univ.filter (fun i => v i ∉ D), S.ρ (v b) = r.val) ∧
        ((Finset.univ.filter (fun i => v i ∉ D)).filter
          (fun i => S.ρ (v i) ≠ r.val)).card ≤ 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := hW.strict_gap_structure hd hgap
  have hpenalty : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      A p.1 p.2 = true → Y p.1 p.2 ≤ -(1 + m) / 2 := by
    filter_upwards [S.ae_body_penalty_gt_half_delta_of_zero_body r hW hd hgap hzero hratio,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hp hG hY hx hy hA
    have hG1 : adjacencyKernel W p.1 p.2 = 1 := by
      change PhysicalRepresentative.adjacency W m p.1 p.2 = true at hA
      change W.moment CappedColor.adjacency p = 1
      simpa only [hA, ite_true] using hG
    have h := hp hx hy hG1
    change Y p.1 p.2 = chargeKernel W p.1 p.2 at hY
    linarith
  let P : Ω × Ω → Prop := fun p =>
    (S.ρ p.1 = r.val → S.ρ p.2 = r.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → Y p.1 p.2 = S.rootChargeRow u p.2) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → A p.1 p.2 = true →
      Y p.1 p.2 ≤ -(1 + m) / 2)
  have hP : ∀ᵐ p ∂μ.prod μ, P p :=
    (S.ae_root_fiber_physical_independent r hW hd hgap).and
      ((S.ae_root_charge u hW hd hgap).and hpenalty)
  let Q : ∀ n, (Fin n → Ω) → Prop := fun n v =>
    (∀ i j : Fin n, i ≠ j → P (v i, v j)) ∧ Good n v
  have hQ (n : ℕ) : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Q n v :=
    (FiniteArity.ae_all_pairs μ n P hP).and (hGood n)
  obtain ⟨n, hn, v, hclique, hgood, T, hTC, hcard, hbad, hincidence⟩ :=
    S.exists_two_copy_completion_witness_with_good r u hru hW hd hgap hell hzero Q hQ
  let E := Finset.univ.filter (fun i : Fin n => S.ρ (v i) ≠ u.val)
  have hE (i : Fin n) (hi : i ∈ E) : S.ρ (v i) ≠ u.val := (Finset.mem_filter.mp hi).2
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have haU : S.ρ (v a) = u.val := (Finset.mem_filter.mp (hTC ha)).2
  have haR : S.ρ (v a) ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans haU))
  have hne (i : Fin n) (hi : i ∈ E) : a ≠ i := fun he => hE i hi (he ▸ haU)
  have hroot : ∀ i ∈ E, ∀ j ∈ E, S.ρ (v i) = r.val → S.ρ (v j) = r.val → i = j := by
    intro i hi j _hj hiR hjR
    by_contra hij
    have hz := (hgood.1 i j hij).1 hiR hjR
    change PhysicalRepresentative.adjacency W m (v i) (v j) = false at hz
    have hDD : ¬(v i ∈ {x | S.ρ x = u.val} ∧ v j ∈ {x | S.ρ x = u.val}) :=
      fun h => hE i hi h.1
    have hc := hclique i j hij
    simp only [FiniteArity.completeAdjacency, ite_eq_right hDD, hz] at hc
    contradiction
  have hstar (i : Fin n) (hi : i ∈ E) (_hiR : S.ρ (v i) = r.val) :
      S.rootChargeRow u (v i) ≤ 1 := by
    rw [← (hgood.1 a i (hne i hi)).2.1 haU]
    exact (PhysicalRepresentative.charge_mem_Icc W m (v a) (v i)).2
  have hbody (i : Fin n) (hi : i ∈ E) (hiR : S.ρ (v i) ≠ r.val) :
      S.rootChargeRow u (v i) ≤ -(1 + m) / 2 := by
    have hDD : ¬(v a ∈ {x | S.ρ x = u.val} ∧ v i ∈ {x | S.ρ x = u.val}) :=
      fun h => hE i hi h.2
    have hc : A (v a) (v i) = true := by
      simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique a i (hne i hi)
    rw [← (hgood.1 a i (hne i hi)).2.1 haU]
    exact (hgood.1 a i (hne i hi)).2.2 haR hiR hc
  have hm : -m < 1 := S.ell_lt_one_of_exterior_atom r u hru hW hd hgap hzero
  have hell0 : 0 < -m := by linarith
  have hbody' (i : Fin n) (hi : i ∈ E) (hiR : S.ρ (v i) ≠ r.val) :
      S.rootChargeRow u (v i) ≤ 0 := (hbody i hi hiR).trans (by linarith)
  have hrootExists := FiniteArity.exists_root_of_incidence_pos E
    {i | S.ρ (v i) = r.val} (fun i => S.rootChargeRow u (v i)) hbody'
    (hell0.trans hincidence)
  have hsmall := FiniteArity.nonroot_card_le_one_of_incidence_gt E
    {i | S.ρ (v i) = r.val} (fun i => S.rootChargeRow u (v i)) (-m) ⟨hell0, hm⟩
    hroot hstar (by
      intro i hi hiR
      have h := hbody i hi hiR
      nlinarith) hincidence
  exact ⟨n, hn, v, hclique, hgood.2, T, hTC, hcard, hbad, hincidence, hrootExists, hsmall⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
