module

public import Erdos1017.Exclusions.Common.SelectedRepeatContextShape
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyUniversal

/-!
# Diffuse repeat context

The two-copy witness has only the universal root and at most one diffuse
exterior point, every other atom being ruled out by its own star floor.
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

/-- The actual two-copy witness has only the universal root and at most
one genuine diffuse exterior point. Every other original atom is ruled
out by its own star floor and the original universal-root triangle. -/
theorem exists_root_diffuse_completion_witness
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
          (fun i => S.ρ (v i) ≠ r.val)).card ≤ 1 ∧
        ∀ i ∈ Finset.univ.filter (fun i => v i ∉ D),
          S.ρ (v i) = r.val ∨ v i ∈ S.D := by
  let : Countable S.I := S.hI.to_subtype
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let V : Ω → Prop := fun x => ∀ k : S.I, r ≠ k → S.ρ x = k.val →
    -m < S.rootChargeRow r x
  have hV : ∀ᵐ x ∂μ, V x := by
    apply ae_all_iff.mpr
    intro k
    by_cases hrk : r = k
    · exact Eventually.of_forall (fun _ h => False.elim (h hrk))
    · exact ((ae_restrict_iff' (S.hfibers k.val k.property).1).mp
        (S.ae_rootChargeRow_gt_of_zero_body r k hrk hW hd hgap hzero)).mono
          (fun _ h _ => h)
  let P : Ω × Ω → Prop := fun p =>
    (S.ρ p.1 = r.val → S.ρ p.2 = r.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → Y p.1 p.2 = S.rootChargeRow u p.2) ∧
    (S.ρ p.1 = r.val → Y p.1 p.2 = S.rootChargeRow r p.2) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → A p.1 p.2 = true →
      S.rootChargeRow r p.1 + S.rootChargeRow r p.2 + Y p.1 p.2 ≤ 1)
  have hP : ∀ᵐ p ∂μ.prod μ, P p :=
    (S.ae_root_fiber_physical_independent r hW hd hgap).and
      ((S.ae_root_charge u hW hd hgap).and ((S.ae_root_charge r hW hd hgap).and
        (S.ae_universal_root_triangle r hW hd hgap
          (S.root_neutral_of_zero_body r hW hd hgap hzero))))
  let Q : ∀ n, (Fin n → Ω) → Prop := fun n v =>
    (∀ i j : Fin n, i ≠ j → P (v i, v j)) ∧ (∀ i, V (v i)) ∧ Good n v
  have hQ (n : ℕ) : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Q n v := by
    have hvertices : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i, V (v i) := by
      apply ae_all_iff.mpr
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hV
    exact (FiniteArity.ae_all_pairs μ n P hP).and (hvertices.and (hGood n))
  obtain ⟨n, hn, v, hclique, hgood, T, hTC, hcard, hbad, hincidence, hrootExists, hsmall⟩ :=
    S.exists_small_exterior_completion_witness r u hru hW hd hgap hell hzero hratio Q hQ
  let E := Finset.univ.filter (fun i : Fin n => v i ∉ {x | S.ρ x = u.val})
  have hE (i : Fin n) (hi : i ∈ E) : S.ρ (v i) ≠ u.val := (Finset.mem_filter.mp hi).2
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have haU : S.ρ (v a) = u.val := (Finset.mem_filter.mp (hTC ha)).2
  have haR : S.ρ (v a) ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans haU))
  have hne (i : Fin n) (hi : i ∈ E) : a ≠ i := fun he => hE i hi (he ▸ haU)
  obtain ⟨b, hb, hbR⟩ := hrootExists
  have hrootUnique {i : Fin n} (hi : i ∈ E) (hiR : S.ρ (v i) = r.val) : i = b := by
    by_contra hib
    have hz := (hgood.1 i b hib).1 hiR hbR
    change PhysicalRepresentative.adjacency W m (v i) (v b) = false at hz
    have hDD : ¬(v i ∈ {x | S.ρ x = u.val} ∧ v b ∈ {x | S.ρ x = u.val}) :=
      fun h => hE i hi h.1
    have hc := hclique i b hib
    simp only [FiniteArity.completeAdjacency, ite_eq_right hDD, hz] at hc
    contradiction
  have hclasses : ∀ j ∈ E, S.ρ (v j) = r.val ∨ v j ∈ S.D := by
    intro j hj
    by_cases hjR : S.ρ (v j) = r.val
    · exact Or.inl hjR
    · right
      have hjb : j ≠ b := fun he => hjR (he ▸ hbR)
      have hnotI : S.ρ (v j) ∉ S.I := by
        intro hjI
        let k : S.I := ⟨S.ρ (v j), hjI⟩
        have hrk : r ≠ k := fun he => hjR (congrArg Subtype.val he).symm
        have hstar := hgood.2.1 j k hrk rfl
        have hEeq : E = {b, j} := by
          ext i
          constructor
          · intro hi
            by_cases hiR : S.ρ (v i) = r.val
            · simp [hrootUnique hi hiR]
            · have hiF : i ∈ E.filter (fun i => S.ρ (v i) ≠ r.val) :=
                Finset.mem_filter.mpr ⟨hi, hiR⟩
              have hjF : j ∈ E.filter (fun i => S.ρ (v i) ≠ r.val) :=
                Finset.mem_filter.mpr ⟨hj, hjR⟩
              have hij := Finset.card_le_one.mp hsmall i hiF j hjF
              simp [hij]
          · intro hi
            rcases Finset.mem_insert.mp hi with he | he
            · exact he ▸ hb
            · exact (Finset.mem_singleton.mp he) ▸ hj
        have hsum : (∑ i ∈ E, S.rootChargeRow u (v i)) =
            S.rootChargeRow u (v b) + S.rootChargeRow u (v j) := by
          rw [hEeq]
          simp [Ne.symm hjb]
        have hhead : S.rootChargeRow u (v b) = S.rootChargeRow r (v a) := by
          calc
            _ = Y (v a) (v b) := ((hgood.1 a b (hne b hb)).2.1 haU).symm
            _ = Y (v b) (v a) := PhysicalRepresentative.charge_symm W m (v a) (v b)
            _ = _ := (hgood.1 b a (Ne.symm (hne b hb))).2.2.1 hbR
        have hDD : ¬(v a ∈ {x | S.ρ x = u.val} ∧ v j ∈ {x | S.ρ x = u.val}) :=
          fun h => hE j hj h.2
        have hA : A (v a) (v j) = true := by
          simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique a j (hne j hj)
        have htriangle := (hgood.1 a j (hne j hj)).2.2.2 haR hjR hA
        rw [(hgood.1 a j (hne j hj)).2.1 haU] at htriangle
        rw [hsum, hhead] at hincidence
        linarith
      rw [S.hDeq]
      simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
      rintro ⟨k, hk, he⟩
      exact hnotI (he ▸ hk)
  exact ⟨n, hn, v, hclique, hgood.2.2, T, hTC, hcard, hbad, hincidence,
    ⟨b, hb, hbR⟩, hsmall, hclasses⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
