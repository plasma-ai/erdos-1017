module

public import Erdos1017.Exclusions.Common.Covered.CoveredBoundaryRepresentedRepeat
public import Erdos1017.Exclusions.Common.SelectedRepeatContextShape

/-!
# Shape of the boundary repeat context

Conditional completion supplies a finite two-copy witness whose exterior
consists of one root and at most one `D` label, with its exterior charge and
incidence retained (`exists_covered_boundary_coefficient_context`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Actual conditional completion supplies a finite two-copy witness
whose exterior consists of one root and at most one D label. Its
exterior charge and incidence retain the literal original coefficients. -/
theorem exists_covered_boundary_coefficient_context (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) :
    ∃ (n : ℕ) (E : Finset (Fin n)) (q : Fin n → S.I ⊕ Unit) (Z : Fin n → Fin n → ℝ),
      (∀ i, Z i i = 0) ∧ (∀ i j, Z i j = Z j i) ∧
      (∀ i ∈ E, ∀ j ∈ E, i ≠ j → Z i j = S.coveredCountableBoundaryCoefficient (q i) (q j)) ∧
      1 < FiniteArity.pairCharge E Z +
        2 * (∑ i ∈ E, S.coveredCountableBoundaryCoefficient (Sum.inl u) (q i)) + m ∧
      (∃ b ∈ E, q b = Sum.inl r ∧ ∀ i ∈ E, q i = Sum.inl r → i = b) ∧
      (E.filter (fun i => q i ≠ Sum.inl r)).card ≤ 1 ∧
      ∀ i ∈ E, q i = Sum.inl r ∨ ∃ flag : Unit, q i = Sum.inr flag := by
  obtain ⟨V, hV, hmom, _, _⟩ :=
    S.exists_covered_countable_boundary_stationary_average mode r a hW hd hgap hpair
      hzero hD hnull
  let A := PhysicalRepresentative.adjacency V m
  let Y := PhysicalRepresentative.charge V m
  let P : Ω × Ω → Prop := fun p =>
    A p.1 p.2 = S.coveredCountableBoundaryGraph mode r a
          (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) ∧
    Y p.1 p.2 = S.coveredCountableBoundaryCoefficient
      (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2)
  have hP : ∀ᵐ p ∂μ.prod μ, P p := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq V m
      (hV.strict_gap_structure hd hgap).strict_support,
      PhysicalRepresentative.charge_ae_eq V m
        (hV.strict_gap_structure hd hgap).strict_support] with p hp hy
    constructor
    · have he := hp.symm.trans (hmom p).1
      cases hA : A p.1 p.2 <;>
        cases hH : S.coveredCountableBoundaryGraph mode r a
          (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) <;>
        simp_all [A]
    · exact hy.trans (hmom p).2
  let Good : ∀ n, (Fin n → Ω) → Prop := fun _ v => ∀ i j, i ≠ j → P (v i, v j)
  have hGood (n : ℕ) : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v :=
    FiniteArity.ae_all_pairs μ n P hP
  obtain ⟨n, _, cfg, hclique, hgood, T, hTC, hcard, hbad, hincidence⟩ :=
    S.covered_boundary_repeat_witness_of_model mode r a V hV hd hgap hmom hzero u hru
      hell Good hGood
  let E := Finset.univ.filter (fun i : Fin n => S.ρ (cfg i) ≠ u.val)
  let q := fun i : Fin n => S.coveredCountableBoundaryLabel (cfg i)
  let Z := fun i j : Fin n => if i = j then 0 else
    FiniteArity.completeCharge A Y {x | S.ρ x = u.val} (-m) (cfg i) (cfg j)
  let w := fun i : Fin n => S.coveredCountableBoundaryCoefficient (Sum.inl u) (q i)
  have hp (i j : Fin n) (hij : i ≠ j) :
      A (cfg i) (cfg j) = S.coveredCountableBoundaryGraph mode r a (q i) (q j) ∧
      Y (cfg i) (cfg j) = S.coveredCountableBoundaryCoefficient (q i) (q j) := hgood i j hij
  have hE' (i : Fin n) (hi : i ∈ E) : S.ρ (cfg i) ≠ u.val := (Finset.mem_filter.mp hi).2
  have hT (i : Fin n) (hi : i ∈ T) : S.ρ (cfg i) = u.val :=
    (Finset.mem_filter.mp (hTC hi)).2
  have hlabel (i : Fin n) : q i = Sum.inl u ↔ S.ρ (cfg i) = u.val :=
    S.coveredCountableBoundaryLabel_eq_inl_iff u (cfg i)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hvU := hT v hv
  have hne (i : Fin n) (hi : i ∈ E) : v ≠ i := fun he => hE' i hi (he ▸ hvU)
  have hjoin (i : Fin n) (hi : i ∈ E) :
      S.coveredCountableBoundaryGraph mode r a (Sum.inl u) (q i) = true := by
    have hDD : ¬(cfg v ∈ {x | S.ρ x = u.val} ∧ cfg i ∈ {x | S.ρ x = u.val}) :=
      fun h => hE' i hi h.2
    have hc : A (cfg v) (cfg i) = true := by
      simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique v i (hne i hi)
    rw [(hp v i (hne i hi)).1, (hlabel v).mpr hvU] at hc
    exact hc
  have hroot : ∀ i ∈ E, ∀ j ∈ E, q i = Sum.inl r → q j = Sum.inl r → i = j := by
    intro i hi j _ hiR hjR
    by_contra hij
    have hz := (hp i j hij).1
    rw [hiR, hjR] at hz
    have hDD : ¬(cfg i ∈ {x | S.ρ x = u.val} ∧ cfg j ∈ {x | S.ρ x = u.val}) :=
      fun h => hE' i hi h.1
    have hc : A (cfg i) (cfg j) = true := by
      simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique i j hij
    have hzfalse : A (cfg i) (cfg j) = false := by
      simpa [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph] using hz
    rw [hc] at hzfalse
    contradiction
  have hstar (i : Fin n) (_hi : i ∈ E) (_hiR : q i = Sum.inl r) : w i ≤ 1 :=
    (S.coveredCountableBoundaryCoefficient_mem hD (Sum.inl u) (q i)).2
  have hbody (i : Fin n) (hi : i ∈ E) (hiR : q i ≠ Sum.inl r) :
      w i ≤ -(1 + m) / 2 := by
    have huR : (Sum.inl u : S.I ⊕ Unit) ≠ Sum.inl r := by simp [Ne.symm hru]
    have hp := S.coveredCountableBoundaryCoefficient_penalty_gt_half_delta mode r a hW hd hgap hpair hzero
      hD hnull hratio (Sum.inl u) (q i) huR hiR (hjoin i hi)
    dsimp [w]
    linarith
  have hm : -m < 1 := S.ell_lt_one_of_exterior_atom r u hru hW hd hgap hzero
  have hell0 : 0 < -m := by linarith
  obtain ⟨b, hb, hbR⟩ := FiniteArity.exists_root_of_incidence_pos E
    {i | q i = Sum.inl r} w
    (fun i hi hn => (hbody i hi hn).trans (by linarith)) (hell0.trans hincidence)
  change q b = Sum.inl r at hbR
  have hsmall := FiniteArity.nonroot_card_le_one_of_incidence_gt E
    {i | q i = Sum.inl r} w (-m) ⟨hell0, hm⟩ hroot hstar
    (by intro i hi hn; have h := hbody i hi hn; linarith) hincidence
  have hunique {i : Fin n} (hi : i ∈ E) (hiR : q i = Sum.inl r) : i = b :=
    hroot i hi b hb hiR hbR
  have hEeq {j : Fin n} (hj : j ∈ E) (hjR : q j ≠ Sum.inl r) : E = {b, j} := by
    ext i
    constructor
    · intro hi
      by_cases hiR : q i = Sum.inl r
      · simp [hunique hi hiR]
      · have he := Finset.card_le_one.mp hsmall i (Finset.mem_filter.mpr ⟨hi, hiR⟩)
          j (Finset.mem_filter.mpr ⟨hj, hjR⟩)
        simp [he]
    · intro hi
      rcases Finset.mem_insert.mp hi with he | he
      · exact he ▸ hb
      · exact (Finset.mem_singleton.mp he) ▸ hj
  have hclasses : ∀ j ∈ E, q j = Sum.inl r ∨ ∃ flag : Unit, q j = Sum.inr flag := by
    intro j hj
    by_cases hjR : q j = Sum.inl r
    · exact Or.inl hjR
    right
    cases hqj : q j with
    | inr flag => exact ⟨flag, rfl⟩
    | inl k =>
      have hkr : k ≠ r := fun he => hjR (hqj.trans (congrArg Sum.inl he))
      have hku : k ≠ u := fun he => hE' j hj ((hlabel j).mp (hqj.trans (congrArg Sum.inl he)))
      have hkb : S.coveredCountableBoundaryGraph mode r a (Sum.inl r) (Sum.inl k) = true := by
        simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph, Ne.symm hkr, hpair.1]
      have hub : S.coveredCountableBoundaryGraph mode r a (Sum.inl r) (Sum.inl u) = true := by
        simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph, hru, hpair.1]
      have huk := hjoin j hj
      rw [hqj] at huk
      have htri := S.coveredCountableBoundaryCoefficient_triangle mode r a hW hd hgap hpair hzero hD hnull
        (Sum.inl r) (Sum.inl u) (Sum.inl k) hub hkb huk
      have hfloor := S.coveredCountableBoundaryCoefficient_root_atom_gt r a k (Ne.symm hkr) hW hd hgap hzero
      have hsum : (∑ i ∈ E, w i) =
          S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) +
          S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl k) := by
        rw [hEeq hj hjR]
        have hjb : j ≠ b := fun he => hjR (he ▸ hbR)
        simp [Ne.symm hjb, w, hbR, hqj,
          S.coveredCountableBoundaryCoefficient_symm (Sum.inl u) (Sum.inl r)]
      change -m < ∑ i ∈ E, w i at hincidence
      rw [hsum] at hincidence
      exfalso
      linarith
  have hdiag (i : Fin n) : Z i i = 0 := by simp [Z]
  have hsym (i j : Fin n) : Z i j = Z j i := by
    by_cases hij : i = j
    · simp [Z, hij]
    · simp only [Z, hij, Ne.symm hij, ite_false, FiniteArity.completeCharge,
        PhysicalRepresentative.adjacency_symm V m (cfg i) (cfg j),
        PhysicalRepresentative.charge_symm V m (cfg i) (cfg j), A, Y]
      congr 1
      exact propext (by tauto)
  have hentries (i : Fin n) (hi : i ∈ E) (j : Fin n) (_hj : j ∈ E) (hij : i ≠ j) :
      Z i j = S.coveredCountableBoundaryCoefficient (q i) (q j) := by
    simp only [Z, hij, ite_false, FiniteArity.completeCharge, hE' i hi,
      Set.mem_ofPred_eq, false_and, ite_false]
    exact (hp i j hij).2
  have hdisj : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    exact fun i hi he => hE' i he (hT i hi)
  have hcell (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ T) (hij : i ≠ j) :
      Z i j = -(-m) := by
    have hz := (hp i j hij).1
    rw [(hlabel i).mpr (hT i hi), (hlabel j).mpr (hT j hj)] at hz
    have hA : A (cfg i) (cfg j) = false := by
      simpa [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph] using hz
    simp [Z, hij, FiniteArity.completeCharge, hT i hi, hT j hj, hA]
  have hrow (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ E) : Z i j = w j := by
    have hij : i ≠ j := fun he => hE' j hj (he ▸ hT i hi)
    simp only [Z, hij, ite_false, FiniteArity.completeCharge, Set.mem_ofPred_eq,
      hE' j hj, and_false, false_and, ite_false]
    rw [(hp i j hij).2, (hlabel i).mpr (hT i hi)]
  have hformula := FiniteArity.pairCharge_homogeneous_cell T E hdisj Z hdiag hsym (-m) w hcell hrow
  change 1 < FiniteArity.pairCharge (T ∪ E) Z at hbad
  rw [hformula, hcard] at hbad
  norm_num at hbad
  refine ⟨n, E, q, Z, hdiag, hsym, hentries, ?_, ⟨b, hb, hbR, ?_⟩, hsmall, hclasses⟩
  · change 1 < FiniteArity.pairCharge E Z + 2 * (∑ i ∈ E, w i) + m
    linarith
  · exact fun i hi hiR => hunique hi hiR

end Erdos1017.CappedModel.SelectedHighLowStructure
