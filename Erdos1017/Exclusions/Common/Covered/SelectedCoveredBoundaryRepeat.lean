module

public import Erdos1017.Exclusions.Common.Covered.CoveredBoundaryContextShape

/-!
# Repeat contexts on the null-region boundaries

On either null-region boundary the only repeat contexts are the bare root and
`BD`, two exterior atoms exhaust all remaining atoms, and so the whole countable
family has at most two exterior labels.
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

/-- Both null-region boundaries have only the genuine bare-root or BD
repeat contexts, with the literal original conditional coefficients. -/
theorem covered_boundary_repeat_contexts (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a u : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) :
    let t := S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u);
    -m < 2 * t - 1 ∨ -m < 2 * t - 1 +
      S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inr ()) +
        2 * S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inr ()) := by
  obtain ⟨n, E, q, Z, hdiag, hsym, hentries, hbad, ⟨b, hb, hbR, hroot⟩, hsmall, hclasses⟩ :=
    S.exists_covered_boundary_coefficient_context mode r a u hW hd hgap hpair hzero
      hD hnull hell hratio hru
  dsimp only
  by_cases hex : ∃ j ∈ E, q j ≠ Sum.inl r
  · obtain ⟨j, hj, hjR⟩ := hex
    have hjb : j ≠ b := fun he => hjR (he ▸ hbR)
    have hEeq : E = {b, j} := by
      ext i
      constructor
      · intro hi
        by_cases hiR : q i = Sum.inl r
        · simp [hroot i hi hiR]
        · have he := Finset.card_le_one.mp hsmall i (Finset.mem_filter.mpr ⟨hi, hiR⟩)
            j (Finset.mem_filter.mpr ⟨hj, hjR⟩)
          simp [he]
      · intro hi
        rcases Finset.mem_insert.mp hi with he | he
        · exact he ▸ hb
        · exact (Finset.mem_singleton.mp he) ▸ hj
    obtain ⟨flag, hjflag⟩ := (hclasses j hj).resolve_left hjR
    cases flag
    have hcharge : FiniteArity.pairCharge E Z =
        S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inr ()) := by
      rw [hEeq]
      simp [FiniteArity.pairCharge, FiniteArity.crossSum, Ne.symm hjb, hdiag,
        ← hsym b j, hentries b hb j hj (Ne.symm hjb), hbR, hjflag]
    have hsum : (∑ i ∈ E, S.coveredCountableBoundaryCoefficient (Sum.inl u) (q i)) =
        S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) +
        S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inr ()) := by
      rw [hEeq]
      simp [Ne.symm hjb, hbR, hjflag,
        S.coveredCountableBoundaryCoefficient_symm (Sum.inl u) (Sum.inl r)]
    rw [hcharge, hsum] at hbad
    exact Or.inr (by linarith)
  · have hEeq : E = {b} := by
      ext i
      constructor
      · intro hi
        exact Finset.mem_singleton.mpr (hroot i hi (by by_contra hn; exact hex ⟨i, hi, hn⟩))
      · intro hi
        exact (Finset.mem_singleton.mp hi) ▸ hb
    have hcharge : FiniteArity.pairCharge E Z = 0 := by
      simp [hEeq, FiniteArity.pairCharge, FiniteArity.crossSum, hdiag]
    rw [hEeq] at hbad
    simp only [Finset.sum_singleton] at hbad
    rw [show FiniteArity.pairCharge {b} Z = 0 from hEeq ▸ hcharge, hbR,
      S.coveredCountableBoundaryCoefficient_symm (Sum.inl u) (Sum.inl r)] at hbad
    exact Or.inl (by linarith)

/-- Two genuine exterior atoms exhaust all remaining atoms in either
null-region boundary. Both context types are derived internally, and
actual joint triangle/four-label tests forbid repetition of either type. -/
theorem covered_boundary_atoms_eq_four (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a u v : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) (hau : a ≠ u) (hrv : r ≠ v) (hav : a ≠ v) (huv : u ≠ v) :
    ∀ w : S.I, w = r ∨ w = a ∨ w = u ∨ w = v := by
  let ξ := S.coveredCountableBoundaryCoefficient
  let bare := fun z : S.I => -m < 2 * ξ (Sum.inl r) (Sum.inl z) - 1
  let diffuse := fun z : S.I => -m < 2 * ξ (Sum.inl r) (Sum.inl z) - 1 +
    ξ (Sum.inl r) (Sum.inr ()) + 2 * ξ (Sum.inl z) (Sum.inr ())
  have hcontexts (z : S.I) (hrz : r ≠ z) : bare z ∨ diffuse z :=
    S.covered_boundary_repeat_contexts mode r a z hW hd hgap hpair hzero hD hnull hell hratio hrz
  have hsame (z w : S.I) (hrz : r ≠ z) (haz : a ≠ z) (hrw : r ≠ w) (haw : a ≠ w)
      (hzw : z ≠ w) : ¬(bare z ∧ bare w) ∧ ¬(diffuse z ∧ diffuse w) := by
    have hBz : S.coveredCountableBoundaryGraph mode r a (Sum.inl r) (Sum.inl z) = true := by
      simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph, hrz, hpair.1]
    have hBw : S.coveredCountableBoundaryGraph mode r a (Sum.inl r) (Sum.inl w) = true := by
      simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph, hrw, hpair.1]
    have hzwG : S.coveredCountableBoundaryGraph mode r a (Sum.inl z) (Sum.inl w) = true := by
      simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph,
        hzw, Ne.symm haz, Ne.symm haw]
    have htri := S.coveredCountableBoundaryCoefficient_triangle mode r a hW hd hgap hpair
      hzero hD hnull (Sum.inl r) (Sum.inl z) (Sum.inl w) hBz hBw hzwG
    have hfloor := S.coveredCountableBoundaryCoefficient_present_gt_m mode r a hW hd hgap
      hpair hzero hD hnull (Sum.inl z) (Sum.inl w) hzwG
    have hclique : FiniteArity.TupleClique (S.coveredCountableBoundaryGraph mode r a)
        ![Sum.inl r, Sum.inl z, Sum.inl w, Sum.inr ()] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at * <;>
        simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph,
          hrz, hrw, hzw, Ne.symm hrz, Ne.symm hrw, Ne.symm hzw,
          Ne.symm haz, Ne.symm haw, hpair.1]
    have ht := S.coveredCountableBoundaryCoefficient_tuple_le_one mode r a hW hd hgap hpair
      hzero hD hnull ![Sum.inl r, Sum.inl z, Sum.inl w, Sum.inr ()] hclique
    have heq : FiniteArity.tupleCharge ξ ![Sum.inl r, Sum.inl z, Sum.inl w, Sum.inr ()] =
        ξ (Sum.inl r) (Sum.inl z) + ξ (Sum.inl r) (Sum.inl w) +
          ξ (Sum.inl r) (Sum.inr ()) + ξ (Sum.inl z) (Sum.inl w) +
          ξ (Sum.inl z) (Sum.inr ()) + ξ (Sum.inl w) (Sum.inr ()) := by
      simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
        Fin.sum_univ_succ, ξ, S.coveredCountableBoundaryCoefficient_symm (Sum.inl z) (Sum.inl r),
        S.coveredCountableBoundaryCoefficient_symm (Sum.inl w) (Sum.inl r),
        S.coveredCountableBoundaryCoefficient_symm (Sum.inr ()) (Sum.inl r),
        S.coveredCountableBoundaryCoefficient_symm (Sum.inl w) (Sum.inl z),
        S.coveredCountableBoundaryCoefficient_symm (Sum.inr ()) (Sum.inl z),
        S.coveredCountableBoundaryCoefficient_symm (Sum.inr ()) (Sum.inl w)]
      ring
    change FiniteArity.tupleCharge ξ _ ≤ 1 at ht
    rw [heq] at ht
    change ξ (Sum.inl r) (Sum.inl z) + ξ (Sum.inl r) (Sum.inl w) +
      ξ (Sum.inl z) (Sum.inl w) ≤ 1 at htri
    change m < ξ (Sum.inl z) (Sum.inl w) at hfloor
    constructor
    · rintro ⟨hz, hw⟩
      dsimp [bare] at hz hw
      linarith
    · rintro ⟨hz, hw⟩
      dsimp [diffuse] at hz hw
      linarith
  have hpaircontexts := hsame u v hru hau hrv hav huv
  intro w
  by_cases hwr : w = r
  · exact Or.inl hwr
  by_cases hwa : w = a
  · exact Or.inr (Or.inl hwa)
  by_cases hwu : w = u
  · exact Or.inr (Or.inr (Or.inl hwu))
  by_cases hwv : w = v
  · exact Or.inr (Or.inr (Or.inr hwv))
  exfalso
  have hwucontexts := hsame w u (Ne.symm hwr) (Ne.symm hwa) hru hau hwu
  have hwvcontexts := hsame w v (Ne.symm hwr) (Ne.symm hwa) hrv hav hwv
  rcases hcontexts u hru with hu | hu <;>
    rcases hcontexts v hrv with hv | hv <;>
    rcases hcontexts w (Ne.symm hwr) with hw | hw
  · exact hpaircontexts.1 ⟨hu, hv⟩
  · exact hpaircontexts.1 ⟨hu, hv⟩
  · exact hwucontexts.1 ⟨hw, hu⟩
  · exact hwvcontexts.2 ⟨hw, hv⟩
  · exact hwvcontexts.1 ⟨hw, hv⟩
  · exact hwucontexts.2 ⟨hw, hu⟩
  · exact hpaircontexts.2 ⟨hu, hv⟩
  · exact hpaircontexts.2 ⟨hu, hv⟩

/-- The entire countable family has at most two exterior labels. The
chosen labels may repeat or equal a head when fewer exterior atoms exist. -/
theorem exists_covered_boundary_two_label_cover (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    ∃ u v : S.I, ∀ w : S.I, w = r ∨ w = a ∨ w = u ∨ w = v := by
  by_cases hfirst : ∃ u : S.I, u ≠ r ∧ u ≠ a
  · obtain ⟨u, hur, hua⟩ := hfirst
    by_cases hsecond : ∃ v : S.I, v ≠ r ∧ v ≠ a ∧ v ≠ u
    · obtain ⟨v, hvr, hva, hvu⟩ := hsecond
      exact ⟨u, v, S.covered_boundary_atoms_eq_four mode r a u v hW hd hgap hpair hzero
        hD hnull hell hratio (Ne.symm hur) (Ne.symm hua) (Ne.symm hvr) (Ne.symm hva)
        (Ne.symm hvu)⟩
    · refine ⟨u, u, ?_⟩
      intro w
      by_cases hwr : w = r
      · exact Or.inl hwr
      by_cases hwa : w = a
      · exact Or.inr (Or.inl hwa)
      have hwu : w = u := by by_contra hn; exact hsecond ⟨w, hwr, hwa, hn⟩
      exact Or.inr (Or.inr (Or.inl hwu))
  · refine ⟨r, a, ?_⟩
    intro w
    by_cases hwr : w = r
    · exact Or.inl hwr
    have hwa : w = a := by by_contra hn; exact hfirst ⟨w, hwr, hn⟩
    exact Or.inr (Or.inl hwa)

end Erdos1017.CappedModel.SelectedHighLowStructure
