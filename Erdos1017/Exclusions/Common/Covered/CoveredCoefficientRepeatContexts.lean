module

public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientContextShape
public import Erdos1017.Exclusions.Common.Covered.CoveredEStar
public import Erdos1017.Exclusions.Common.Covered.CoveredPositiveContexts

/-!
# Repeat contexts of the exterior atoms

Every exterior atom has a two-copy threshold in the `B`, `BR` or `BE` context,
positive `R` and `E` force the bare-root context, so at most one exterior atom
exists when both diffuse regions are positive, and such an atom exhausts the
countable atom family.
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

/-- Every actual exterior atom has a genuine B, BR or BE two-copy
threshold. All coefficients are the literal original conditional means. -/
theorem coveredCoefficient_repeat_contexts (S : SelectedHighLowStructure W m) (r a u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) :
    let t := S.coveredCoefficient a (Sum.inl r) (Sum.inl u);
    -m < 2 * t - 1 ∨
      -m < 2 * t - 1 + S.coveredCoefficient a (Sum.inl r) (Sum.inr true) +
        2 * S.coveredCoefficient a (Sum.inl u) (Sum.inr true) ∨
      -m < 2 * t - 1 + S.coveredCoefficient a (Sum.inl r) (Sum.inr false) +
        2 * S.coveredCoefficient a (Sum.inl u) (Sum.inr false) := by
  obtain ⟨n, E, q, Z, hdiag, hsym, hentries, hbad, ⟨b, hb, hbR, hroot⟩, hsmall, hclasses⟩ :=
    S.exists_covered_coefficient_context r a u hW hd hgap hpair hzero hR hE hell hratio hru
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
    have hcharge : FiniteArity.pairCharge E Z =
        S.coveredCoefficient a (Sum.inl r) (Sum.inr flag) := by
      rw [hEeq]
      simp [FiniteArity.pairCharge, FiniteArity.crossSum, Ne.symm hjb, hdiag,
        ← hsym b j, hentries b hb j hj (Ne.symm hjb), hbR, hjflag]
    have hsum : (∑ i ∈ E, S.coveredCoefficient a (Sum.inl u) (q i)) =
        S.coveredCoefficient a (Sum.inl r) (Sum.inl u) +
        S.coveredCoefficient a (Sum.inl u) (Sum.inr flag) := by
      rw [hEeq]
      simp [Ne.symm hjb, hbR, hjflag, S.coveredCoefficient_symm a (Sum.inl u) (Sum.inl r)]
    rw [hcharge, hsum] at hbad
    cases flag
    · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
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
      S.coveredCoefficient_symm a (Sum.inl u) (Sum.inl r)] at hbad
    exact Or.inl (by linarith)

/-- Positive R/E forces every exterior repeat witness to be the bare
root context. The strict E-star and actual half-delta penalties are
proved internally from the same original optimum. -/
theorem coveredCoefficient_bare_repeat (S : SelectedHighLowStructure W m) (r a u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) (hau : a ≠ u) :
    -m < 2 * S.coveredCoefficient a (Sum.inl r) (Sum.inl u) - 1 := by
  have hBR : S.coveredGraph r a (Sum.inl r) (Sum.inr true) = true := by
    simp [coveredGraph]
  have hBE : S.coveredGraph r a (Sum.inl r) (Sum.inr false) = true := by
    simp [coveredGraph, hpair.1]
  have hBu : S.coveredGraph r a (Sum.inl r) (Sum.inl u) = true := by
    simp [coveredGraph, hru, hpair.1]
  have huR : S.coveredGraph r a (Sum.inl u) (Sum.inr true) = true := by
    simp [coveredGraph]
  have huE : S.coveredGraph r a (Sum.inl u) (Sum.inr false) = true := by
    simp [coveredGraph, Ne.symm hau]
  have hv := S.coveredCoefficient_root_E_gt r a hW hd hgap hpair hzero hR hE
  have hz := S.coveredCoefficient_penalty_gt_half_delta r a hW hd hgap hpair hzero hR hE hratio
    (Sum.inl u) (Sum.inr true) (by simp [Ne.symm hru]) (by simp) huR
  have hRtri := S.coveredCoefficient_triangle r a hW hd hgap hpair hzero hR hE
    (Sum.inl r) (Sum.inl u) (Sum.inr true) hBu hBR huR
  have hEtri := S.coveredCoefficient_triangle r a hW hd hgap hpair hzero hR hE
    (Sum.inl r) (Sum.inl u) (Sum.inr false) hBu hBE huE
  have hw := S.coveredCoefficient_repeat_contexts r a u hW hd hgap hpair hzero hR hE hell hratio hru
  apply CoveredRepeat.bare_witness_of_three_contexts
    (h := S.coveredCoefficient a (Sum.inl r) (Sum.inr true))
    (v := S.coveredCoefficient a (Sum.inl r) (Sum.inr false))
    (z := -S.coveredCoefficient a (Sum.inl u) (Sum.inr true))
    (d := -S.coveredCoefficient a (Sum.inl u) (Sum.inr false))
    hell hv (by linarith) (by linarith) (by linarith)
  simpa only [sub_neg_eq_add, mul_neg, neg_neg] using hw

/-- There is at most one exterior independent atom when both diffuse
regions are positive. This is derived before any finite-five realization. -/
theorem covered_exterior_unique (S : SelectedHighLowStructure W m) (r a u v : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hru : r ≠ u) (hau : a ≠ u) (hrv : r ≠ v) (hav : a ≠ v) : u = v := by
  by_contra huv
  have hfirst := S.coveredCoefficient_bare_repeat r a u hW hd hgap hpair hzero hR hE hell hratio hru hau
  have hsecond := S.coveredCoefficient_bare_repeat r a v hW hd hgap hpair hzero hR hE hell hratio hrv hav
  have hBu : S.coveredGraph r a (Sum.inl r) (Sum.inl u) = true := by
    simp [coveredGraph, hru, hpair.1]
  have hBv : S.coveredGraph r a (Sum.inl r) (Sum.inl v) = true := by
    simp [coveredGraph, hrv, hpair.1]
  have huvG : S.coveredGraph r a (Sum.inl u) (Sum.inl v) = true := by
    simp [coveredGraph, huv, Ne.symm hau, Ne.symm hav]
  have hjoint := S.coveredCoefficient_triangle r a hW hd hgap hpair hzero hR hE
    (Sum.inl r) (Sum.inl u) (Sum.inl v) hBu hBv huvG
  have hfloor := S.coveredCoefficient_present_gt_m r a hW hd hgap hpair hzero hR hE
    (Sum.inl u) (Sum.inl v) huvG
  have hp : -S.coveredCoefficient a (Sum.inl u) (Sum.inl v) < -m := by linarith
  exact CoveredRepeat.not_two_bare_witnesses hfirst hsecond (by linarith) hp.le

/-- Any actual exterior atom exhausts the remaining countable atom
family. This is the derived three-atom license for a finite-five model. -/
theorem covered_atoms_eq_three (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hrz : r ≠ z) (haz : a ≠ z) : ∀ u : S.I, u = r ∨ u = a ∨ u = z := by
  intro u
  by_cases hur : u = r
  · exact Or.inl hur
  by_cases hua : u = a
  · exact Or.inr (Or.inl hua)
  exact Or.inr (Or.inr (S.covered_exterior_unique r a u z hW hd hgap hpair hzero
    hR hE hell hratio (Ne.symm hur) (Ne.symm hua) hrz haz))

end Erdos1017.CappedModel.SelectedHighLowStructure
