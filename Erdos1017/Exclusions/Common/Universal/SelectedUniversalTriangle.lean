module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal

/-!
# Triangle inequality of a universal root

One root section of the product triangle test gives an almost-everywhere
inequality on exterior pairs, and whole-row homogeneity removes the dependence
on the chosen root.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- One actual root section of the original product triangle test gives
an AE inequality on exterior pairs. Whole-row homogeneity removes the
chosen root, so the result subsequently transfers to pair-AC parent laws. -/
theorem ae_universal_root_triangle (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      S.rootChargeRow r p.1 + S.rootChargeRow r p.2 +
        PhysicalRepresentative.charge W m p.1 p.2 ≤ 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := hW.strict_gap_structure hd hgap
  have htest := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic 3
  have hroot : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (A p.1 p.2 = true ↔ S.ρ p.2 ≠ r.val) ∧ Y p.1 p.2 = S.rootChargeRow r p.2 := by
    filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN,
      S.ae_root_charge r hW hd hgap] with p ha hy hx
    exact ⟨ha hx, hy hx⟩
  have hsections := FiniteArity.ae_root_sections μ 2 _ htest
  obtain ⟨x, hx, hrow, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hroot)).and
      (ae_restrict_of_ae hsections))
  have hpairTest : ∀ᵐ p ∂μ.prod μ, FiniteArity.TupleClique A ![x, p.1, p.2] →
      FiniteArity.tupleCharge Y ![x, p.1, p.2] ≤ 1 := by
    have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
      (measurePreserving_finTwoArrow μ)
    have hvec (p : Ω × Ω) :
        Fin.cons x ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) = ![x, p.1, p.2] := by
      ext i
      fin_cases i <;> rfl
    filter_upwards [hmp.quasiMeasurePreserving.ae hsection] with p hp
    simpa only [hvec] using hp
  filter_upwards [hpairTest, Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow] with p ht hy hz hp1 hp2 hpA
  have hxy := (hy hx).1.mpr hp1
  have hxz := (hz hx).1.mpr hp2
  have hyx : A p.1 x = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hxy
  have hzx : A p.2 x = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hxz
  have hzy : A p.2 p.1 = true := by simpa [A, PhysicalRepresentative.adjacency_symm] using hpA
  have hclique : FiniteArity.TupleClique A ![x, p.1, p.2] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at * <;>
      first | exact hxy | exact hxz | exact hyx | exact hpA | exact hzx | exact hzy
  have hbound := ht hclique
  rw [tupleCharge_three Y x p.1 p.2 (PhysicalRepresentative.charge_symm W m),
    (hy hx).2, (hz hx).2] at hbound
  exact hbound

end Erdos1017.CappedModel.SelectedHighLowStructure
