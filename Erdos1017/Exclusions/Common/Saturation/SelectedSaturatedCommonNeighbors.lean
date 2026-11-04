module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy

/-!
# Score cap on common neighbors of a saturated pair

A saturated atom pair bounds its shifted score on almost all common neighbors by
the remaining triangle budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hxy : Y x y = Y y x) (hxz : Y x z = Y z x)
    (hyz : Y y z = Y z y) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hxy, hxz, hyz]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- The same original saturated pair bounds its shifted score on almost
all common neighbors by the remaining triangle budget. -/
theorem IsSaturatedAtomPair.ae_common_neighbor_score_le
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, 0 < r.val x → 0 < u.val x → r.val x + u.val x ≤ -2 * m := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hIupos : 0 < μ Iu := (S.hfibers u.val u.property).2.1
  have hs := hW.strict_gap_structure hd hgap
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  let row (q : S.I) (z : Ω) : ℝ := q.val z
  let indicator (q : S.I) (z : Ω) : ℝ := if 0 < row q z then 1 else 0
  have hrows (q : S.I) : ∀ᵐ x ∂μ.restrict {x | S.ρ x = q.val},
      (adjacencyKernel W x =ᵐ[μ] indicator q) ∧
      (chargeKernel W x =ᵐ[μ] fun z => row q z + m * indicator q z) := by
    simpa only [row, indicator] using
      ((S.hfibers q.val q.property).2.2.2.rows.mono (fun _ hx => hx.2))
  have hevent : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ Ir → p.2 ∈ Iu → chargeKernel W p.1 p.2 = 1) ∧
      Y p.1 p.2 = chargeKernel W p.1 p.2 ∧
      adjacencyKernel W p.1 p.2 = (if A p.1 p.2 = true then 1 else 0) := by
    filter_upwards [hpair.2, PhysicalRepresentative.charge_ae_eq W m hs.strict_support,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support]
      with p hsat hpY hpA
    exact ⟨hsat, hpY, hpA⟩
  have htest : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1 := hfull 3
  have htrip : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      (FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) ∧
      ∀ i j, i ≠ j →
        (v i ∈ Ir → v j ∈ Iu → chargeKernel W (v i) (v j) = 1) ∧
        Y (v i) (v j) = chargeKernel W (v i) (v j) ∧
        adjacencyKernel W (v i) (v j) =
          (if A (v i) (v j) = true then 1 else 0) :=
    htest.and (FiniteArity.ae_all_pairs μ 3 _ hevent)
  have hroot := FiniteArity.ae_root_sections μ 2 _ htrip
  have hpairx := Measure.ae_ae_of_ae_prod hevent
  obtain ⟨x, hxIr, hxrows, hxroot, hxpair⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      ((hrows r).and ((ae_restrict_of_ae hroot).and (ae_restrict_of_ae hpairx)))
  have hpairSection : ∀ᵐ p ∂μ.prod μ,
      (FiniteArity.TupleClique A ![x, p.1, p.2] →
        FiniteArity.tupleCharge Y ![x, p.1, p.2] ≤ 1) ∧
      ∀ i j, i ≠ j →
        (![x, p.1, p.2] i ∈ Ir → ![x, p.1, p.2] j ∈ Iu →
          chargeKernel W (![x, p.1, p.2] i) (![x, p.1, p.2] j) = 1) ∧
        Y (![x, p.1, p.2] i) (![x, p.1, p.2] j) =
          chargeKernel W (![x, p.1, p.2] i) (![x, p.1, p.2] j) ∧
        adjacencyKernel W (![x, p.1, p.2] i) (![x, p.1, p.2] j) =
          (if A (![x, p.1, p.2] i) (![x, p.1, p.2] j) = true then 1 else 0) := by
    have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
      (measurePreserving_finTwoArrow μ)
    have hvec (p : Ω × Ω) :
        Fin.cons x ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) =
          ![x, p.1, p.2] := by
      ext i
      fin_cases i <;> rfl
    filter_upwards [hmp.quasiMeasurePreserving.ae hxroot] with p hp
    simpa only [hvec] using hp
  have hyu := Measure.ae_ae_of_ae_prod hpairSection
  obtain ⟨y, hyIu, hyrows, hysection, hxy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIupos.ne'
      ((hrows u).and ((ae_restrict_of_ae hyu).and (ae_restrict_of_ae hxpair)))
  filter_upwards [hxrows.1, hxrows.2, hyrows.1, hyrows.2, hysection]
    with z hAxz hYxz hAyz hYyz htr hrz huz
  change 0 < row r z at hrz
  change 0 < row u z at huz
  have hxy' := hxy.1 hxIr hyIu
  have hxyY : Y x y = 1 := (hxy.2.1).trans hxy'
  have hxyA : A x y = true := by
    by_contra hn
    have hf : A x y = false := Bool.eq_false_iff.mpr hn
    have hz := PhysicalRepresentative.charge_zero_of_nonedge W m x y hf
    linarith
  have hxz := htr.2 0 2 (by decide)
  have hyz := htr.2 1 2 (by decide)
  have hphys_xz : Y x z = chargeKernel W x z := by simpa using hxz.2.1
  have hphys_yz : Y y z = chargeKernel W y z := by simpa using hyz.2.1
  have hAx : A x z = true := by
    have h := hxz.2.2
    change adjacencyKernel W x z =
      (if A x z = true then (1 : ℝ) else 0) at h
    rw [hAxz] at h
    simp [indicator, hrz] at h
    by_contra hn
    have hf : A x z = false := Bool.eq_false_iff.mpr hn
    simp [hf] at h
  have hAy : A y z = true := by
    have h := hyz.2.2
    change adjacencyKernel W y z =
      (if A y z = true then (1 : ℝ) else 0) at h
    rw [hAyz] at h
    simp [indicator, huz] at h
    by_contra hn
    have hf : A y z = false := Bool.eq_false_iff.mpr hn
    simp [hf] at h
  have hAyX : A y x = true := by
    simpa [A, PhysicalRepresentative.adjacency_symm] using hxyA
  have hAzX : A z x = true := by
    simpa [A, PhysicalRepresentative.adjacency_symm] using hAx
  have hAzY : A z y = true := by
    simpa [A, PhysicalRepresentative.adjacency_symm] using hAy
  have hclique : FiniteArity.TupleClique A ![x, y, z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact hxyA | exact hAyX | exact hAx | exact hAy | exact hAzX |
        exact hAzY | exact False.elim (hij rfl)
  have hbound := htr.1 hclique
  rw [tupleCharge_three Y x y z (PhysicalRepresentative.charge_symm W m x y)
    (PhysicalRepresentative.charge_symm W m x z)
    (PhysicalRepresentative.charge_symm W m y z)] at hbound
  have hYx : Y x z = row r z + m := by
    rw [hphys_xz, hYxz]
    simp [indicator, hrz]
  have hYy : Y y z = row u z + m := by
    rw [hphys_yz, hYyz]
    simp [indicator, huz]
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
