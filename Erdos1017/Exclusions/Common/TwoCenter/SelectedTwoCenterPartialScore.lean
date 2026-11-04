module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurEnergy
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative

/-!
# Triangle score outside the plateau heads

Every original vertex outside the high region and the two plateau heads pays the
triangle score of the two positive heads, almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- Every original vertex outside HIGH and the two plateau heads pays the
triangle score of the two actual positive heads. -/
theorem ae_head_deficit_floor_on_plateauOther (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    ∀ᵐ x ∂μ.restrict R.plateauOther,
      2 * S.headPairing r u - 1 + 3 * m ≤
        S.headPairing r u - r.val x - u.val x := by
  let κ := S.headPairing r u
  have hs := hW.strict_gap_structure hd hgap
  have hκ : 0 < κ := by
    have hν := hs.stationary_pos
    have hbound := R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept
    dsimp only [κ]
    linarith
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let O : Set Ω := R.plateauOther
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hO : MeasurableSet O := S.hpartition.1.compl.diff R.measurableSet_plateauRegion
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hIupos : 0 < μ Iu := (S.hfibers u.val u.property).2.1
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n :=
    PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  have hphysA := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hphysY := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
  obtain ⟨q, _, hq, hblock⟩ := S.exists_original_head_block r u hW
  have hqpos : 0 < q := hq ▸ hκ
  have hru : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iu →
      A p.1 p.2 = true ∧ Y p.1 p.2 = κ + m := by
    rw [Measure.prod_restrict] at hblock
    have hraw := (ae_restrict_iff' (hIr.prod hIu)).mp hblock
    filter_upwards [hraw, hphysA, hphysY] with p hb ha hy hr hu
    have hb' := hb ⟨hr, hu⟩
    have hAdj : adjacencyKernel W p.1 p.2 = 1 := by simpa [hqpos] using hb'.2.1
    have hA : A p.1 p.2 = true := by
      by_contra hn
      have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
      change adjacencyKernel W p.1 p.2 =
        (if A p.1 p.2 = true then (1 : ℝ) else 0) at ha
      rw [hf] at ha
      norm_num at ha
      linarith
    refine ⟨hA, ?_⟩
    change PhysicalRepresentative.charge W m p.1 p.2 = κ + m
    rw [hy]
    simpa [hqpos, κ, hq] using hb'.2.2
  have hrmem : r ∈ R.plateau := by rw [hp]; simp
  have humem : u ∈ R.plateau := by rw [hp]; simp
  have hro : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ O →
      A p.1 p.2 = true ∧ Y p.1 p.2 = r.val p.2 + m := by
    filter_upwards [R.plateau_head_joined_half r hrmem hW hd hgap,
      S.ae_kernel_eq_fiber_row r.val r.property,
      hphysA, hphysY] with p hAdj hrow ha hy hr ho
    have hoH : p.2 ∉ S.H := ho.1
    have hone : S.ρ p.2 ≠ r.val := by
      intro h
      exact ho.2 (by rw [R.plateauRegion_eq_pair r u hp]; exact Or.inl h)
    have hG := hAdj hr hoH hone
    have hA : A p.1 p.2 = true := by
      by_contra hn
      have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
      change adjacencyKernel W p.1 p.2 =
        (if A p.1 p.2 = true then (1 : ℝ) else 0) at ha
      rw [hf] at ha
      norm_num at ha
      linarith
    refine ⟨hA, ?_⟩
    have hK := hrow hr
    change PhysicalRepresentative.charge W m p.1 p.2 = r.val p.2 + m
    rw [hy]
    rw [shiftedKernel, shiftedMoment_eq] at hK
    change chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 =
      r.val p.2 at hK
    rw [hG] at hK
    linarith
  have huo : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Iu → p.2 ∈ O →
      A p.1 p.2 = true ∧ Y p.1 p.2 = u.val p.2 + m := by
    filter_upwards [R.plateau_head_joined_half u humem hW hd hgap,
      S.ae_kernel_eq_fiber_row u.val u.property,
      hphysA, hphysY] with p hAdj hrow ha hy hu ho
    have hoH : p.2 ∉ S.H := ho.1
    have hone : S.ρ p.2 ≠ u.val := by
      intro h
      exact ho.2 (by rw [R.plateauRegion_eq_pair r u hp]; exact Or.inr h)
    have hG := hAdj hu hoH hone
    have hA : A p.1 p.2 = true := by
      by_contra hn
      have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
      change adjacencyKernel W p.1 p.2 =
        (if A p.1 p.2 = true then (1 : ℝ) else 0) at ha
      rw [hf] at ha
      norm_num at ha
      linarith
    refine ⟨hA, ?_⟩
    have hK := hrow hu
    change PhysicalRepresentative.charge W m p.1 p.2 = u.val p.2 + m
    rw [hy]
    rw [shiftedKernel, shiftedMoment_eq] at hK
    change chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 =
      u.val p.2 at hK
    rw [hG] at hK
    linarith
  let E : Set Ω := O ∩ {x | 1 - κ - r.val x - u.val x < 3 * m}
  have hE : MeasurableSet E := hO.inter
    (measurableSet_lt
      ((measurable_const.sub (Lp.stronglyMeasurable r.val).measurable).sub
        (Lp.stronglyMeasurable u.val).measurable) measurable_const)
  have hEzero : μ E = 0 := by
    by_contra hn
    have hEpos : 0 < μ E := lt_of_le_of_ne (zero_le : (0 : ENNReal) ≤ μ E) (Ne.symm hn)
    let P : (Fin 3 → Ω) → Prop := fun w =>
        (FiniteArity.TupleClique A w → FiniteArity.tupleCharge Y w ≤ 1) ∧
        ∀ i j : Fin 3, i ≠ j →
          (w i ∈ Ir → w j ∈ Iu → A (w i) (w j) = true ∧ Y (w i) (w j) = κ + m) ∧
          (w i ∈ Ir → w j ∈ E → A (w i) (w j) = true ∧ Y (w i) (w j) = r.val (w j) + m) ∧
          (w i ∈ Iu → w j ∈ E → A (w i) (w j) = true ∧ Y (w i) (w j) = u.val (w j) + m)
    have htrip : ∀ᵐ w ∂Measure.pi (fun _ : Fin 3 => μ), P w := by
      have he : E ⊆ O := fun _ hx => hx.1
      have hpair := hru.and ((hro.mono fun _ hp hi hj => hp hi (he hj)).and
        (huo.mono fun _ hp hi hj => hp hi (he hj)))
      exact (hfull 3).and (FiniteArity.ae_all_pairs μ 3 _ hpair)
    have hroot := FiniteArity.ae_root_sections μ 2 _ htrip
    obtain ⟨x, hx, hxroot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIrpos.ne' (ae_restrict_of_ae hroot)
    have hsection : ∀ᵐ p ∂μ.prod μ, P ![x, p.1, p.2] := by
      have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
        (measurePreserving_finTwoArrow μ)
      have hvec (p : Ω × Ω) :
          Fin.cons x ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) =
            ![x, p.1, p.2] := by
        ext i
        fin_cases i <;> rfl
      filter_upwards [hmp.quasiMeasurePreserving.ae hxroot] with p hp
      simpa only [hvec] using hp
    have hys := Measure.ae_ae_of_ae_prod hsection
    obtain ⟨y, hy, hysection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIupos.ne' (ae_restrict_of_ae hys)
    obtain ⟨z, hz, ht⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hEpos.ne' (ae_restrict_of_ae hysection)
    have hxy := ht.2 0 1 (by decide)
    have hxz := ht.2 0 2 (by decide)
    have hyz := ht.2 1 2 (by decide)
    have hAxy : A x y = true := (hxy.1 hx hy).1
    have hAxz : A x z = true := (hxz.2.1 hx hz).1
    have hAyz : A y z = true := (hyz.2.2 hy hz).1
    have hAyx : A y x = true := (PhysicalRepresentative.adjacency_symm W m x y).symm.trans hAxy
    have hAzx : A z x = true := (PhysicalRepresentative.adjacency_symm W m x z).symm.trans hAxz
    have hAzy : A z y = true := (PhysicalRepresentative.adjacency_symm W m y z).symm.trans hAyz
    have hclique : FiniteArity.TupleClique A ![x, y, z] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp <;>
        first | exact hAxy | exact hAyx | exact hAxz | exact hAyz |
          exact hAzx | exact hAzy | exact False.elim (hij rfl)
    have hbound := ht.1 hclique
    have hcharge : FiniteArity.tupleCharge Y ![x, y, z] =
        Y x y + Y x z + Y y z := by
      simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
        FiniteArity.crossSum, Fin.sum_univ_succ]
      have hxy : Y x y = Y y x := PhysicalRepresentative.charge_symm W m x y
      have hxz : Y x z = Y z x := PhysicalRepresentative.charge_symm W m x z
      have hyz : Y y z = Y z y := PhysicalRepresentative.charge_symm W m y z
      rw [← hxy, ← hxz, ← hyz]
      ring
    rw [hcharge] at hbound
    have hYxy : Y x y = κ + m := (hxy.1 hx hy).2
    have hYxz : Y x z = r.val z + m := (hxz.2.1 hx hz).2
    have hYyz : Y y z = u.val z + m := (hyz.2.2 hy hz).2
    have hbad := hz.2
    change 1 - κ - r.val z - u.val z < 3 * m at hbad
    linarith
  have hraw : ∀ᵐ x ∂μ, x ∈ O →
      2 * κ - 1 + 3 * m ≤ κ - r.val x - u.val x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp hEzero
    filter_upwards [hnot] with x hx ho
    have hn : x ∉ E := hx
    have : ¬ 1 - κ - r.val x - u.val x < 3 * m := by
      intro h
      exact hn ⟨ho, h⟩
    linarith
  exact (ae_restrict_iff' hO).mpr hraw

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
