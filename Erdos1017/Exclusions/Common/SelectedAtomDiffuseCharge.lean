module

public import Erdos1017.Exclusions.Common.SelectedRootRows

/-!
# Charge of a whole atom on diffuse points

A whole atom charges an adjacent diffuse point at most half the remaining
triangle budget, and in particular strictly less than one, with the root sampled
from its positive-measure fiber.
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

/-- A whole atom can charge an adjacent diffuse point at most half the
remaining triangle budget. The root is sampled from its positive-measure
fiber; no exceptional physical representative is selected. -/
theorem charge_le_half_one_sub_multiplier_on_atom_diffuse
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (r : S.I) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.D →
      chargeKernel W p.1 p.2 ≤ (1 - m) / 2 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I : Set Ω := {x | S.ρ x = r.val}
  let N := S.rootNeighborhood r
  let f := S.rootChargeRow r
  let B : Set Ω := {y | y ∈ S.D ∧ y ∈ N ∧ (1 - m) / 2 < f y}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hIpos : 0 < μ I := (S.hfibers r.val r.property).2.1
  have hB : MeasurableSet B := by
    have h : MeasurableSet (S.D ∩ N ∩ {y | (1 - m) / 2 < f y}) :=
      (S.hD.inter (S.measurableSet_rootNeighborhood r)).inter
        (measurableSet_lt measurable_const (S.measurable_rootChargeRow r))
    convert h using 1
    ext y
    simp only [B, N, f, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  have hs := hW.strict_gap_structure hd hgap
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  have hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D → m ≤ Y p.1 p.2 := by
    filter_upwards [S.hDcomplete, hW.moment_mem,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hA hK hY hx hy
    change m ≤ PhysicalRepresentative.charge W m p.1 p.2
    rw [hY]
    have hA' := hA hx hy
    rw [shiftedMoment_eq] at hK
    change m ≤ W.moment CappedColor.charge p
    rw [hA'] at hK
    nlinarith [hK.1]
  have hcomplete : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      A p.1 p.2 = true := by
    filter_upwards [S.hDcomplete,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support] with p hp hA hx hy
    have h := hp hx hy
    rw [hA] at h
    by_contra hn
    have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
    change (if A p.1 p.2 = true then (1 : ℝ) else 0) = 1 at h
    simp [hf] at h
  have hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I →
      (A p.1 p.2 = true ↔ p.2 ∈ N) ∧ Y p.1 p.2 = f p.2 := by
    filter_upwards [S.ae_root_adjacency r hW hd hgap,
      S.ae_root_charge r hW hd hgap] with p ha hy hi
    exact ⟨ha hi, hy hi⟩
  have htriple : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1 := hfull 3
  have hpair : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      (∀ i j, i ≠ j →
        (v i ∈ I → (A (v i) (v j) = true ↔ v j ∈ N) ∧ Y (v i) (v j) = f (v j))) ∧
      (∀ i j, i ≠ j → v i ∈ S.D → v j ∈ S.D →
        A (v i) (v j) = true ∧ m ≤ Y (v i) (v j)) := by
    have hd : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
        A p.1 p.2 = true ∧ m ≤ Y p.1 p.2 := by
      filter_upwards [hcomplete, hfloor] with p hc hf hi hj
      exact ⟨hc hi hj, hf hi hj⟩
    filter_upwards [FiniteArity.ae_all_pairs μ 3 _ hroot,
      FiniteArity.ae_all_pairs μ 3 _ hd] with v hr hdiff
    exact ⟨fun i j hij hi => hr i j hij hi,
      fun i j hij hi hj => hdiff i j hij hi hj⟩
  have hbad : μ B = 0 := by
    by_contra hne
    have hBpos : 0 < μ B := pos_iff_ne_zero.mpr hne
    have hsection := FiniteArity.ae_root_sections μ 2 _ (htriple.and hpair)
    obtain ⟨x, hxI, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hIpos.ne'
      (ae_restrict_of_ae hsection)
    have hpairSection : ∀ᵐ p ∂μ.prod μ,
        (FiniteArity.TupleClique A ![x, p.1, p.2] →
          FiniteArity.tupleCharge Y ![x, p.1, p.2] ≤ 1) ∧
        (∀ i j, i ≠ j →
          (![x, p.1, p.2] i ∈ I →
            (A (![x, p.1, p.2] i) (![x, p.1, p.2] j) = true ↔
              ![x, p.1, p.2] j ∈ N) ∧
            Y (![x, p.1, p.2] i) (![x, p.1, p.2] j) =
              f (![x, p.1, p.2] j))) ∧
        (∀ i j, i ≠ j → ![x, p.1, p.2] i ∈ S.D →
          ![x, p.1, p.2] j ∈ S.D →
          A (![x, p.1, p.2] i) (![x, p.1, p.2] j) = true ∧
            m ≤ Y (![x, p.1, p.2] i) (![x, p.1, p.2] j)) := by
      have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
        (measurePreserving_finTwoArrow μ)
      have hvec (p : Ω × Ω) :
          Fin.cons x ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) =
            ![x, p.1, p.2] := by
        ext i
        fin_cases i <;> rfl
      filter_upwards [hmp.quasiMeasurePreserving.ae hx] with p hp
      simpa only [hvec] using hp
    obtain ⟨y, hyB, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hBpos.ne'
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpairSection))
    obtain ⟨z, hzB, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hBpos.ne'
      (ae_restrict_of_ae hy)
    have hyN : y ∈ N := hyB.2.1
    have hzN : z ∈ N := hzB.2.1
    have hxy := (hz.2.1 0 1 (by decide) (by simpa using hxI)).1.mpr hyN
    have hxz := (hz.2.1 0 2 (by decide) (by simpa using hxI)).1.mpr hzN
    have hyz := (hz.2.2 1 2 (by decide) hyB.1 hzB.1).1
    have hzy := (hz.2.2 2 1 (by decide) hzB.1 hyB.1).1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hxy hxz hyz hzy
    have hyx : A y x = true := by
      simpa [A, PhysicalRepresentative.adjacency_symm] using hxy
    have hzx : A z x = true := by
      simpa [A, PhysicalRepresentative.adjacency_symm] using hxz
    have hclique : FiniteArity.TupleClique A ![x, y, z] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp at * <;>
        first | exact hxy | exact hxz | exact hyx | exact hyz | exact hzx | exact hzy
    have hbound := hz.1 hclique
    have hxyY := (hz.2.1 0 1 (by decide) (by simpa using hxI)).2
    have hxzY := (hz.2.1 0 2 (by decide) (by simpa using hxI)).2
    have hfloor' := (hz.2.2 1 2 (by decide) hyB.1 hzB.1).2
    have hxyY' : Y x y = f y := by simpa using hxyY
    have hxzY' : Y x z = f z := by simpa using hxzY
    have hfloor'' : m ≤ Y y z := by simpa using hfloor'
    rw [tupleCharge_three Y x y z (PhysicalRepresentative.charge_symm W m x y)
      (PhysicalRepresentative.charge_symm W m x z)
      (PhysicalRepresentative.charge_symm W m y z)] at hbound
    have hylarge := hyB.2.2
    have hzlarge := hzB.2.2
    linarith
  have hrowcap : ∀ᵐ y ∂μ, y ∈ S.D → y ∈ N → f y ≤ (1 - m) / 2 := by
    rw [ae_iff]
    have hsub : {y | ¬(y ∈ S.D → y ∈ N → f y ≤ (1 - m) / 2)} ⊆ B := by
      intro y hy
      simp only [not_forall, not_le] at hy
      exact ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec⟩
    exact (measure_mono_null hsub hbad)
  filter_upwards [S.ae_root_charge r hW hd hgap,
    S.ae_root_adjacency r hW hd hgap,
    Measure.quasiMeasurePreserving_snd.ae hrowcap,
    PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hpY hpA hcap hphys hx hy
  by_cases hn : p.2 ∈ N
  · rw [← hphys, hpY hx]
    exact hcap hy hn
  · have hfalse : A p.1 p.2 = false := by
      cases h : A p.1 p.2 with
      | false => rfl
      | true => exact False.elim (hn ((hpA hx).mp h))
    rw [← hphys, PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hfalse]
    have hm : m < 0 := hs.multiplier_neg
    linarith

theorem charge_lt_one_on_atom_diffuse
    (S : SelectedHighLowStructure W m) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (r : S.I) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.D →
      chargeKernel W p.1 p.2 < 1 := by
  filter_upwards [S.charge_le_half_one_sub_multiplier_on_atom_diffuse hW hd hgap r]
    with p hp hi hj
  have h := hp hi hj
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
