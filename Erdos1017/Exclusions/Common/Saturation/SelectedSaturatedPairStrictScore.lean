module

public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairIncidence
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative

/-!
# Strict score drop away from the saturated heads

Away from the two saturated heads, two explicitly unsaturated whole fibers have
a strictly smaller combined shifted score.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem exists_triple_in_positive_fibers {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ir Iu Iv : Set Ω) (hr : 0 < μ Ir) (hu : 0 < μ Iu) (hv : 0 < μ Iv)
    (P : (Fin 3 → Ω) → Prop)
    (hP : ∀ᵐ w ∂Measure.pi (fun _ : Fin 3 => μ), P w) :
    ∃ x ∈ Ir, ∃ y ∈ Iu, ∃ z ∈ Iv, P ![x, y, z] := by
  have hroot := FiniteArity.ae_root_sections μ 2 P hP
  obtain ⟨x, hx, hxroot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hr.ne'
    (ae_restrict_of_ae hroot)
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
  obtain ⟨y, hy, hysection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hu.ne'
    (ae_restrict_of_ae hys)
  obtain ⟨z, hz, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hv.ne'
    (ae_restrict_of_ae hysection)
  exact ⟨x, hx, y, hy, z, hz, hp⟩

private theorem tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hxy : Y x y = Y y x) (hxz : Y x z = Y z x)
    (hyz : Y y z = Y z y) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hxy, hxz, hyz]
  ring

private theorem triangle_cross_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (Ir Iu Iv : Set Ω) (hr : 0 < μ Ir) (hu : 0 < μ Iu) (hv : 0 < μ Iv)
    (qrv quv m : ℝ) (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n)
    (hru : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iu →
      A p.1 p.2 = true ∧ Y p.1 p.2 = 1)
    (hrv : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iv →
      A p.1 p.2 = true ∧ Y p.1 p.2 = qrv + m)
    (huv : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Iu → p.2 ∈ Iv →
      A p.1 p.2 = true ∧ Y p.1 p.2 = quv + m) :
    qrv + quv ≤ -2 * m := by
  have hpair := hru.and (hrv.and huv)
  have htrip : ∀ᵐ w ∂Measure.pi (fun _ : Fin 3 => μ),
      (FiniteArity.TupleClique A w → FiniteArity.tupleCharge Y w ≤ 1) ∧
      ∀ i j : Fin 3, i ≠ j →
        (w i ∈ Ir → w j ∈ Iu → A (w i) (w j) = true ∧ Y (w i) (w j) = 1) ∧
        (w i ∈ Ir → w j ∈ Iv →
          A (w i) (w j) = true ∧ Y (w i) (w j) = qrv + m) ∧
        (w i ∈ Iu → w j ∈ Iv →
          A (w i) (w j) = true ∧ Y (w i) (w j) = quv + m) :=
    (hfull 3).and (FiniteArity.ae_all_pairs μ 3 _ hpair)
  obtain ⟨x, hx, y, hy, z, hz, ht⟩ :=
    exists_triple_in_positive_fibers μ Ir Iu Iv hr hu hv _ htrip
  have hxy := ht.2 0 1 (by decide)
  have hxz := ht.2 0 2 (by decide)
  have hyz := ht.2 1 2 (by decide)
  have hAxy : A x y = true := (hxy.1 hx hy).1
  have hAxz : A x z = true := (hxz.2.1 hx hz).1
  have hAyz : A y z = true := (hyz.2.2 hy hz).1
  have hAyx : A y x = true := by simpa [hAsym] using hAxy
  have hAzx : A z x = true := by simpa [hAsym] using hAxz
  have hAzy : A z y = true := by simpa [hAsym] using hAyz
  have hclique : FiniteArity.TupleClique A ![x, y, z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact hAxy | exact hAyx | exact hAxz | exact hAyz |
        exact hAzx | exact hAzy | exact False.elim (hij rfl)
  have hbound := ht.1 hclique
  rw [tupleCharge_three Y x y z (hYsym x y) (hYsym x z) (hYsym y z)] at hbound
  have hYxy : Y x y = 1 := (hxy.1 hx hy).2
  have hYxz : Y x z = qrv + m := (hxz.2.1 hx hz).2
  have hYyz : Y y z = quv + m := (hyz.2.2 hy hz).2
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- Away from the two saturated heads, both explicitly unsaturated original
whole fibers have a strictly smaller combined shifted score. -/
theorem IsSaturatedAtomPair.score_lt_on_other_atom
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) (v : S.I)
    (hrv : r ≠ v) (huv : u ≠ v)
    (hnorv : ¬S.IsSaturatedAtomPair r v)
    (hnouv : ¬S.IsSaturatedAtomPair u v)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = v.val}, r.val x + u.val x < 1 - m := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let Iv : Set Ω := {x | S.ρ x = v.val}
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hIv : MeasurableSet Iv := (S.hfibers v.val v.property).1
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hIupos : 0 < μ Iu := (S.hfibers u.val u.property).2.1
  have hIvpos : 0 < μ Iv := (S.hfibers v.val v.property).2.1
  obtain ⟨qrv, hqrv, hrq, _, hcrossrv⟩ :=
    KernelOperator.exists_whole_row_cross_block
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
      r.val v.val hIrpos hIvpos
      (S.hfibers r.val r.property).2.2.2 (S.hfibers v.val v.property).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun p hp => hp.symm)) hW.moment_mem
  obtain ⟨quv, hquv, huq, _, hcrossuv⟩ :=
    KernelOperator.exists_whole_row_cross_block
      (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
      u.val v.val hIupos hIvpos
      (S.hfibers u.val u.property).2.2.2 (S.hfibers v.val v.property).2.2.2
      (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
      (chargeKernel_measurable W)
      ((shiftedMoment_symm W m).mono (fun p hp => hp.symm)) hW.moment_mem
  have hrvraw : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iv →
      shiftedKernel W m p.1 p.2 = qrv ∧
      adjacencyKernel W p.1 p.2 = (if 0 < qrv then 1 else 0) ∧
      chargeKernel W p.1 p.2 = qrv + m * (if 0 < qrv then 1 else 0) := by
    rw [Measure.prod_restrict] at hcrossrv
    have hraw := (ae_restrict_iff' (hIr.prod hIv)).mp hcrossrv
    filter_upwards [hraw] with p hp hr hv
    exact hp ⟨hr, hv⟩
  have huvraw : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Iu → p.2 ∈ Iv →
      shiftedKernel W m p.1 p.2 = quv ∧
      adjacencyKernel W p.1 p.2 = (if 0 < quv then 1 else 0) ∧
      chargeKernel W p.1 p.2 = quv + m * (if 0 < quv then 1 else 0) := by
    rw [Measure.prod_restrict] at hcrossuv
    have hraw := (ae_restrict_iff' (hIu.prod hIv)).mp hcrossuv
    filter_upwards [hraw] with p hp hu hv
    exact hp ⟨hu, hv⟩
  have hscore := S.ae_saturated_head_score_le hW hd hgap hell r u hpair.1 hpair.2
  have hsum : qrv + quv ≤ 1 - m := by
    obtain ⟨x, _, hs, hr, hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIvpos.ne' ((ae_restrict_of_ae hscore).and (hrq.and huq))
    linarith
  have hstrict : qrv + quv < 1 - m := by
    by_contra hn
    have heq : qrv + quv = 1 - m := le_antisymm hsum (le_of_not_gt hn)
    by_cases hqr : 0 < qrv
    · by_cases hqu : 0 < quv
      · have hs := hW.strict_gap_structure hd hgap
        have hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n :=
          PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
        have hphysA := PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
        have hphysY := PhysicalRepresentative.charge_ae_eq W m hs.strict_support
        have hru : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iu →
            A p.1 p.2 = true ∧ Y p.1 p.2 = 1 := by
          filter_upwards [hpair.shifted_block, hpair.2, hphysA, hphysY]
            with p hp ha hA hY hr hu
          have hG := (hp hr hu).1
          have hAy : A p.1 p.2 = true := by
            by_contra hn
            have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
            change adjacencyKernel W p.1 p.2 =
              (if A p.1 p.2 = true then (1 : ℝ) else 0) at hA
            rw [hf] at hA
            norm_num at hA
            linarith
          exact ⟨hAy, hY.trans (ha hr hu)⟩
        have hrv : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ Iv →
            A p.1 p.2 = true ∧ Y p.1 p.2 = qrv + m := by
          filter_upwards [hrvraw, hphysA, hphysY] with p hp hA hY hr hv
          have h := hp hr hv
          have hG : adjacencyKernel W p.1 p.2 = 1 := by simpa [hqr] using h.2.1
          have hAy : A p.1 p.2 = true := by
            by_contra hn
            have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
            change adjacencyKernel W p.1 p.2 =
              (if A p.1 p.2 = true then (1 : ℝ) else 0) at hA
            rw [hf] at hA
            norm_num at hA
            linarith
          refine ⟨hAy, ?_⟩
          change PhysicalRepresentative.charge W m p.1 p.2 = qrv + m
          rw [hY]
          simpa [hqr] using h.2.2
        have huv : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Iu → p.2 ∈ Iv →
            A p.1 p.2 = true ∧ Y p.1 p.2 = quv + m := by
          filter_upwards [huvraw, hphysA, hphysY] with p hp hA hY hu hv
          have h := hp hu hv
          have hG : adjacencyKernel W p.1 p.2 = 1 := by simpa [hqu] using h.2.1
          have hAy : A p.1 p.2 = true := by
            by_contra hn
            have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
            change adjacencyKernel W p.1 p.2 =
              (if A p.1 p.2 = true then (1 : ℝ) else 0) at hA
            rw [hf] at hA
            norm_num at hA
            linarith
          refine ⟨hAy, ?_⟩
          change PhysicalRepresentative.charge W m p.1 p.2 = quv + m
          rw [hY]
          simpa [hqu] using h.2.2
        have htriangle := triangle_cross_sum_le μ A Y
          (PhysicalRepresentative.adjacency_symm W m)
          (PhysicalRepresentative.charge_symm W m)
          Ir Iu Iv hIrpos hIupos hIvpos qrv quv m hfull hru hrv huv
        linarith
      · have hqu0 : quv = 0 := le_antisymm (le_of_not_gt hqu) hquv.1
        have hinc : S.IsSaturatedAtomPair r v := by
          refine ⟨hrv, ?_⟩
          filter_upwards [hrvraw] with p hp hr hv
          have h := hp hr hv
          have hy : chargeKernel W p.1 p.2 = qrv + m := by
            simpa [hqr] using h.2.2
          linarith
        exact hnorv hinc
    · by_cases hqu : 0 < quv
      · have hqr0 : qrv = 0 := le_antisymm (le_of_not_gt hqr) hqrv.1
        have hinc : S.IsSaturatedAtomPair u v := by
          refine ⟨huv, ?_⟩
          filter_upwards [huvraw] with p hp hu hv
          have h := hp hu hv
          have hy : chargeKernel W p.1 p.2 = quv + m := by
            simpa [hqu] using h.2.2
          linarith
        exact hnouv hinc
      · have hm : m < 0 := (hW.strict_gap_structure hd hgap).multiplier_neg
        have hqr0 : qrv = 0 := le_antisymm (le_of_not_gt hqr) hqrv.1
        have hqu0 : quv = 0 := le_antisymm (le_of_not_gt hqu) hquv.1
        linarith
  filter_upwards [hrq, huq] with x hr hu
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
