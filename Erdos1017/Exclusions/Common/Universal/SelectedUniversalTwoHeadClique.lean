module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry

/-!
# Two-head clique bound at common neighbors

Appending the universal root and its saturated partner to a common-neighbor pair
pays one unit on the head pair, so the total head charge is nonpositive at every
common neighbor and the head-charge sum obeys the two-head bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem tupleCharge_four {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z w : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z, w] =
      Y x y + Y x z + Y x w + Y y z + Y y w + Y z w := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
    Fin.sum_univ_succ, hsym y x, hsym z x, hsym w x, hsym z y, hsym w y, hsym w z]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Appending the actual universal root and its saturated partner to a
present common-neighbor pair pays one unit on the head pair. The remaining
four head charges bound the old body charge on one original pair event. -/
theorem ae_universal_saturated_four_clique
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ q ∂μ.prod μ, S.ρ q.1 ≠ r.val → S.ρ q.2 ≠ r.val →
      q.1 ∈ S.rootNeighborhood p → q.2 ∈ S.rootNeighborhood p →
        PhysicalRepresentative.adjacency W m q.1 q.2 = true →
          PhysicalRepresentative.charge W m q.1 q.2 ≤
            -(S.rootChargeRow r q.1 + S.rootChargeRow p q.1) -
              (S.rootChargeRow r q.2 + S.rootChargeRow p q.2) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let Ir := {x | S.ρ x = r.val}
  let Ip := {x | S.ρ x = p.val}
  have hIr := S.hfibers r.val r.property
  have hIp := S.hfibers p.val p.property
  have hs := hW.strict_gap_structure hd hgap
  have hfull :=
    PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic 4
  have hrowr : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      (G q.1 q.2 = true ↔ S.ρ q.2 ≠ r.val) ∧ Y q.1 q.2 = S.rootChargeRow r q.2 := by
    filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN,
      S.ae_root_charge r hW hd hgap] with q hG hY hr
    exact ⟨hG hr, hY hr⟩
  have hrowp : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = p.val →
      (G q.1 q.2 = true ↔ q.2 ∈ S.rootNeighborhood p) ∧
        Y q.1 q.2 = S.rootChargeRow p q.2 := by
    filter_upwards [S.ae_root_adjacency p hW hd hgap,
      S.ae_root_charge p hW hd hgap] with q hG hY hp
    exact ⟨hG hp, hY hp⟩
  have hsat : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val → S.ρ q.2 = p.val → Y q.1 q.2 = 1 := by
    filter_upwards [hpair.2, PhysicalRepresentative.charge_ae_eq W m hs.strict_support]
      with q hq he hr hp
    exact he.trans (hq hr hp)
  have hsections := FiniteArity.ae_root_sections μ 3 _ hfull
  obtain ⟨x, hxIr, hxtest, hxrow, hxsat⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIr.2.1.ne'
      ((ae_restrict_of_ae hsections).and
        ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hrowr)).and
          (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hsat))))
  have hsections' := FiniteArity.ae_root_sections μ 2 _ hxtest
  obtain ⟨y, hyIp, hytest, hyrow, hxy⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIp.2.1.ne'
      ((ae_restrict_of_ae hsections').and
        ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hrowp)).and
          (ae_restrict_of_ae hxsat)))
  have hxyY : Y x y = 1 := hxy hxIr hyIp
  have hxyG : G x y = true := by
    by_contra hn
    have hz := PhysicalRepresentative.charge_zero_of_nonedge W m x y (Bool.eq_false_iff.mpr hn)
    linarith
  have hpairTest : ∀ᵐ q ∂μ.prod μ, FiniteArity.TupleClique G ![x, y, q.1, q.2] →
      FiniteArity.tupleCharge Y ![x, y, q.1, q.2] ≤ 1 := by
    have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
      (measurePreserving_finTwoArrow μ)
    have hvec (q : Ω × Ω) :
        Fin.cons x (Fin.cons y ((MeasurableEquiv.finTwoArrow (α := Ω)).symm q)) =
          ![x, y, q.1, q.2] := by
      ext i
      fin_cases i <;> rfl
    filter_upwards [hmp.quasiMeasurePreserving.ae hytest] with q hq
    simpa only [hvec] using hq
  filter_upwards [hpairTest, Measure.quasiMeasurePreserving_fst.ae hxrow,
    Measure.quasiMeasurePreserving_snd.ae hxrow, Measure.quasiMeasurePreserving_fst.ae hyrow,
    Measure.quasiMeasurePreserving_snd.ae hyrow] with q ht hrz hrw hpz hpw hzr hwr hzp hwp hzw
  have hxz := (hrz hxIr).1.mpr hzr
  have hxw := (hrw hxIr).1.mpr hwr
  have hyz := (hpz hyIp).1.mpr hzp
  have hyw := (hpw hyIp).1.mpr hwp
  have hsym : ∀ a b, G a b = G b a := PhysicalRepresentative.adjacency_symm W m
  have hclique : FiniteArity.TupleClique G ![x, y, q.1, q.2] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at * <;>
      first | exact hxyG | exact hxz | exact hxw | exact hyz | exact hyw | exact hzw |
        exact (hsym _ _).trans hxyG | exact (hsym _ _).trans hxz |
        exact (hsym _ _).trans hxw | exact (hsym _ _).trans hyz |
        exact (hsym _ _).trans hyw | exact (hsym _ _).trans hzw
  have hbound := ht hclique
  rw [tupleCharge_four Y x y q.1 q.2 (PhysicalRepresentative.charge_symm W m),
    hxyY, (hrz hxIr).2, (hrw hxIr).2, (hpz hyIp).2, (hpw hyIp).2] at hbound
  change Y q.1 q.2 ≤ _
  linarith

/-- The original saturated triangle leaves nonpositive total head charge
at every common neighbor. No sign is assigned to either head separately. -/
theorem ae_universal_saturated_common_score_nonpos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → x ∈ S.rootNeighborhood p →
      S.rootChargeRow r x + S.rootChargeRow p x ≤ 0 := by
  have hconstant := S.ae_rootChargeRow_on_constant_block r p hW hd hgap 1 hpair.2
  have htri := Measure.ae_ae_of_ae_prod (S.ae_universal_root_triangle r hW hd hgap hN)
  have hrow : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = p.val →
      (PhysicalRepresentative.adjacency W m q.1 q.2 = true ↔ q.2 ∈ S.rootNeighborhood p) ∧
        PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow p q.2 := by
    filter_upwards [S.ae_root_adjacency p hW hd hgap,
      S.ae_root_charge p hW hd hgap] with q ha hy hp
    exact ⟨ha hp, hy hp⟩
  obtain ⟨y, hy, hc, ht, hr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    (hconstant.and ((ae_restrict_of_ae htri).and
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hrow))))
  have hyn : S.ρ y ≠ r.val := fun he =>
    hpair.1 (Subtype.ext (he.symm.trans hy))
  filter_upwards [ht, hr] with x hx hrow hxout hxp
  have h := hx hyn hxout ((hrow hy).1.mpr hxp)
  rw [hc, (hrow hy).2] at h
  linarith

/-- The actual original charge obeys the two-head bound on all common
neighbor pairs, including nonedges. The sum of head charges is kept signed. -/
theorem ae_universal_saturated_common_charge_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ q ∂μ.prod μ, S.ρ q.1 ≠ r.val → S.ρ q.2 ≠ r.val →
      q.1 ∈ S.rootNeighborhood p → q.2 ∈ S.rootNeighborhood p →
        chargeKernel W q.1 q.2 ≤ -(S.rootChargeRow r q.1 + S.rootChargeRow p q.1) -
          (S.rootChargeRow r q.2 + S.rootChargeRow p q.2) := by
  have hscore := S.ae_universal_saturated_common_score_nonpos r p hpair hW hd hgap hN
  filter_upwards [S.ae_universal_saturated_four_clique r p hpair hW hd hgap hN,
    Measure.quasiMeasurePreserving_fst.ae hscore, Measure.quasiMeasurePreserving_snd.ae hscore,
    PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
    with q hfour hx hy he hxr hyr hxp hyp
  by_cases hA : PhysicalRepresentative.adjacency W m q.1 q.2 = true
  · rw [← he]
    exact hfour hxr hyr hxp hyp hA
  · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2
      (Bool.eq_false_iff.mpr hA)
    rw [← he, hz]
    linarith [hx hxr hxp, hy hyr hyp]

end Erdos1017.CappedModel.SelectedHighLowStructure
