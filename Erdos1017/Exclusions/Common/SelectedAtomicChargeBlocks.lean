module

public import Erdos1017.Exclusions.Common.Covered.CoveredBoundaryCoefficientBounds
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalTriangle

/-!
# Constant charge blocks between whole atoms

Positive whole fibers carry a constant charge block equal to their conditional
mean, the averaged root row on a second whole fiber equals that atomic
coefficient, and distinct exterior atoms obey the rooted conditional triangle
and their own strict support floor.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Actual positive whole fibers have a constant original charge block,
identified with their literal conditional mean. No diffuse mass is needed. -/
theorem ae_atomic_charge_block (S : SelectedHighLowStructure W m) (k u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = S.coveredCountableBoundaryCoefficient (Sum.inl k) (Sum.inl u) := by
  obtain ⟨q, _, _, _, hc⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ k.val u.val
    (S.hfibers k.val k.property).2.1 (S.hfibers u.val u.property).2.1
    (S.hfibers k.val k.property).2.2.2 (S.hfibers u.val u.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W) (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun _ h => h.symm)) hW.moment_mem
  let b := q + m * (if 0 < q then 1 else 0)
  have hb : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = b := by
    rw [Measure.prod_restrict] at hc
    have h := (ae_restrict_iff' ((S.hfibers k.val k.property).1.prod
      (S.hfibers u.val u.property).1)).mp hc
    exact h.mono (fun _ hp hk hu => (hp ⟨hk, hu⟩).2.2)
  let : IsProbabilityMeasure (cond μ {x | S.ρ x = k.val}) :=
    cond_isProbabilityMeasure (S.hfibers k.val k.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ {x | S.ρ x = u.val}) :=
    cond_isProbabilityMeasure (S.hfibers u.val u.property).2.1.ne'
  have hmean : S.coveredCountableBoundaryCoefficient (Sum.inl k) (Sum.inl u) = b := by
    unfold coveredCountableBoundaryCoefficient FiniteArity.regionPairCharge
    dsimp only
    rw [S.coveredCountableBoundaryLabel_fiber_inl k,
      S.coveredCountableBoundaryLabel_fiber_inl u]
    have heq : ∀ᵐ p ∂(cond μ {x | S.ρ x = k.val}).prod (cond μ {x | S.ρ x = u.val}),
        chargeKernel W p.1 p.2 = b := by
      filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hb,
        Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers k.val k.property).1),
        Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (S.hfibers u.val u.property).1)]
        with p hp hk hu
      exact hp hk hu
    rw [integral_congr_ae heq, integral_const, probReal_univ, one_smul]
  exact hb.mono (fun _ hp hk hu => (hp hk hu).trans hmean.symm)

/-- The actual original averaged root row equals the literal atomic
conditional coefficient on the second whole fiber, on one AE event. -/
theorem ae_atomic_rootChargeRow (S : SelectedHighLowStructure W m) (k u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x =
      S.coveredCountableBoundaryCoefficient (Sum.inl k) (Sum.inl u) :=
  S.ae_rootChargeRow_on_constant_block k u hW hd hgap _ (S.ae_atomic_charge_block k u hW)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Actual distinct exterior atoms obey their rooted conditional triangle
and their original own strict support floor. No diffuse positivity or
averaged-model/cardinality premise is used. -/
theorem exterior_atomic_triangle_and_floor (S : SelectedHighLowStructure W m) (r a u v : S.I)
    (hru : r ≠ u) (hau : a ≠ u) (hrv : r ≠ v) (hav : a ≠ v) (huv : u ≠ v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) +
        S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl v) +
        S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl v) ≤ 1 ∧
      m < S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl v) := by
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  have hG := S.ae_exterior_atoms_adjacent_of_zero_body r a u v hru hau hrv hav huv
    hW hd hgap hN hpair hzero
  have hU := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
    (S.ae_atomic_rootChargeRow r u hW hd hgap)
  have hV := (ae_restrict_iff' (S.hfibers v.val v.property).1).mp
    (S.ae_atomic_rootChargeRow r v hW hd hgap)
  have hs := hW.strict_gap_structure hd hgap
  have hall : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = v.val →
      S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) +
          S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl v) +
          S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl v) ≤ 1 ∧
        m < S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl v) := by
    filter_upwards [hG, S.ae_atomic_charge_block u v hW,
      Measure.quasiMeasurePreserving_fst.ae hU, Measure.quasiMeasurePreserving_snd.ae hV,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support,
      S.ae_universal_root_triangle r hW hd hgap hN, hs.strict_support]
      with p hg hy hu hv hphys hyphys htri hstrict hx hyv
    have hG1 := hg hx hyv
    have hY := hy hx hyv
    have hA : PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
      change W.moment CappedColor.adjacency p = 1 at hG1
      rw [hG1] at hphys
      cases he : PhysicalRepresentative.adjacency W m p.1 p.2
      · simp only [he, Bool.false_eq_true, ite_false] at hphys
        norm_num at hphys
      · rfl
    have hrootx : S.ρ p.1 ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans hx))
    have hrooty : S.ρ p.2 ≠ r.val := fun he => hrv (Subtype.ext (he.symm.trans hyv))
    have ht := htri hrootx hrooty hA
    rw [hu hx, hv hyv, hyphys, hY] at ht
    have hM : 0 < shiftedMoment W m p := by
      by_contra hn
      rw [ite_eq_right hn] at hstrict
      change W.moment CappedColor.adjacency p = 0 at hstrict
      change W.moment CappedColor.adjacency p = 1 at hG1
      linarith
    rw [shiftedMoment_eq] at hM
    change 0 < chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 at hM
    rw [hY, hG1] at hM
    exact ⟨ht, by linarith⟩
  let : IsProbabilityMeasure (cond μ {x | S.ρ x = u.val}) :=
    cond_isProbabilityMeasure (S.hfibers u.val u.property).2.1.ne'
  let : IsProbabilityMeasure (cond μ {x | S.ρ x = v.val}) :=
    cond_isProbabilityMeasure (S.hfibers v.val v.property).2.1.ne'
  let ν := (cond μ {x | S.ρ x = u.val}).prod (cond μ {x | S.ρ x = v.val})
  have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hlabels : ∀ᵐ p ∂ν, S.ρ p.1 = u.val ∧ S.ρ p.2 = v.val :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (S.hfibers u.val u.property).1)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (S.hfibers v.val v.property).1))
  obtain ⟨p, hl, hp⟩ := (hlabels.and (hac.ae_le hall)).exists
  exact hp hl.1 hl.2

end Erdos1017.CappedModel.SelectedHighLowStructure
