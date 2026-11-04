module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Entry
public import Erdos1017.Exclusions.Common.CliqueStarVariation
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral

/-!
# Peak alternatives after joining the one-center head

At a middle `E₂` contact, an original common peak joined to the one-center head
is either the saturated partner of that head or falls under the other
alternative of `middle_e2_joined_peak_alternatives`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

private theorem middle_joined_unsaturated_mass
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (k r : S.I) (hkr : k ≠ r)
    (hjoined : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood r)
    (hnot : ¬S.IsSaturatedAtomPair k r) :
    2 * μ.real {x | S.ρ x = k.val} ≤ μ.real (S.rootNeighborhood r) := by
  let I : Set Ω := {x | S.ρ x = k.val}
  let P : Set Ω := {x | S.ρ x = r.val}
  let N := S.rootNeighborhood r
  let Z := N \ I
  have hI : MeasurableSet I := (S.hfibers k.val k.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hZ : MeasurableSet Z := hN.diff hI
  have hblock : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = if true = true then 1 else 0 := by
    have hjoined' := (ae_restrict_iff' hI).mp hjoined
    filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_original_root_adjacency r hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae hjoined', adjacencyKernel_symm W]
      with p hr hj hs hk _
    have h := hr (show S.ρ p.2 = r.val from ‹S.ρ p.2 = r.val›)
    change adjacencyKernel W p.2 p.1 = if p.1 ∈ N then 1 else 0 at h
    rw [ite_eq_left (hj hk)] at h
    exact hs.trans h
  have hmem : ∀ᵐ x ∂μ.restrict P, x ∈ S.rootNeighborhood k := by
    have h := S.ae_rootNeighborhood_on_constant_block k r hW hd hgap true hblock
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem (S.hfibers r.val r.property).1]
      with x hx hρ
    exact (hx hρ).mpr rfl
  have hslack := S.ae_rootChargeRow_lt_one_of_not_saturated k r hkr hW hd hgap hnot
  have hcover : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ S.rootNeighborhood k →
      p.2 ∉ Z → adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [S.ae_original_root_adjacency r hW hd hgap] with p hp hP hNk hnotZ
    by_cases hAdj : adjacencyKernel W p.1 p.2 = 0
    · exact hAdj
    have hNr : p.2 ∈ N := by
      have he := hp hP
      by_cases hz : p.2 ∈ N
      · exact hz
      · change adjacencyKernel W p.1 p.2 = if p.2 ∈ N then 1 else 0 at he
        rw [ite_eq_right hz] at he
        exact False.elim (hAdj he)
    have hI' : p.2 ∈ I := by
      by_contra h
      exact hnotZ ⟨hNr, h⟩
    exact False.elim (hNk.1 hI')
  have hcap := S.root_mass_le_cover_of_unsaturated_head k hW hd hgap
    P Z (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.1 hZ
    hmem hslack hcover
  have hsub := (ae_restrict_iff' hI).mp hjoined
  have hinter : μ.real (N ∩ I) = μ.real I := by
    apply measureReal_congr
    filter_upwards [hsub] with x hx
    exact propext ⟨And.right, fun hi => ⟨hx hi, hi⟩⟩
  have hsplit := measureReal_sdiff_add_inter (μ := μ) (s := N) hI
  rw [hinter] at hsplit
  change μ.real Z + μ.real I = μ.real N at hsplit
  linarith

/-- At a middle-E2 contact, an original common peak joined to the actual
one-center head is either the saturated partner of that head, with its
literal universal original row and mass below the recovered height, or
an unsaturated neighbor paying twice its mass in the head neighborhood,
which forces it below one third. -/
theorem middle_e2_joined_peak_alternatives
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (p k : S.I) (hp : R.plateau = {p}) (hkp : k ≠ p)
    (hpeak : S.IsCommonForwardPeak d c k)
    (hjoin : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.rootNeighborhood p) :
    (S.IsSaturatedAtomPair k p ∧
      (∀ᵐ z ∂μ.prod μ, S.ρ z.1 = k.val →
        adjacencyKernel W z.1 z.2 = if S.ρ z.2 = k.val then 0 else 1) ∧
      S.originalAtomMass k < R.height) ∨
    (¬S.IsSaturatedAtomPair k p ∧
      2 * S.originalAtomMass k ≤ μ.real (S.rootNeighborhood p) ∧
      2 * S.originalAtomMass k + R.height ≤ 1 ∧ S.originalAtomMass k < 1 / 3) := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨_, hell, _⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  by_cases hpair : S.IsSaturatedAtomPair k p
  · left
    obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ :=
      S.exists_original_atomic_square_reserve hW hd hgap
    have heq : j = k := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
      (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
    subst j
    have hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.N := by
      rcases hside with hH | hN
      · have hz := hpair.high_head_null hW hd hgap hell.2
        have hraw := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hH
        have heq : μ ({x | S.ρ x = k.val} ∩ S.H) = μ {x | S.ρ x = k.val} := by
          apply measure_congr
          filter_upwards [hraw] with x hx
          exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
        rw [heq] at hz
        exact False.elim ((S.hfibers k.val k.property).2.1.ne' hz)
      · exact hN
    have huniv := S.neutral_atom_adjacency k hW hd hgap hN
    have hneutral := S.universal_atom_neutral k hW hd hgap huniv
    have hmarg := R.reverse_marginals_zero_on_neutral k hneutral
    have he := MissingFlow.endpoint_real_set_eq_original R.flow R.isFullReverseFlow.integrable
      R.isFullReverseFlow.nonnegative R.isFullReverseFlow.supply_le_one
      {x | S.ρ x = k.val} (S.hfibers k.val k.property).1
      (hmarg.mono (fun _ h hx => (h hx).1))
      (hmarg.mono (fun _ h hx => (h hx).2))
    have hmass : S.reverseClassMass R.flow k = S.originalAtomMass k := by
      rw [reverseClassMass, S.collapsedPartLabel_fiber k, he]
      rfl
    have hne : S.reverseClassMass R.flow k ≠ R.height := by
      intro h
      have hk := (R.classMass_eq_iff hW k).mp h
      rw [hp] at hk
      exact hkp (Finset.mem_singleton.mp hk)
    have hlt : S.originalAtomMass k < R.height := by
      rw [← hmass]
      exact lt_of_le_of_ne (R.classMass_le hW k) hne
    exact ⟨hpair, huniv, hlt⟩
  · right
    have hmass := middle_joined_unsaturated_mass (S := S) hW hd hgap k p hkp hjoin hpair
    change 2 * S.originalAtomMass k ≤ μ.real (S.rootNeighborhood p) at hmass
    have hpartition : R.height + μ.real (S.rootNeighborhood p) ≤ 1 := by
      rw [← R.one_center_core_mass p hp]
      exact measureReal_le_one
    obtain ⟨_, _, _, hct⟩ := R.endpoint_credit hW hd hgap
    have hB := MiddleE2Parameter.twoHeadValue_gt_eighth hq
    rw [← hvalue] at hB
    have ht : 1 / 3 < R.height := by
      by_contra h
      have h2 := pow_le_pow_left₀ R.height_pos.le (le_of_not_gt h) 2
      linarith
    exact ⟨hpair, hmass, by linarith, by linarith⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
