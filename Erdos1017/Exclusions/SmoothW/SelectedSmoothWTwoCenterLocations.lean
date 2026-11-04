module

public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterAtomLocation
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePeakBound

/-!
# Common peak lies on the two-center plateau

At a smooth-`W` global excess contact, the common original forward peak belongs
to the recovered two-center plateau, using the `W` intercept and the outside and
private cases (`smoothW_common_peak_mem_plateau`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- At a genuine smooth-W global excess contact, the common original
forward peak belongs to the actual recovered two-center plateau. The W
intercept and the outside, private and shared-source exclusions are derived internally. -/
theorem smoothW_common_peak_mem_plateau
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) (k : S.I) (hpeak : S.IsCommonForwardPeak d c k) :
    k ∈ R.plateau := by
  obtain ⟨hΔ, i, hA, _, _, hi, _, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  have heq : i = k := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  obtain ⟨_, _, hell, heta, hgamma, _⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  obtain ⟨r, u, hru, hp⟩ := Finset.card_eq_two.mp hcard
  have hintercept : (1 + m) / 4 < 2 * (c - m * d) + m := by linarith
  have ht := (R.two_center_parameters hW hd hgap hcard hintercept).2.2.1
  change 357 / 1000 < μ.real {x | S.ρ x = k.val} at hA
  have hlarge : 1 - 2 * R.height < μ.real {x | S.ρ x = k.val} := by linarith
  rcases R.original_atom_twoCenter_location k r u hru hW hp hlarge with
    hr | hu | hprivateFirst | hprivateSecond | hshared
  · obtain ⟨x, hx, hrx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hr
    have hkr : k = r := Subtype.ext (hx.symm.trans hrx)
    rw [hkr, hp]
    simp
  · obtain ⟨x, hx, hux⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers k.val k.property).2.1.ne' hu
    have hku : k = u := Subtype.ext (hx.symm.trans hux)
    rw [hku, hp]
    simp
  · have hb := R.private_atom_mass_lt_third k r u hru hW hd hgap hp hintercept hprivateFirst
    linarith
  · have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
    have hb := R.private_atom_mass_lt_third k u r hru.symm hW hd hgap hp'
      hintercept hprivateSecond
    linarith
  · have hb := R.twoCenter_shared_mass_lt r u hru hW hd hgap hp hintercept hell.1
    have hsub := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hshared
    have hm : S.originalAtomMass k ≤ μ.real (S.twoCenterShared r u) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    change μ.real {x | S.ρ x = k.val} ≤ μ.real (S.twoCenterShared r u) at hm
    linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
