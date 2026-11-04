module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassMeasurablePatch

/-!
# Structure preserved by a class patch

The shifted moment vanishes on the square of a boundary feature fiber, the
patched conditional color law keeps shifted-color determinism, and a patch on
one class leaves every restricted clique test on a disjoint measurable class
unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The spectral formula makes the shifted moment vanish on the square of a
boundary feature fiber. -/
theorem ae_shiftedMoment_zero_on_featureFiber {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W : Model Ω μ) (F : Ω → H) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫) :
    ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ {x | F x = v} ∧ p.2 ∈ {x | F x = v} →
        shiftedMoment W m p = 0 := by
  filter_upwards [hrep] with p hp hclass
  rw [hp, hclass.1, hclass.2, real_inner_self_eq_norm_sq, hv,
    Real.sq_sqrt hν]
  ring

omit [IsProbabilityMeasure μ] in
/-- A class-square patch preserves the shifted moment when the old shifted
moment vanishes on that square. -/
theorem shiftedMoment_patchZeroClass_ae_eq {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ s ∧ p.2 ∈ s → shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ,
      shiftedMoment (patchZeroClass W s hs m hm L hL) m p =
        shiftedMoment W m p := by
  filter_upwards [hzero] with p hp
  change (patchZeroClass W s hs m hm L hL).moment (shiftedColor m) p = _
  rw [patchZeroClass_moment]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · rw [ite_eq_left hclass, hp hclass]
    by_cases hlabel : L p.1 = L p.2
    · simp [hlabel, shiftedColor]
    · simp [hlabel, shiftedColor, CappedColor.present,
        CappedColor.charge, CappedColor.adjacency]
  · simp [hclass, shiftedMoment]

omit [IsProbabilityMeasure μ] in
/-- The patched model retains the same spectral representation, boundary
zero characterization, and nonnegative shifted moment. -/
theorem patchZeroClass_preserves_shifted_geometry {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k : ℕ} (W : Model Ω μ) (F : Ω → H) (v : H) (ν m : ℝ)
    (hν : 0 ≤ ν) (hv : ‖v‖ = Real.sqrt ν)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (hs : MeasurableSet {x | F x = v})
    (hrep : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔
        ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p) :
    (∀ᵐ p ∂μ.prod μ,
      shiftedMoment (patchZeroClass W {x | F x = v} hs m hm L hL) m p =
        ν - ⟪F p.1, F p.2⟫) ∧
    (∀ᵐ p ∂μ.prod μ,
      shiftedMoment (patchZeroClass W {x | F x = v} hs m hm L hL) m p = 0 ↔
        ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2) ∧
    (∀ᵐ p ∂μ.prod μ,
      0 ≤ shiftedMoment (patchZeroClass W {x | F x = v} hs m hm L hL) m p) := by
  have heq := shiftedMoment_patchZeroClass_ae_eq W {x | F x = v} hs m hm L hL
    (ae_shiftedMoment_zero_on_featureFiber W F v ν m hν hv hrep)
  constructor
  · filter_upwards [heq, hrep] with p hp hrepP
    exact hp.trans hrepP
  constructor
  · filter_upwards [heq, hzero] with p hp hzeroP
    rw [hp]
    exact hzeroP
  · filter_upwards [heq, hnonneg] with p hp hnonnegP
    rw [hp]
    exact hnonnegP

omit [IsProbabilityMeasure μ] in
/-- Complementarity survives an internal finite-label patch. -/
theorem patchZeroClass_complementary {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ∀ᵐ p ∂μ.prod μ,
      (1 - (patchZeroClass W s hs m hm L hL).moment
        CappedColor.adjacency p) *
          shiftedMoment (patchZeroClass W s hs m hm L hL) m p = 0 := by
  classical
  filter_upwards [hcomp] with p hp
  rw [patchZeroClass_moment]
  change (1 - (if p.1 ∈ s ∧ p.2 ∈ s then
      CappedColor.adjacency (if L p.1 = L p.2 then CappedColor.absent
        else CappedColor.present m hm)
      else W.moment CappedColor.adjacency p)) *
    (patchZeroClass W s hs m hm L hL).moment (shiftedColor m) p = 0
  rw [patchZeroClass_moment]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · by_cases hlabel : L p.1 = L p.2
    · simp [hclass, hlabel, shiftedColor]
    · simp [hclass, hlabel, shiftedColor, CappedColor.present,
        CappedColor.charge, CappedColor.adjacency]
  · simpa [hclass, shiftedMoment] using hp

omit [IsProbabilityMeasure μ] in
/-- The patched conditional color law retains shifted-color determinism. -/
theorem patchZeroClass_shifted_deterministic {k : ℕ} (W : Model Ω μ)
    (s : Set Ω) (hs : MeasurableSet s) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (L : Ω → Fin k) (hL : Measurable L)
    (hdet : ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂(patchZeroClass W s hs m hm L hL).kernel p,
        shiftedColor m c = shiftedMoment (patchZeroClass W s hs m hm L hL) m p := by
  filter_upwards [hdet] with p hp
  rw [patchZeroClass_kernel]
  by_cases hclass : p.1 ∈ s ∧ p.2 ∈ s
  · rw [ite_eq_left hclass]
    change ∀ᵐ c ∂Measure.dirac (if L p.1 = L p.2 then CappedColor.absent
      else CappedColor.present m hm),
        shiftedColor m c = (patchZeroClass W s hs m hm L hL).moment (shiftedColor m) p
    rw [patchZeroClass_moment, ite_eq_left hclass]
    simp
  · rw [ite_eq_right hclass]
    change ∀ᵐ c ∂W.kernel p,
      shiftedColor m c = (patchZeroClass W s hs m hm L hL).moment (shiftedColor m) p
    rw [patchZeroClass_moment, ite_eq_right hclass]
    exact hp

omit [IsProbabilityMeasure μ] in
/-- A patch on one class leaves every restricted clique test on a disjoint
measurable class unchanged. -/
theorem restrictedCliquePresence_patchZeroClass_eq_of_disjoint {k : ℕ}
    (W : Model Ω μ) (s : Set Ω) (hs : MeasurableSet s)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (L : Ω → Fin k) (hL : Measurable L)
    (t : Set Ω) (ht : MeasurableSet t) (hdisj : Disjoint s t) (j : ℕ) :
    restrictedCliquePresence (patchZeroClass W s hs m hm L hL) t j =
      restrictedCliquePresence W t j := by
  have hno {x : Ω} (hx : x ∈ t) : x ∉ s := by
    intro hxs
    exact (Set.disjoint_left.mp hdisj hxs hx)
  have hpi : MeasurableSet (Set.univ.pi (fun _ : Fin j => t)) :=
    MeasurableSet.pi countable_univ (fun _ _ => ht)
  have hLaw (x : Fin j → Ω) (hx : x ∈ Set.univ.pi (fun _ : Fin j => t)) :
      cliqueLaw (patchZeroClass W s hs m hm L hL) x = cliqueLaw W x := by
    unfold cliqueLaw DecoratedKernel.sampleLaw
    congr 1
    funext e
    rw [patchZeroClass_kernel]
    have hxt : x e.val.1 ∈ t := Set.mem_pi.mp hx _ (Set.mem_univ _)
    simp [hno hxt]
  unfold restrictedCliquePresence
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hpi] with x hx
  rw [hLaw x hx]

end Erdos1017.CappedModel
