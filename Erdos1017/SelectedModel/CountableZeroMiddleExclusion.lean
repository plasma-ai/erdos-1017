module

public import Erdos1017.SelectedModel.Structure.AffineIsotropicLine
public import Erdos1017.SelectedModel.ZeroClass.IndexOneZeroClasses
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Middle points with two positive neighborhoods are null

Two positive whole-row fibers almost everywhere inside a block exhaust its two
row values, so countably many positive row fibers exclude almost every middle
point with two positive ordered neighborhoods
(`ae_not_two_positive_neighborhoods`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.OrderedZeroTripleGeometry

variable {Ω H Row : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure Ω}

/-- The actual affine-feature plane is measurable without a separability
instance on the whole Hilbert space. Strong measurability suffices. -/
theorem measurableSet_affinePlane (φ : Ω → ℝ) (V : Ω → H)
    (hφ : StronglyMeasurable φ) (hV : StronglyMeasurable V) (x z : Ω) :
    MeasurableSet (affinePlane φ V x z) := by
  have hline : StronglyMeasurable
      (fun w => affineLine (φ x) (φ z) (V x) (V z) (φ w)) := by
    have hleft : StronglyMeasurable (fun w => (φ z - φ w) / (φ z - φ x)) :=
      (stronglyMeasurable_const.sub hφ).div stronglyMeasurable_const
    have hright : StronglyMeasurable (fun w => (φ w - φ x) / (φ z - φ x)) :=
      (hφ.sub stronglyMeasurable_const).div stronglyMeasurable_const
    exact (hleft.smul_const _).add (hright.smul_const _)
  have hn := (hV.sub hline).norm.measurable (measurableSet_singleton (0 : ℝ))
  change MeasurableSet {w | ‖V w - affineLine (φ x) (φ z) (V x) (V z) (φ w)‖ = 0} at hn
  change MeasurableSet {w | V w = affineLine (φ x) (φ z) (V x) (V z) (φ w)}
  simpa only [norm_eq_zero, sub_eq_zero] using hn

/-- Two positive whole-row fibers contained almost everywhere in a block
exhaust its two possible row values. A third row has zero block measure. -/
theorem two_row_block_has_no_third_row (ρ : Ω → Row) (E : Set Ω)
    (hcover : ∃ q₁ q₂ : Row, ∀ᵐ x ∂μ, x ∈ E → ρ x = q₁ ∨ ρ x = q₂)
    (a b : Row) (hab : a ≠ b)
    (ha : 0 < μ {x | ρ x = a}) (hb : 0 < μ {x | ρ x = b})
    (hEa : ∀ᵐ x ∂μ, ρ x = a → x ∈ E)
    (hEb : ∀ᵐ x ∂μ, ρ x = b → x ∈ E) :
    ∀ᵐ x ∂μ, x ∈ E → ρ x = a ∨ ρ x = b := by
  obtain ⟨q₁, q₂, hq⟩ := hcover
  obtain ⟨x, hxa, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt ha)
    (ae_restrict_of_ae (hEa.and hq))
  obtain ⟨z, hzb, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt hb)
    (ae_restrict_of_ae (hEb.and hq))
  change ρ x = a at hxa
  change ρ z = b at hzb
  have haq : a = q₁ ∨ a = q₂ := by simpa only [hxa] using hx.2 (hx.1 hxa)
  have hbq : b = q₁ ∨ b = q₂ := by simpa only [hzb] using hz.2 (hz.1 hzb)
  have hvalues (v : Row) (hv : v = q₁ ∨ v = q₂) : v = a ∨ v = b := by
    rcases haq with ha | ha
    · rcases hbq with hb | hb
      · exact (hab (ha.trans hb.symm)).elim
      · exact hv.imp (fun h => h.trans ha.symm) (fun h => h.trans hb.symm)
    · rcases hbq with hb | hb
      · exact hv.elim (fun h => Or.inr (h.trans hb.symm)) (fun h => Or.inl (h.trans ha.symm))
      · exact (hab (ha.trans hb.symm)).elim
  filter_upwards [hq] with w hw hwe
  exact hvalues _ (hw hwe)

private theorem exists_positive_endpoint_fibers
    (ρ : Ω → Row) (φ : Ω → ℝ) (S E L R : Set Ω) (y : Ω)
    (hy : y ∈ S)
    (hcoords : ∀ x ∈ S, ∀ z ∈ S, ρ x = ρ z → φ x = φ z)
    (hL : ∀ x ∈ L, x ∈ S ∧ φ x < φ y)
    (hR : ∀ z ∈ R, z ∈ S ∧ φ y < φ z)
    (hLpos : μ L ≠ 0) (hRpos : μ R ≠ 0)
    (hLE : ∀ᵐ x ∂μ, x ∈ L → x ∈ E)
    (hRE : ∀ᵐ x ∂μ, x ∈ R → x ∈ E)
    (hcover : ∃ q₁ q₂ : Row, ∀ᵐ x ∂μ, x ∈ E → ρ x = q₁ ∨ ρ x = q₂) :
    ∃ x ∈ L, ∃ z ∈ R, x ∈ E ∧ z ∈ E ∧
      0 < μ {w | ρ w = ρ x} ∧ 0 < μ {w | ρ w = ρ z} ∧
      ρ y ≠ ρ x ∧ ρ y ≠ ρ z := by
  obtain ⟨q₁, q₂, hq⟩ := hcover
  obtain ⟨x, hxL, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hLpos
    (ae_restrict_of_ae (hLE.and hq))
  obtain ⟨z, hzR, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hRpos
    (ae_restrict_of_ae (hRE.and hq))
  have hxE := hx.1 hxL
  have hxq := hx.2 hxE
  have hzE := hz.1 hzR
  have hzq := hz.2 hzE
  have hxs := (hL x hxL).1
  have hzs := (hR z hzR).1
  have hxy := (hL x hxL).2
  have hyz := (hR z hzR).2
  have hxz : ρ x ≠ ρ z := by
    intro heq
    have hφ := hcoords x hxs z hzs heq
    linarith
  have hleft : ∀ᵐ w ∂μ, w ∈ L → ρ w = ρ x := by
    filter_upwards [hLE, hq] with w hwE hwq hwL
    have hws := (hL w hwL).1
    have hwy := (hL w hwL).2
    have hwz : ρ w ≠ ρ z := by
      intro heq
      have hφ := hcoords w hws z hzs heq
      linarith
    rcases hxq with hxq | hxq
    · rcases hzq with hzq | hzq
      · exact (hxz (hxq.trans hzq.symm)).elim
      · rcases hwq (hwE hwL) with hw | hw
        · exact hw.trans hxq.symm
        · exact (hwz (hw.trans hzq.symm)).elim
    · rcases hzq with hzq | hzq
      · rcases hwq (hwE hwL) with hw | hw
        · exact (hwz (hw.trans hzq.symm)).elim
        · exact hw.trans hxq.symm
      · exact (hxz (hxq.trans hzq.symm)).elim
  have hright : ∀ᵐ w ∂μ, w ∈ R → ρ w = ρ z := by
    filter_upwards [hRE, hq] with w hwE hwq hwR
    have hws := (hR w hwR).1
    have hyw := (hR w hwR).2
    have hwx : ρ w ≠ ρ x := by
      intro heq
      have hφ := hcoords w hws x hxs heq
      linarith
    rcases hxq with hxq | hxq
    · rcases hzq with hzq | hzq
      · exact (hxz (hxq.trans hzq.symm)).elim
      · rcases hwq (hwE hwR) with hw | hw
        · exact (hwx (hw.trans hxq.symm)).elim
        · exact hw.trans hzq.symm
    · rcases hzq with hzq | hzq
      · rcases hwq (hwE hwR) with hw | hw
        · exact hw.trans hzq.symm
        · exact (hwx (hw.trans hxq.symm)).elim
      · exact (hxz (hxq.trans hzq.symm)).elim
  have hapos : 0 < μ {w | ρ w = ρ x} :=
    (pos_iff_ne_zero.mpr hLpos).trans_le (measure_mono_ae hleft)
  have hbpos : 0 < μ {w | ρ w = ρ z} :=
    (pos_iff_ne_zero.mpr hRpos).trans_le (measure_mono_ae hright)
  refine ⟨x, hxL, z, hzR, hxE, hzE, hapos, hbpos, ?_, ?_⟩
  · intro heq
    have hφ := hcoords y hy x hxs heq
    linarith
  · intro heq
    have hφ := hcoords y hy z hzs heq
    linarith

variable [MeasurableSpace Row] [MeasurableSingletonClass Row] [SFinite μ]

/-- Countably many actual positive row fibers exclude almost every middle
point with two positive ordered neighborhoods. Endpoint atoms, reanchoring
and the null third-row sets are derived from the two explicit plane inputs. -/
theorem ae_not_two_positive_neighborhoods
    (ρ : Ω → Row) (hρ : Measurable ρ) (φ : Ω → ℝ) (V : Ω → H)
    (ν σ : ℝ) (S : Set Ω) (hS : ∀ᵐ x ∂μ, x ∈ S)
    (hcoords : ∀ x ∈ S, ∀ z ∈ S, ρ x = ρ z → φ x = φ z ∧ V x = V z)
    (L R : Ω → Set Ω)
    (hL : ∀ y x, x ∈ L y → x ∈ S ∧ φ x < φ y)
    (hR : ∀ y z, z ∈ R y → z ∈ S ∧ φ y < φ z)
    (htwo : ∀ x z, IsotropicPair ν σ φ V x z → μ (affinePlane φ V x z) ≠ 0 →
      ∃ q₁ q₂ : Row, ∀ᵐ w ∂μ, w ∈ affinePlane φ V x z → ρ w = q₁ ∨ ρ w = q₂)
    (hextract : ∀ᵐ y ∂μ, μ (L y) ≠ 0 → μ (R y) ≠ 0 →
      ∃ x z, IsotropicPair ν σ φ V x z ∧ y ∈ affinePlane φ V x z ∧
        ∀ᵐ w ∂μ, w ∈ L y ∪ R y → w ∈ affinePlane φ V x z) :
    ∀ᵐ y ∂μ, μ (L y) = 0 ∨ μ (R y) = 0 := by
  classical
  let A := KernelOperator.positiveFiberValues μ ρ
  have hA : A.Countable := KernelOperator.positiveFiberValues_countable ρ hρ
  have : Countable A := hA.to_subtype
  have hrep : ∀ a : A, ∃ x, x ∈ S ∧ ρ x = a.1 := by
    intro a
    have ha : 0 < μ {x | ρ x = a.1} := a.property
    obtain ⟨x, hxa, hxS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt ha)
      (ae_restrict_of_ae hS)
    exact ⟨x, hxS, hxa⟩
  choose rep hrepS hrepρ using hrep
  have hthird (a b : A) : ∀ᵐ y ∂μ,
      IsotropicPair ν σ φ V (rep a) (rep b) →
      y ∈ affinePlane φ V (rep a) (rep b) → ρ y = a.1 ∨ ρ y = b.1 := by
    by_cases hpair : IsotropicPair ν σ φ V (rep a) (rep b)
    · have hEa : ∀ᵐ w ∂μ, ρ w = a.1 → w ∈ affinePlane φ V (rep a) (rep b) := by
        filter_upwards [hS] with w hwS hwa
        have hc := hcoords w hwS (rep a) (hrepS a) (hwa.trans (hrepρ a).symm)
        exact (mem_affinePlane_iff_of_coordinates hc.1 hc.2).mpr
          (left_mem_affinePlane φ V _ _ hpair.scalar_ne)
      have hEb : ∀ᵐ w ∂μ, ρ w = b.1 → w ∈ affinePlane φ V (rep a) (rep b) := by
        filter_upwards [hS] with w hwS hwb
        have hc := hcoords w hwS (rep b) (hrepS b) (hwb.trans (hrepρ b).symm)
        exact (mem_affinePlane_iff_of_coordinates hc.1 hc.2).mpr
          (right_mem_affinePlane φ V _ _ hpair.scalar_ne)
      have hapos : 0 < μ {w | ρ w = a.1} := a.property
      have hbpos : 0 < μ {w | ρ w = b.1} := b.property
      have hEpos : 0 < μ (affinePlane φ V (rep a) (rep b)) :=
        hapos.trans_le (measure_mono_ae hEa)
      have hab : a.1 ≠ b.1 := by
        intro heq
        have hc := hcoords (rep a) (hrepS a) (rep b) (hrepS b)
          ((hrepρ a).trans (heq.trans (hrepρ b).symm))
        exact hpair.scalar_ne hc.1
      have hnothird := two_row_block_has_no_third_row ρ (affinePlane φ V (rep a) (rep b))
        (htwo _ _ hpair (ne_of_gt hEpos)) a.1 b.1 hab hapos hbpos hEa hEb
      filter_upwards [hnothird] with y hy _
      exact hy
    · exact .of_forall (fun _ h => (hpair h).elim)
  have hall : ∀ᵐ y ∂μ, ∀ a b : A,
      IsotropicPair ν σ φ V (rep a) (rep b) →
      y ∈ affinePlane φ V (rep a) (rep b) → ρ y = a.1 ∨ ρ y = b.1 :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hthird a b))
  filter_upwards [hextract, hS, hall] with y hyextract hyS hyall
  by_cases hLzero : μ (L y) = 0
  · exact Or.inl hLzero
  · right
    by_contra hRzero
    obtain ⟨x, z, hpair, hyplane, hneighborhood⟩ := hyextract hLzero hRzero
    have hLE : ∀ᵐ w ∂μ, w ∈ L y → w ∈ affinePlane φ V x z := by
      filter_upwards [hneighborhood] with w hw hwL
      exact hw (Or.inl hwL)
    have hRE : ∀ᵐ w ∂μ, w ∈ R y → w ∈ affinePlane φ V x z := by
      filter_upwards [hneighborhood] with w hw hwR
      exact hw (Or.inr hwR)
    have hEpos : 0 < μ (affinePlane φ V x z) :=
      (pos_iff_ne_zero.mpr hLzero).trans_le (measure_mono_ae hLE)
    obtain ⟨u, huL, v, hvR, huE, hvE, hapos, hbpos, hya, hyb⟩ :=
      exists_positive_endpoint_fibers ρ φ S (affinePlane φ V x z) (L y) (R y) y hyS
        (fun a ha b hb h => (hcoords a ha b hb h).1) (hL y) (hR y) hLzero hRzero
        hLE hRE (htwo x z hpair (ne_of_gt hEpos))
    let a : A := ⟨ρ u, hapos⟩
    let b : A := ⟨ρ v, hbpos⟩
    have huS := (hL y u huL).1
    have hvS := (hR y v hvR).1
    have huv : φ u ≠ φ v := ne_of_lt ((hL y u huL).2.trans (hR y v hvR).2)
    have hpairuv := hpair.reanchor huE hvE huv
    have hcua := hcoords u huS (rep a) (hrepS a) (hrepρ a).symm
    have hcvb := hcoords v hvS (rep b) (hrepS b) (hrepρ b).symm
    have hpairab : IsotropicPair ν σ φ V (rep a) (rep b) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [← hcua.1, ← hcvb.1] using hpairuv.scalar_ne
      · simpa only [← hcua.1, ← hcua.2] using hpairuv.left_norm
      · simpa only [← hcvb.1, ← hcvb.2] using hpairuv.right_norm
      · simpa only [← hcua.1, ← hcua.2, ← hcvb.1, ← hcvb.2] using hpairuv.inner_eq
    have hplanes : affinePlane φ V (rep a) (rep b) = affinePlane φ V x z := by
      rw [← affinePlane_eq_of_endpoint_coordinates hcua.1 hcua.2 hcvb.1 hcvb.2]
      exact affinePlane_reanchor huE hvE huv
    have hyaorb := hyall a b hpairab (hplanes.symm ▸ hyplane)
    exact hyaorb.elim hya hyb

end Erdos1017.OrderedZeroTripleGeometry
