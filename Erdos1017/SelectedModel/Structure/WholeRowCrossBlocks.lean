module

public import Erdos1017.SelectedModel.Structure.WholeRowAtoms

/-!
# Cross blocks between whole row fibers

Two positive sets of whole homogeneous rows have one cross constant, so two
positive whole-row fibers have a single original cross block that is either
missing or joined, and a positive intersection with the first row's nonneighbor
region forces it to be missing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual measurable representatives justify lifting restricted row
identities to a restricted product. -/
private theorem ae_eq_of_homogeneous_restricted_rows
    (K : Ω → Ω → ℝ) (f : Ω → ℝ) (hf : StronglyMeasurable f) (s t : Set Ω)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] f) :
    ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = f p.2 := by
  have hle : (μ.restrict s).prod (μ.restrict t) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hm := hK.mono_measure hle
  have he : (fun p : Ω × Ω => K p.1 p.2) =ᵐ[(μ.restrict s).prod (μ.restrict t)]
      hm.mk (fun p : Ω × Ω => K p.1 p.2) := hm.ae_eq_mk
  have hgood : ∀ᵐ x ∂μ.restrict s, ∀ᵐ y ∂μ.restrict t,
      hm.mk (fun p : Ω × Ω => K p.1 p.2) (x, y) = f y := by
    filter_upwards [hrows, Measure.ae_ae_of_ae_prod he] with x hx heq
    filter_upwards [ae_restrict_of_ae hx, heq] with y hy hz
    exact hz.symm.trans hy
  have hprod : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t),
      hm.mk (fun p : Ω × Ω => K p.1 p.2) p = f p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm.stronglyMeasurable_mk.measurable
      (hf.comp_measurable measurable_snd).measurable)).mpr hgood
  exact he.trans hprod

/-- Two positive sets of whole homogeneous rows have one actual cross
constant. Both row-value constants and the kernel constant are derived
from common good sections, with no prescribed physical point. -/
theorem exists_cross_constant_of_homogeneous_rows
    (K : Ω → Ω → ℝ) (f g : Ω → ℝ) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (s t : Set Ω) (hspos : 0 < μ s) (htpos : 0 < μ t)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hrows : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] f)
    (hrowt : ∀ᵐ x ∂μ.restrict t, K x =ᵐ[μ] g)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (B : ℝ) (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B) :
    ∃ q ∈ Icc (0 : ℝ) B,
      (f =ᵐ[μ.restrict t] fun _ => q) ∧ (g =ᵐ[μ.restrict s] fun _ => q) ∧
      ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = q := by
  have hle : (μ.restrict s).prod (μ.restrict t) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hleft := ae_eq_of_homogeneous_restricted_rows K f hf s t hK hrows
  have hright := (Measure.measurePreserving_swap (μ := μ.restrict s)
    (ν := μ.restrict t)).quasiMeasurePreserving.ae
      (ae_eq_of_homogeneous_restricted_rows K g hg t s hK hrowt)
  have hfg : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), g p.1 = f p.2 := by
    filter_upwards [hleft, hright, ae_mono hle hsym] with p hl hr hs
    exact hr.symm.trans (hs.symm.trans hl)
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
    (Measure.ae_ae_of_ae_prod hfg)
  have hfq : f =ᵐ[μ.restrict t] fun _ => g x := hx.mono (fun _ hy => hy.symm)
  have hgq : g =ᵐ[μ.restrict s] fun _ => g x := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfg] with z hz
    obtain ⟨y, _, hy, hfy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htpos.ne' (hz.and hfq)
    exact hy.trans hfy
  have hkq : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), K p.1 p.2 = g x := by
    filter_upwards [hleft, Measure.quasiMeasurePreserving_snd.ae hfq] with p hp hq
    exact hp.trans hq
  have hb : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict t), g x ∈ Icc (0 : ℝ) B := by
    filter_upwards [hkq, ae_mono hle hbound] with p hp hb
    rwa [← hp]
  obtain ⟨z, _, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
    (Measure.ae_ae_of_ae_prod hb)
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htpos.ne' hz
  exact ⟨g x, hy, hfq, hgq, hkq⟩

/-- The same supplied positive whole-row fibers have a single original
K/G/Y cross block, including both restricted row-value constants. -/
theorem exists_whole_row_cross_block
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ) (r u : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hr : WholeRowFiberData μ K G Y B m R r) (hu : WholeRowFiberData μ K G Y B m R u)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hG : AEStronglyMeasurable (fun p : Ω × Ω => G p.1 p.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B) :
    ∃ q ∈ Icc (0 : ℝ) B,
      ((r : Ω → ℝ) =ᵐ[μ.restrict {x | R x = u}] fun _ => q) ∧
      ((u : Ω → ℝ) =ᵐ[μ.restrict {x | R x = r}] fun _ => q) ∧
      ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
        K p.1 p.2 = q ∧ G p.1 p.2 = (if 0 < q then 1 else 0) ∧
          Y p.1 p.2 = q + m * (if 0 < q then 1 else 0) := by
  obtain ⟨q, hq, hrq, huq, hkq⟩ := exists_cross_constant_of_homogeneous_rows K r u
    (Lp.stronglyMeasurable r) (Lp.stronglyMeasurable u) _ _ hrpos hupos hK
    (hr.rows.mono (fun _ h => h.1)) (hu.rows.mono (fun _ h => h.1)) hsym B hbound
  have hrg : ∀ᵐ x ∂μ.restrict {x | R x = r}, G x =ᵐ[μ] fun y => if 0 < r y then 1 else 0 :=
    hr.rows.mono (fun _ h => h.2.1)
  have hry : ∀ᵐ x ∂μ.restrict {x | R x = r},
      Y x =ᵐ[μ] fun y => r y + m * (if 0 < r y then 1 else 0) :=
    hr.rows.mono (fun _ h => h.2.2)
  have hfg : StronglyMeasurable (fun y => if 0 < r y then (1 : ℝ) else 0) :=
    stronglyMeasurable_const.ite (measurableSet_lt measurable_const (Lp.stronglyMeasurable r).measurable)
      stronglyMeasurable_const
  have hfy : StronglyMeasurable (fun y => r y + m * (if 0 < r y then (1 : ℝ) else 0)) :=
    (Lp.stronglyMeasurable r).add (stronglyMeasurable_const.mul hfg)
  have hg := ae_eq_of_homogeneous_restricted_rows G _ hfg {x | R x = r} {x | R x = u} hG hrg
  have hy := ae_eq_of_homogeneous_restricted_rows Y _ hfy {x | R x = r} {x | R x = u} hY hry
  refine ⟨q, hq, hrq, huq, ?_⟩
  filter_upwards [hkq, hg, hy, Measure.quasiMeasurePreserving_snd.ae hrq] with p hk hg hy hq
  exact ⟨hk, by simpa only [hq] using hg, by simpa only [hq] using hy⟩

/-- Every actual cross block between two positive whole fibers is either
missing or joined in the original adjacency. -/
theorem whole_row_cross_block_missing_or_joined
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ) (r u : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hr : WholeRowFiberData μ K G Y B m R r) (hu : WholeRowFiberData μ K G Y B m R u)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hG : AEStronglyMeasurable (fun p : Ω × Ω => G p.1 p.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B) :
    (∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}), G p.1 p.2 = 0) ∨
      (∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}), G p.1 p.2 = 1) := by
  obtain ⟨q, _, _, _, hcross⟩ := exists_whole_row_cross_block
    K G Y B m R r u hrpos hupos hr hu hK hG hY hsym hbound
  by_cases hq : 0 < q
  · exact Or.inr (hcross.mono (fun _ hp => by simpa only [hq, ↓reduceIte] using hp.2.1))
  · exact Or.inl (hcross.mono (fun _ hp => by simpa only [hq, ↓reduceIte] using hp.2.1))

/-- A positive intersection of the second fiber with the first row's
nonneighbor region forces the entire original cross block to be missing. -/
theorem whole_row_cross_block_zero_of_positive_nonpositive
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ) (r u : Lp ℝ 2 μ)
    (hrpos : 0 < μ {x | R x = r}) (hupos : 0 < μ {x | R x = u})
    (hr : WholeRowFiberData μ K G Y B m R r) (hu : WholeRowFiberData μ K G Y B m R u)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hG : AEStronglyMeasurable (fun p : Ω × Ω => G p.1 p.2) (μ.prod μ))
    (hY : AEStronglyMeasurable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B)
    (humeas : MeasurableSet {x | R x = u})
    (hmissing : 0 < μ ({x | R x = u} ∩ {x | r x ≤ 0})) :
    ((r : Ω → ℝ) =ᵐ[μ.restrict {x | R x = u}] fun _ => 0) ∧
      ((u : Ω → ℝ) =ᵐ[μ.restrict {x | R x = r}] fun _ => 0) ∧
      (∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = u}),
        K p.1 p.2 = 0 ∧ G p.1 p.2 = 0 ∧ Y p.1 p.2 = 0) := by
  obtain ⟨q, hq, hrq, huq, hcross⟩ := exists_whole_row_cross_block
    K G Y B m R r u hrpos hupos hr hu hK hG hY hsym hbound
  have hglobal := (ae_restrict_iff' humeas).mp hrq
  obtain ⟨y, hy, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmissing.ne'
    (ae_restrict_of_ae hglobal)
  have he : r y = q := hgood hy.1
  have hyzero : r y ≤ 0 := hy.2
  rw [he] at hyzero
  have hqzero : q = 0 := le_antisymm hyzero hq.1
  rw [hqzero] at hrq huq hcross
  exact ⟨hrq, huq, hcross.mono (fun _ hp => by simpa using hp)⟩

end Erdos1017.KernelOperator
