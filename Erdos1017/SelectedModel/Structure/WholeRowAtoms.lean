module

public import Erdos1017.SelectedModel.Structure.KernelRowMap

/-!
# Countable whole row atoms of a symmetric kernel

Positive whole row fibers have homogeneous original adjacency and charge rows
with one internal kernel constant, so each is internally independent or a clique
(`WholeRowFiberData`), and the countable family of whole row atoms is
constructed from the bounded symmetric scalar kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurable representatives permit the reverse Fubini implication for
an equality whose original representatives are only AE measurable. -/
private theorem ae_eq_of_ae_ae_eq {ρ τ : Measure Ω} [SFinite ρ] [SFinite τ]
    {f g : Ω × Ω → ℝ} (hf : AEStronglyMeasurable f (ρ.prod τ))
    (hg : AEStronglyMeasurable g (ρ.prod τ))
    (h : ∀ᵐ x ∂ρ, ∀ᵐ y ∂τ, f (x, y) = g (x, y)) : f =ᵐ[ρ.prod τ] g := by
  have hm : hf.mk f =ᵐ[ρ.prod τ] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hf.stronglyMeasurable_mk.measurable
        hg.stronglyMeasurable_mk.measurable)).mpr
    filter_upwards [h, Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hx hfx hgx
    filter_upwards [hx, hfx, hgx] with y hy hfy hgy
    exact hfy.symm.trans (hy.trans hgy)
  exact hf.ae_eq_mk.trans (hm.trans hg.ae_eq_mk.symm)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The original scalar rows agree with the fiber value on a common AE
subset of the whole L² row fiber. -/
theorem row_fiber_homogeneous [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) (r : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ.restrict {x | R x = r}, K x =ᵐ[μ] (r : Ω → ℝ) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  filter_upwards [ae_restrict_of_ae hrow,
    ae_restrict_mem (hR.measurable (measurableSet_singleton r))] with x hx hr
  have heq : (R x : Ω → ℝ) = (r : Ω → ℝ) := congrArg (fun f : Lp ℝ 2 μ => (f : Ω → ℝ)) hr
  exact hx.symm.trans (Filter.Eventually.of_forall (fun y => congrFun heq y))

/-- Symmetry forces a positive homogeneous row set to have one actual
internal kernel value. The chosen constant comes from common Fubini-good
sections, rather than evaluation at an arbitrary physical point. -/
theorem exists_internal_constant_of_homogeneous_rows
    (K : Ω → Ω → ℝ) (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (s : Set Ω) (hspos : 0 < μ s)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hrow : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] f)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (B : ℝ) (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B) :
    ∃ q ∈ Icc (0 : ℝ) B, (f =ᵐ[μ.restrict s] fun _ => q) ∧
      ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), K p.1 p.2 = q := by
  have hle : (μ.restrict s).prod (μ.restrict s) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hrows : (fun p : Ω × Ω => K p.1 p.2) =ᵐ[(μ.restrict s).prod (μ.restrict s)]
      (fun p => f p.2) := by
    apply ae_eq_of_ae_ae_eq (hK.mono_measure hle)
      (hf.comp_measurable measurable_snd).aestronglyMeasurable
    filter_upwards [hrow] with x hx
    exact ae_restrict_of_ae hx
  have hswap := (Measure.measurePreserving_swap (μ := μ.restrict s)
    (ν := μ.restrict s)).quasiMeasurePreserving.ae hrows
  have hfeq : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), f p.1 = f p.2 := by
    filter_upwards [hrows, hswap, ae_mono hle hsym] with p hp hq hsymp
    exact hq.symm.trans (hsymp.symm.trans hp)
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
    (Measure.ae_ae_of_ae_prod hfeq)
  have hfq : f =ᵐ[μ.restrict s] fun _ => f x := by
    filter_upwards [hx] with y hy
    exact hy.symm
  have hkq : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), K p.1 p.2 = f x := by
    filter_upwards [hrows, Measure.quasiMeasurePreserving_snd.ae hfq] with p hp hq
    exact hp.trans hq
  have hb : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), f x ∈ Icc (0 : ℝ) B := by
    filter_upwards [hkq, ae_mono hle hbound] with p hp hb
    rwa [← hp]
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
    (Measure.ae_ae_of_ae_prod hb)
  obtain ⟨z, _, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne' hy
  exact ⟨f x, hz, hfq, hkq⟩

/-- Strict support and the original charge identity transfer whole scalar
rows to the same original adjacency and charge kernels. -/
theorem adjacency_charge_homogeneous_of_rows
    (K G Y : Ω → Ω → ℝ) (f : Ω → ℝ) (m : ℝ) (s : Set Ω)
    (hrow : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] f)
    (hG : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (hY : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = K p.1 p.2 + m * G p.1 p.2) :
    ∀ᵐ x ∂μ.restrict s,
      (G x =ᵐ[μ] fun y => if 0 < f y then 1 else 0) ∧
      (Y x =ᵐ[μ] fun y => f y + m * (if 0 < f y then 1 else 0)) := by
  filter_upwards [hrow, ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hG),
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hY)] with x hx hgx hyx
  constructor
  · filter_upwards [hx, hgx] with y hy hgy
    rwa [hy] at hgy
  · filter_upwards [hx, hgx, hyx] with y hy hgy hyy
    rw [hyy, hgy, hy]

/-- The actual internal adjacency and charge of a positive homogeneous row
set are determined by the nonnegative internal kernel constant. -/
theorem exists_internal_adjacency_charge_constant
    (K G Y : Ω → Ω → ℝ) (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (m : ℝ) (s : Set Ω) (hspos : 0 < μ s)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hrow : ∀ᵐ x ∂μ.restrict s, K x =ᵐ[μ] f)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (B : ℝ) (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B)
    (hG : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (hY : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = K p.1 p.2 + m * G p.1 p.2) :
    ∃ q ∈ Icc (0 : ℝ) B, (f =ᵐ[μ.restrict s] fun _ => q) ∧
      (∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s),
        K p.1 p.2 = q ∧ G p.1 p.2 = (if 0 < q then 1 else 0) ∧
          Y p.1 p.2 = q + m * (if 0 < q then 1 else 0)) := by
  obtain ⟨q, hq, hfq, hkq⟩ :=
    exists_internal_constant_of_homogeneous_rows K f hf s hspos hK hrow hsym B hbound
  refine ⟨q, hq, hfq, ?_⟩
  have hle : (μ.restrict s).prod (μ.restrict s) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [hkq, ae_mono hle hG, ae_mono hle hY] with p hp hg hy
  exact ⟨hp, by simpa only [hp] using hg, by rw [hy, hg, hp]⟩

/-- A positive square cannot support two different AE constants. -/
theorem ae_internal_constant_iff (G : Ω → Ω → ℝ) (s : Set Ω)
    (hspos : 0 < μ s) (a b : ℝ)
    (ha : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), G p.1 p.2 = a) :
    (∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), G p.1 p.2 = b) ↔ a = b := by
  constructor
  · intro hb
    have heq : ∀ᵐ p ∂(μ.restrict s).prod (μ.restrict s), a = b := by
      filter_upwards [ha, hb] with p hp hq
      exact hp.symm.trans hq
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne'
      (Measure.ae_ae_of_ae_prod heq)
    obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hspos.ne' hx
    exact hy
  · rintro rfl
    exact ha

/-- Whole-fiber homogeneity and the actual internal independent/clique
classification, stated for the original scalar kernels. -/
structure WholeRowFiberData (μ : Measure Ω) (K G Y : Ω → Ω → ℝ)
    (B m : ℝ) (R : Ω → Lp ℝ 2 μ) (r : Lp ℝ 2 μ) : Prop where
  rows : ∀ᵐ x ∂μ.restrict {x | R x = r},
    (K x =ᵐ[μ] (r : Ω → ℝ)) ∧
    (G x =ᵐ[μ] fun y => if 0 < r y then 1 else 0) ∧
    (Y x =ᵐ[μ] fun y => r y + m * (if 0 < r y then 1 else 0))
  internal : ∃ q ∈ Icc (0 : ℝ) B,
      ((r : Ω → ℝ) =ᵐ[μ.restrict {x | R x = r}] fun _ => q) ∧
      (∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
        K p.1 p.2 = q ∧ G p.1 p.2 = (if 0 < q then 1 else 0) ∧
          Y p.1 p.2 = q + m * (if 0 < q then 1 else 0)) ∧
      ((∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
        G p.1 p.2 = 0) ↔ q = 0) ∧
      ((∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
        G p.1 p.2 = 1) ↔ 0 < q)

/-- Each positive whole row fiber has homogeneous original adjacency and
charge rows, and its internal support is exactly independent or a clique. -/
theorem positive_row_fiber_structure [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K G Y : Ω → Ω → ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) (r : Lp ℝ 2 μ)
    (hr : 0 < μ {x | R x = r})
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (B m : ℝ) (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B)
    (hG : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (hY : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = K p.1 p.2 + m * G p.1 p.2) :
    WholeRowFiberData μ K G Y B m R r := by
  have hk := row_fiber_homogeneous K R hR hrow r
  have hgy := adjacency_charge_homogeneous_of_rows K G Y (r : Ω → ℝ) m _ hk hG hY
  refine ⟨?_, ?_⟩
  · filter_upwards [hk, hgy] with x hx hy
    exact ⟨hx, hy⟩
  obtain ⟨q, hq, hrq, hconstant⟩ := exists_internal_adjacency_charge_constant
    K G Y (r : Ω → ℝ) (Lp.stronglyMeasurable r) m _ hr hK hk hsym B hbound hG hY
  have hgq : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
      G p.1 p.2 = (if 0 < q then 1 else 0) := hconstant.mono (fun _ hp => hp.2.1)
  refine ⟨q, hq, hrq, hconstant, ?_, ?_⟩
  · rw [ae_internal_constant_iff G _ hr _ 0 hgq]
    by_cases h : 0 < q
    · simp [h, h.ne']
    · simp [le_antisymm (le_of_not_gt h) hq.1]
  · rw [ae_internal_constant_iff G _ hr _ 1 hgq]
    by_cases h : 0 < q <;> simp [h]

/-- Construct the countable family of actual whole row atoms and all their
homogeneity data from the original bounded symmetric scalar kernel. -/
theorem exists_countable_whole_row_atoms [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K G Y : Ω → Ω → ℝ) (B m : ℝ)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hbound : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 ∈ Icc 0 B)
    (hG : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (hY : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = K p.1 p.2 + m * G p.1 p.2) :
    ∃ (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)),
      StronglyMeasurable R ∧
      (∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x) ∧ A.Countable ∧
      (∀ r ∈ A, MeasurableSet {x | R x = r} ∧ 0 < μ {x | R x = r}) ∧
      A.Pairwise (fun r t => Disjoint {x | R x = r} {x | R x = t}) ∧
      (∀ r ∈ A, WholeRowFiberData μ K G Y B m R r) ∧
      (∀ᵐ p ∂μ.prod μ, (K p.1 =ᵐ[μ] K p.2) ↔
        ∃ r ∈ A, R p.1 = r ∧ R p.2 = r) := by
  have hB : 0 ≤ B := by
    obtain ⟨p, hp⟩ := hbound.exists
    exact hp.1.trans hp.2
  have hb : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B := by
    filter_upwards [hbound] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp.1] using hp.2
  obtain ⟨R, A, hR, hrow, _, hA, hpos, hdisj, heq⟩ :=
    exists_countable_positive_row_fibers K B hB hK hb
  refine ⟨R, A, hR, hrow, hA, hpos, hdisj, ?_, heq⟩
  intro r hr
  exact positive_row_fiber_structure K G Y R hR hrow r (hpos r hr).2
    hK hsym B m hbound hG hY

end Erdos1017.KernelOperator
