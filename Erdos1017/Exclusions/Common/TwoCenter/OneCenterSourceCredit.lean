module

public import Erdos1017.Exclusions.Common.Flows.SourceRestrictedReverseFlow
public import Erdos1017.SelectedModel.Flows.AtomicAssignmentFlow
public import Erdos1017.SelectedModel.Recovery.FullReversePlateau

/-!
# Source credit of a one-center recovery

This module defines the one-center source density and direction and the partial
endpoint retaining the chosen source region, a feasible probability law with
density at most the strict-gap optimizer, and proves the sharp endpoint budget
retains both the partial-flow energy and its internal shifted energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MissingFlow.OneCenter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual uniform one-center contribution of the entire chosen source. -/
def sourceDensity (μ : Measure Ω) (I C : Set Ω) (p : Ω × Ω) : ℝ :=
  AtomicAssignment.recipientDensity μ I p.1 * C.indicator (fun _ => 1) p.2

/-- Its original-law receipt minus its retained source supply. -/
def sourceDirection (μ : Measure Ω) (I C : Set Ω) (x : Ω) : ℝ :=
  μ.real C * AtomicAssignment.recipientDensity μ I x - C.indicator (fun _ => 1) x

/-- The actual normalized recipient row is integrable. -/
theorem integrable_recipientDensity {I : Set Ω} (hI : MeasurableSet I) :
    Integrable (AtomicAssignment.recipientDensity μ I) μ :=
  (integrable_const _).indicator hI

omit [IsProbabilityMeasure μ] in
/-- Positive recipient mass normalizes the actual recipient density. -/
theorem integral_recipientDensity {I : Set Ω} (hI : MeasurableSet I) (hIpos : 0 < μ.real I) :
    (∫ x, AtomicAssignment.recipientDensity μ I x ∂μ) = 1 := by
  rw [AtomicAssignment.recipientDensity, integral_indicator hI, setIntegral_const]
  exact mul_inv_cancel₀ hIpos.ne'

/-- No positivity of source mass is needed for product integrability. -/
theorem integrable_sourceDensity {I C : Set Ω} (hI : MeasurableSet I) (hC : MeasurableSet C) :
    Integrable (sourceDensity μ I C) (μ.prod μ) :=
  (integrable_recipientDensity hI).mul_prod ((integrable_const (1 : ℝ)).indicator hC)

omit [IsProbabilityMeasure μ] in
/-- The rank-one source contribution has its exact original-law direction. -/
theorem direction_sourceDensity {I C : Set Ω} (hI : MeasurableSet I)
    (hIpos : 0 < μ.real I) (hC : MeasurableSet C) :
    direction μ (sourceDensity μ I C) = sourceDirection μ I C := by
  funext x
  change (∫ y, AtomicAssignment.recipientDensity μ I x * C.indicator (fun _ => 1) y ∂μ) -
    (∫ y, AtomicAssignment.recipientDensity μ I y * C.indicator (fun _ => 1) x ∂μ) = _
  rw [integral_const_mul, integral_mul_const, integral_recipientDensity hI hIpos,
    integral_indicator hC, setIntegral_const]
  change _ = μ.real C * AtomicAssignment.recipientDensity μ I x - C.indicator (fun _ => 1) x
  simp only [smul_eq_mul, mul_one, one_mul]
  ring

/-- The actual one-center direction is integrable, including null sources. -/
theorem integrable_sourceDirection {I C : Set Ω} (hI : MeasurableSet I) (hC : MeasurableSet C) :
    Integrable (sourceDirection μ I C) μ :=
  ((integrable_recipientDensity hI).const_mul _).sub ((integrable_const (1 : ℝ)).indicator hC)

/-- Concrete constant cross blocks determine their actual weighted pairing. -/
theorem pairing_eq_const_of_supported (K : Ω → Ω → ℝ) (f g : Ω → ℝ)
    (A B : Set Ω) (k : ℝ)
    (hf : ∀ᵐ x ∂μ, x ∉ A → f x = 0) (hg : ∀ᵐ x ∂μ, x ∉ B → g x = 0)
    (hblock : ∀ᵐ p ∂μ.prod μ, p.1 ∈ B → p.2 ∈ A → K p.1 p.2 = k) :
    KernelOperator.kernelPairing (μ := μ) K f g = k * (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  have heq : (fun p : Ω × Ω => K p.1 p.2 * f p.2 * g p.1) =ᵐ[μ.prod μ]
      fun p => k * (g p.1 * f p.2) := by
    filter_upwards [hblock, Measure.quasiMeasurePreserving_snd.ae hf,
      Measure.quasiMeasurePreserving_fst.ae hg] with p hp hf hg
    by_cases ha : p.2 ∈ A
    · by_cases hb : p.1 ∈ B
      · rw [hp hb ha]; ring
      · rw [hg hb]; ring
    · rw [hf ha]; ring
  rw [KernelOperator.kernelPairing, integral_congr_ae heq, integral_const_mul, integral_prod_mul]
  ring

omit [IsProbabilityMeasure μ] in
/-- The diagonal physical integral is the indicator energy on that same set. -/
theorem energy_indicator (K : Ω → Ω → ℝ) {C : Set Ω} (hC : MeasurableSet C) :
    KernelOperator.kernelEnergy (μ := μ) K (C.indicator (fun _ => 1)) =
      ∫ p in C ×ˢ C, K p.1 p.2 ∂μ.prod μ := by
  have heq : (fun p : Ω × Ω => K p.1 p.2 * C.indicator (fun _ => 1) p.2 *
      C.indicator (fun _ => 1) p.1) = (C ×ˢ C).indicator (fun p => K p.1 p.2) := by
    funext p
    by_cases hx : p.1 ∈ C <;> by_cases hy : p.2 ∈ C <;> simp [hx, hy]
  rw [KernelOperator.kernelEnergy, heq, integral_indicator (hC.prod hC)]

/-- Actual zero recipient-square and recipient-source blocks leave exactly
source internal energy, without a positive-source-mass assumption. -/
theorem energy_sourceDirection (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    {I C : Set Ω} (hI : MeasurableSet I) (hC : MeasurableSet C)
    (hII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0)
    (hIC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ C → K p.1 p.2 = 0) :
    KernelOperator.kernelEnergy (μ := μ) K (sourceDirection μ I C) =
      ∫ p in C ×ˢ C, K p.1 p.2 ∂μ.prod μ := by
  have hs : ∀ᵐ x ∂μ, x ∉ I → AtomicAssignment.recipientDensity μ I x = 0 :=
    Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have hc : ∀ᵐ x ∂μ, x ∉ C → C.indicator (fun _ => (1 : ℝ)) x = 0 :=
    Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have hzero := pairing_eq_const_of_supported K
    (AtomicAssignment.recipientDensity μ I) (AtomicAssignment.recipientDensity μ I) I I 0 hs hs hII
  have hcross := pairing_eq_const_of_supported K (C.indicator (fun _ => (1 : ℝ)))
    (AtomicAssignment.recipientDensity μ I) C I 0 hc hs hIC
  have hexpand := KernelOperator.kernelEnergy_sub_mul K hK hB hsym
    (C.indicator (fun _ => (1 : ℝ))) (AtomicAssignment.recipientDensity μ I)
    ((integrable_const (1 : ℝ)).indicator hC) (integrable_recipientDensity hI) (μ.real C)
  have heq : KernelOperator.kernelEnergy (μ := μ) K (sourceDirection μ I C) =
      KernelOperator.kernelEnergy (μ := μ) K
        (fun x => C.indicator (fun _ => 1) x - μ.real C * AtomicAssignment.recipientDensity μ I x) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by dsimp only [sourceDirection]; ring)
  change KernelOperator.kernelEnergy (μ := μ) K (AtomicAssignment.recipientDensity μ I) = _ at hzero
  rw [heq, hexpand, hzero, hcross, energy_indicator K hC]
  ring


/-- The retained source calculation uses concrete old adjacency blocks and
actual partial weights, rather than an assumed density identity. -/
structure RetainedSourceGeometry (G : Ω → Ω → ℝ) (I C O : Set Ω) (w : Ω → ℝ) : Prop where
  measurable_I : MeasurableSet I
  measurable_C : MeasurableSet C
  measurable_O : MeasurableSet O
  positive_I : 0 < μ.real I
  disjoint_IC : Disjoint I C
  disjoint_IO : Disjoint I O
  disjoint_CO : Disjoint C O
  integrable_weight : Integrable w μ
  weight_I : ∀ᵐ x ∂μ, x ∈ I → w x = 1
  weight_C : ∀ᵐ x ∂μ, x ∈ C → w x = 1
  weight_off : ∀ᵐ x ∂μ, x ∉ I ∪ C ∪ O → w x = 0
  zero_II : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → G p.1 p.2 = 0
  zero_IC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ C → G p.1 p.2 = 0
  joined_IO : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ O → G p.1 p.2 = 1
  joined_CO : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ O → G p.1 p.2 = 1

omit [IsProbabilityMeasure μ] in
/-- The partial law decomposes into the unchanged recipient, unchanged
source, and actual remaining weighted region on one common event. -/
theorem RetainedSourceGeometry.weight_decomposition {G : Ω → Ω → ℝ}
    {I C O : Set Ω} {w : Ω → ℝ} (h : RetainedSourceGeometry (μ := μ) G I C O w) :
    w =ᵐ[μ] fun x => I.indicator (fun _ => 1) x + C.indicator (fun _ => 1) x + O.indicator w x := by
  filter_upwards [h.weight_I, h.weight_C, h.weight_off] with x hi hc ho
  by_cases hxI : x ∈ I
  · have hxC : x ∉ C := fun hc => disjoint_left.mp h.disjoint_IC hxI hc
    have hxO : x ∉ O := fun ho => disjoint_left.mp h.disjoint_IO hxI ho
    simp only [indicator_of_mem hxI, indicator_of_notMem hxC, indicator_of_notMem hxO,
      add_zero, hi hxI]
  · by_cases hxC : x ∈ C
    · have hxO : x ∉ O := fun ho => disjoint_left.mp h.disjoint_CO hxC ho
      simp only [indicator_of_notMem hxI, indicator_of_mem hxC, indicator_of_notMem hxO,
        zero_add, add_zero, hc hxC]
    · by_cases hxO : x ∈ O
      · simp only [indicator_of_notMem hxI, indicator_of_notMem hxC, indicator_of_mem hxO,
          zero_add]
      · simp only [indicator_of_notMem hxI, indicator_of_notMem hxC, indicator_of_notMem hxO,
          zero_add, ho (by simpa only [mem_union, not_or] using ⟨⟨hxI, hxC⟩, hxO⟩)]

private theorem pairing_add_left (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) (f g u : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hu : Integrable u μ) :
    KernelOperator.kernelPairing (μ := μ) K (fun x => f x + g x) u =
      KernelOperator.kernelPairing (μ := μ) K f u + KernelOperator.kernelPairing (μ := μ) K g u := by
  have heq : (fun p : Ω × Ω => K p.1 p.2 * (f p.2 + g p.2) * u p.1) =
      (fun p => K p.1 p.2 * f p.2 * u p.1 + K p.1 p.2 * g p.2 * u p.1) := by
    funext p; ring
  rw [KernelOperator.kernelPairing, heq,
    integral_add (KernelOperator.integrable_kernel_bilinear hK hB hf hu)
      (KernelOperator.integrable_kernel_bilinear hK hB hg hu)]
  rfl

private theorem pairing_sub_right (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B) (f g u : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hu : Integrable u μ) (a : ℝ) :
    KernelOperator.kernelPairing (μ := μ) K f (fun x => a * g x - u x) =
      a * KernelOperator.kernelPairing (μ := μ) K f g - KernelOperator.kernelPairing (μ := μ) K f u := by
  have heq : (fun p : Ω × Ω => K p.1 p.2 * f p.2 * (a * g p.1 - u p.1)) =
      (fun p => a * (K p.1 p.2 * f p.2 * g p.1) - K p.1 p.2 * f p.2 * u p.1) := by
    funext p; ring
  rw [KernelOperator.kernelPairing, heq,
    integral_sub ((KernelOperator.integrable_kernel_bilinear hK hB hf hg).const_mul a)
      (KernelOperator.integrable_kernel_bilinear hK hB hf hu), integral_const_mul]
  rfl

/-- Exact joined-block calculus gives the original adjacency mixed term
of the partial weight and one-center direction. -/
theorem RetainedSourceGeometry.pairing_sourceDirection {G : Ω → Ω → ℝ} {B : ℝ}
    {I C O : Set Ω} {w : Ω → ℝ} (h : RetainedSourceGeometry (μ := μ) G I C O w)
    (hG : AEStronglyMeasurable (fun p : Ω × Ω => G p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖G p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = G p.2 p.1) :
    KernelOperator.kernelPairing (μ := μ) G w (sourceDirection μ I C) =
      -(∫ p in C ×ˢ C, G p.1 p.2 ∂μ.prod μ) := by
  let i : Ω → ℝ := I.indicator (fun _ => 1)
  let c : Ω → ℝ := C.indicator (fun _ => 1)
  let o : Ω → ℝ := O.indicator w
  let r := AtomicAssignment.recipientDensity μ I
  have hi : Integrable i μ := (integrable_const (1 : ℝ)).indicator h.measurable_I
  have hc : Integrable c μ := (integrable_const (1 : ℝ)).indicator h.measurable_C
  have ho : Integrable o μ := h.integrable_weight.indicator h.measurable_O
  have hr : Integrable r μ := integrable_recipientDensity h.measurable_I
  have si : ∀ᵐ x ∂μ, x ∉ I → i x = 0 := Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have sc : ∀ᵐ x ∂μ, x ∉ C → c x = 0 := Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have so : ∀ᵐ x ∂μ, x ∉ O → o x = 0 := Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have sr : ∀ᵐ x ∂μ, x ∉ I → r x = 0 := Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have hCI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ I → G p.1 p.2 = 0 := by
    filter_upwards [hsym, Measure.measurePreserving_swap.quasiMeasurePreserving.ae h.zero_IC]
      with p hs hz hx hy
    exact hs.trans (hz hy hx)
  have hir := pairing_eq_const_of_supported G i r I I 0 si sr h.zero_II
  have hcr := pairing_eq_const_of_supported G c r C I 0 sc sr h.zero_IC
  have hor := pairing_eq_const_of_supported G o r O I 1 so sr h.joined_IO
  have hic := pairing_eq_const_of_supported G i c I C 0 si sc hCI
  have hoc := pairing_eq_const_of_supported G o c O C 1 so sc h.joined_CO
  have decomp (f : Ω → ℝ) (hf : Integrable f μ) :
      KernelOperator.kernelPairing (μ := μ) G w f =
        KernelOperator.kernelPairing (μ := μ) G i f +
        KernelOperator.kernelPairing (μ := μ) G c f + KernelOperator.kernelPairing (μ := μ) G o f := by
    have heq : KernelOperator.kernelPairing (μ := μ) G w f =
        KernelOperator.kernelPairing (μ := μ) G (fun x => i x + c x + o x) f := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae h.weight_decomposition] with p hp
      rw [hp]
    rw [heq, pairing_add_left G hG hB (fun x => i x + c x) o f (hi.add hc) ho hf,
      pairing_add_left G hG hB i c f hi hc hf]
  change KernelOperator.kernelPairing (μ := μ) G w (fun x => μ.real C * r x - c x) = _
  rw [pairing_sub_right G hG hB w r c h.integrable_weight hr hc,
    decomp r hr, decomp c hc, hir, hcr, hor, hic, hoc]
  have hrint : (∫ x, r x ∂μ) = 1 := integral_recipientDensity h.measurable_I h.positive_I
  have hcint : (∫ x, c x ∂μ) = μ.real C := by
    rw [show c = C.indicator (fun _ => 1) from rfl, integral_indicator h.measurable_C,
      setIntegral_const, smul_eq_mul, mul_one]
  change μ.real C * _ - _ = _
  rw [hrint, hcint]
  have hcc := energy_indicator (μ := μ) G h.measurable_C
  change KernelOperator.kernelPairing (μ := μ) G c c = _ at hcc
  rw [hcc]
  ring

/-- Passing from the retained-source partial weight to the full weight
removes exactly the original source's internal adjacency energy. -/
theorem RetainedSourceGeometry.energy_add_sourceDirection {G : Ω → Ω → ℝ} {B : ℝ}
    {I C O : Set Ω} {w : Ω → ℝ} (h : RetainedSourceGeometry (μ := μ) G I C O w)
    (hG : AEStronglyMeasurable (fun p : Ω × Ω => G p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖G p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = G p.2 p.1) :
    KernelOperator.kernelEnergy (μ := μ) G (fun x => w x + sourceDirection μ I C x) =
      KernelOperator.kernelEnergy (μ := μ) G w - ∫ p in C ×ˢ C, G p.1 p.2 ∂μ.prod μ := by
  have hx := KernelOperator.kernelEnergy_sub_mul G hG hB hsym w (sourceDirection μ I C)
    h.integrable_weight (integrable_sourceDirection h.measurable_I h.measurable_C) (-1)
  have he := energy_sourceDirection G hG hB hsym h.measurable_I h.measurable_C h.zero_II h.zero_IC
  have hp := h.pairing_sourceDirection hG hB hsym
  simp only [neg_mul, one_mul, sub_neg_eq_add, neg_sq, one_pow, he, hp] at hx
  linarith

/-- Product-AE equality of actual flows gives one common AE direction identity. -/
theorem direction_congr {q r : Ω × Ω → ℝ} (h : q =ᵐ[μ.prod μ] r) :
    direction μ q =ᵐ[μ] direction μ r := by
  filter_upwards [Measure.ae_ae_of_ae_prod h,
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae h)]
    with x hx hy
  change ∀ᵐ y ∂μ, q (y, x) = r (y, x) at hy
  change (∫ y, q (x, y) ∂μ) - (∫ y, q (y, x) ∂μ) = _
  rw [integral_congr_ae hx, integral_congr_ae hy]
  rfl

/-- The actual recovered source column factorization identifies its direction. -/
theorem direction_sourceSlice {q : Ω × Ω → ℝ} {I C : Set Ω}
    (hI : MeasurableSet I) (hIpos : 0 < μ.real I) (hC : MeasurableSet C)
    (hfactor : sourceSlice C q =ᵐ[μ.prod μ] sourceDensity μ I C) :
    direction μ (sourceSlice C q) =ᵐ[μ] sourceDirection μ I C := by
  have h := direction_congr hfactor
  rwa [direction_sourceDensity hI hIpos hC] at h

/-- The physical source slice pays exactly the original source internal
shifted energy whenever its actual column factorization and zero blocks hold. -/
theorem energy_sourceSlice (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    {q : Ω × Ω → ℝ} {I C : Set Ω} (hI : MeasurableSet I) (hIpos : 0 < μ.real I)
    (hC : MeasurableSet C) (hfactor : sourceSlice C q =ᵐ[μ.prod μ] sourceDensity μ I C)
    (hII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0)
    (hIC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ C → K p.1 p.2 = 0) :
    KernelOperator.kernelEnergy (μ := μ) K (direction μ (sourceSlice C q)) =
      ∫ p in C ×ˢ C, K p.1 p.2 ∂μ.prod μ := by
  rw [← energy_sourceDirection K hK hB hsym hI hC hII hIC]
  apply integral_congr_ae
  have hd := direction_sourceSlice hI hIpos hC hfactor
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hd,
    Measure.quasiMeasurePreserving_snd.ae hd] with p hx hy
  rw [hx, hy]

end Erdos1017.MissingFlow.OneCenter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Endpoint density is the original adjacency energy of its actual weight. -/
theorem missingFlowEndpoint_density_eq_energy (W : Model Ω μ) (q : Ω × Ω → ℝ)
    (hq : Integrable q (μ.prod μ)) (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hsupply : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1) :
    density (missingFlowEndpoint W q hq hq0 hsupply) =
      KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W)
        (integrableTiltWeight (MissingFlow.direction μ q) 1) / 2 :=
  density_integrableReweight W _
    (integrableTiltWeight_integrable _ (MissingFlow.integrable_direction hq) 1)
    (integrableTiltWeight_nonnegative _ (MissingFlow.direction_ge_neg_one hq0 hsupply)
      1 ⟨by norm_num, le_rfl⟩)
    (integrableTiltWeight_integral _ (MissingFlow.integrable_direction hq)
      (MissingFlow.integral_direction hq) 1)

/-- Endpoint density depends only on the actual original-law flow direction. -/
theorem missingFlowEndpoint_density_congr (W : Model Ω μ) {q r : Ω × Ω → ℝ}
    (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ x ∂μ, MissingFlow.supply μ q x ≤ 1)
    (hrs : ∀ᵐ x ∂μ, MissingFlow.supply μ r x ≤ 1)
    (hqr : MissingFlow.direction μ q =ᵐ[μ] MissingFlow.direction μ r) :
    density (missingFlowEndpoint W q hq hq0 hqs) = density (missingFlowEndpoint W r hr hr0 hrs) := by
  rw [missingFlowEndpoint_density_eq_energy, missingFlowEndpoint_density_eq_energy]
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hqr,
    Measure.quasiMeasurePreserving_snd.ae hqr] with p hx hy
  change adjacencyKernel W p.1 p.2 * (1 + 1 * MissingFlow.direction μ q p.2) *
    (1 + 1 * MissingFlow.direction μ q p.1) = _
  rw [hx, hy]
  rfl

namespace SelectedHighLowStructure.IsFullReverseFlow

variable {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- The literal complementary slice is supported on the remaining HIGH sources. -/
theorem sourceSlice_compl_eq_high_diff (hq : S.IsFullReverseFlow q) (C : Set Ω) :
    MissingFlow.sourceSlice Cᶜ q =ᵐ[μ.prod μ] MissingFlow.sourceSlice (S.H \ C) q := by
  filter_upwards [hq.support] with p hp
  by_cases hz : q p = 0
  · simp [MissingFlow.sourceSlice, hz]
  · have hH := (hp hz).2.2
    simp [MissingFlow.sourceSlice, hH]

/-- Complementary source supply is explicitly at most the original law. -/
theorem retained_supply_le_one (hq : S.IsFullReverseFlow q) (C : Set Ω) :
    ∀ᵐ x ∂μ, MissingFlow.supply μ (MissingFlow.sourceSlice Cᶜ q) x ≤ 1 := by
  filter_upwards [hq.sourceSlice_compl_supply C] with x hx
  rw [hx]
  by_cases h : x ∈ S.H \ C
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]; exact zero_le_one

/-- The actual partial endpoint retaining the chosen source region. -/
def retainedEndpoint (hq : S.IsFullReverseFlow q) {C : Set Ω} (hC : MeasurableSet C) :
    Model Ω (missingFlowEndpointLaw μ (MissingFlow.sourceSlice Cᶜ q)) :=
  missingFlowEndpoint W _ (MissingFlow.integrable_sourceSlice hq.integrable hC.compl)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative Cᶜ) (hq.retained_supply_le_one C)

/-- The retained endpoint is an actual probability law, including null sources. -/
theorem retainedEndpoint_probability (hq : S.IsFullReverseFlow q) {C : Set Ω}
    (hC : MeasurableSet C) : IsProbabilityMeasure (missingFlowEndpointLaw μ (MissingFlow.sourceSlice Cᶜ q)) :=
  missingFlowEndpoint_probability _ (MissingFlow.integrable_sourceSlice hq.integrable hC.compl)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative Cᶜ) (hq.retained_supply_le_one C)

/-- Full clique feasibility survives the retained endpoint's actual law. -/
theorem retainedEndpoint_fullFeasible (hq : S.IsFullReverseFlow q) {C : Set Ω}
    (hC : MeasurableSet C) (hW : FullFeasible W) : FullFeasible (hq.retainedEndpoint hC) :=
  fullFeasible_missingFlowEndpoint W hW _ (MissingFlow.integrable_sourceSlice hq.integrable hC.compl)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative Cᶜ) (hq.retained_supply_le_one C)

/-- Actual singleton source factorization and joined blocks give the exact
density lost between the retained partial endpoint and the full endpoint. -/
theorem endpoint_density_eq_retained_sub (hq : S.IsFullReverseFlow q)
    {I C O : Set Ω}
    (hgeom : MissingFlow.OneCenter.RetainedSourceGeometry (μ := μ) (adjacencyKernel W) I C O
      (integrableTiltWeight (MissingFlow.direction μ (MissingFlow.sourceSlice Cᶜ q)) 1))
    (hfactor : MissingFlow.sourceSlice C q =ᵐ[μ.prod μ] MissingFlow.OneCenter.sourceDensity μ I C) :
    density hq.endpoint = density (hq.retainedEndpoint hgeom.measurable_C) -
      (∫ p in C ×ˢ C, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 := by
  have hsource := MissingFlow.OneCenter.direction_sourceSlice hgeom.measurable_I hgeom.positive_I
    hgeom.measurable_C hfactor
  have hd : integrableTiltWeight (MissingFlow.direction μ q) 1 =ᵐ[μ]
      fun x => integrableTiltWeight (MissingFlow.direction μ (MissingFlow.sourceSlice Cᶜ q)) 1 x +
        MissingFlow.OneCenter.sourceDirection μ I C x := by
    filter_upwards [MissingFlow.direction_sourceSlice_add_compl hq.integrable hgeom.measurable_C,
      hsource] with x hx hs
    change 1 + 1 * MissingFlow.direction μ q x = _
    rw [hx]
    dsimp only [Pi.add_apply]
    rw [hs]
    dsimp only [integrableTiltWeight]
    ring
  have heq : KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W)
      (integrableTiltWeight (MissingFlow.direction μ q) 1) =
      KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W)
        (fun x => integrableTiltWeight (MissingFlow.direction μ (MissingFlow.sourceSlice Cᶜ q)) 1 x +
          MissingFlow.OneCenter.sourceDirection μ I C x) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hd,
      Measure.quasiMeasurePreserving_snd.ae hd] with p hx hy
    rw [hx, hy]
  have he := hgeom.energy_add_sourceDirection (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (adjacencyKernel_symm W)
  change density (missingFlowEndpoint W q hq.integrable hq.nonnegative hq.supply_le_one) = _
  rw [missingFlowEndpoint_density_eq_energy]
  change _ = density (missingFlowEndpoint W _ _ _ _) - _
  rw [missingFlowEndpoint_density_eq_energy, heq, he]
  ring

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The retained partial model has density at most the original strict-gap
optimizer, without requiring a positive transported or retained source mass. -/
theorem retainedEndpoint_density_le (hq : S.IsFullReverseFlow q) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) {C : Set Ω} (hC : MeasurableSet C) :
    density (hq.retainedEndpoint hC) ≤ d := by
  have hT : MeasurableSet (S.H \ C) := S.hpartition.1.diff hC
  have hTH : S.H \ C ⊆ S.H := sdiff_subset
  have hdir := MissingFlow.OneCenter.direction_congr (hq.sourceSlice_compl_eq_high_diff C)
  have hden := missingFlowEndpoint_density_congr W
    (MissingFlow.integrable_sourceSlice hq.integrable hC.compl)
    (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative Cᶜ)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative (S.H \ C))
    (hq.retained_supply_le_one C) (hq.sourceSlice_supply_le_one hTH) hdir
  exact hden.trans_le (hq.sourceSliceEndpoint_density_le hW hd hgap hT hTH)

/-- The sharp full endpoint budget retains both the partial-flow energy and
the source's actual internal shifted energy, paying its internal edges. -/
theorem one_center_source_credit (hq : S.IsFullReverseFlow q) {d c t : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hcap : ∀ r : S.I, S.reverseClassMass q r ≤ t)
    {I C O : Set Ω}
    (hgeom : MissingFlow.OneCenter.RetainedSourceGeometry (μ := μ) (adjacencyKernel W) I C O
      (integrableTiltWeight (MissingFlow.direction μ (MissingFlow.sourceSlice Cᶜ q)) 1))
    (hfactor : MissingFlow.sourceSlice C q =ᵐ[μ.prod μ] MissingFlow.OneCenter.sourceDensity μ I C) :
    c + (-m) * ((∫ p in C ×ˢ C, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) +
        (KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
          (MissingFlow.direction μ (MissingFlow.sourceSlice Cᶜ q)) +
            ∫ p in C ×ˢ C, shiftedKernel W m p.1 p.2 ∂μ.prod μ) / 2 ≤ t ^ 2 := by
  have hII : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, hgeom.zero_II] with p hc hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hc
    simpa only [hz hx hy, sub_zero, one_mul] using hc
  have hIC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ C → shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, hgeom.zero_IC] with p hc hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hc
    simpa only [hz hx hy, sub_zero, one_mul] using hc
  have hcredit := (hq.endpoint_credit hW hd hgap t hcap).2.2.1
  have henergy := hq.sourceSlice_energy_add_le hW hd hgap hgeom.measurable_C
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 :=
    (shiftedMoment_symm W m).mono (fun _ hx => hx.symm)
  have hsource := MissingFlow.OneCenter.energy_sourceSlice (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    hgeom.measurable_I hgeom.positive_I hgeom.measurable_C hfactor hII hIC
  rw [hsource] at henergy
  have hden := hq.endpoint_density_eq_retained_sub hgeom hfactor
  have hpartial := hq.retainedEndpoint_density_le hW hd hgap hgeom.measurable_C
  have hm : 0 ≤ -m := (neg_pos.mpr (hW.strict_gap_structure hd hgap).multiplier_neg).le
  have hcost := mul_nonneg hm (sub_nonneg.mpr hpartial)
  nlinarith

end SelectedHighLowStructure.IsFullReverseFlow

end Erdos1017.CappedModel
