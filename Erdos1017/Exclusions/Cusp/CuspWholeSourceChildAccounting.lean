module

public import Erdos1017.Exclusions.Cusp.WholeSourceChild
public import Erdos1017.SelectedModel.Structure.IntegrableKernelPolynomials
public import Erdos1017.Exclusions.Common.TwoCenter.OneCenterSourceCredit

/-!
# Row accounting for the whole-source child

Row and cross-block integrals (`rowIntegral`, `crossIntegral`), the signed
energy weight, and the expansion of the signed child value `physicalChildValue`
under the current law. From the partial-endpoint rows and the hole identity, a
full child with its signed cusp score and outside-square cost bound is obtained
(`exists_child_with_cusp_score`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.WholeSourceChild

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

private theorem pairing_add_mul_left (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (f g h : Ω → ℝ) (hf : Integrable f ν) (hg : Integrable g ν) (hh : Integrable h ν)
    (t : ℝ) : kernelPairing (μ := ν) K (fun x => f x + t * g x) h =
      kernelPairing (μ := ν) K f h + t * kernelPairing (μ := ν) K g h := by
  have he : (fun p : Ω × Ω => K p.1 p.2 * (f p.2 + t * g p.2) * h p.1) =
      (fun p => K p.1 p.2 * f p.2 * h p.1 + t * (K p.1 p.2 * g p.2 * h p.1)) := by
    funext p
    ring
  rw [kernelPairing, he, integral_add (integrable_kernel_bilinear hK hB hf hh)
    ((integrable_kernel_bilinear hK hB hg hh).const_mul t), integral_const_mul]
  rfl

private theorem energy_add_mul (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (f g : Ω → ℝ) (hf : Integrable f ν) (hg : Integrable g ν) (t : ℝ) :
    kernelEnergy (μ := ν) K (fun x => f x + t * g x) =
      kernelEnergy (μ := ν) K f + 2 * t * kernelPairing (μ := ν) K f g +
        t ^ 2 * kernelEnergy (μ := ν) K g := by
  simpa only [neg_mul, sub_neg_eq_add, neg_sq, mul_neg] using
    kernelEnergy_sub_mul K hK hB hsym f g hf hg (-t)

/-- Unnormalized physical current-law row total of the displayed old cell. -/
def rowIntegral (ν : Measure Ω) (K : Ω → Ω → ℝ) (C : Set Ω) : ℝ :=
  ∫ x in C, ∫ y, K x y ∂ν ∂ν

/-- The literal unhalved current-law cross-block charge. -/
def crossIntegral (ν : Measure Ω) (K : Ω → Ω → ℝ) (C D : Set Ω) : ℝ :=
  ∫ p in C ×ˢ D, K p.1 p.2 ∂ν.prod ν

omit [IsProbabilityMeasure ν] in
theorem pairing_indicator (K : Ω → Ω → ℝ) (C D : Set Ω)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    kernelPairing (μ := ν) K (D.indicator (fun _ => 1)) (C.indicator (fun _ => 1)) =
      crossIntegral ν K C D := by
  have he : (fun p : Ω × Ω => K p.1 p.2 * D.indicator (fun _ => 1) p.2 *
      C.indicator (fun _ => 1) p.1) = (C ×ˢ D).indicator (fun p => K p.1 p.2) := by
    funext p
    by_cases hx : p.1 ∈ C <;> by_cases hy : p.2 ∈ D <;> simp [hx, hy]
  rw [kernelPairing, he, integral_indicator (hC.prod hD)]
  rfl

theorem pairing_one_indicator (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B) (C : Set Ω) (hC : MeasurableSet C) :
    kernelPairing (μ := ν) K (fun _ => 1) (C.indicator (fun _ => 1)) = rowIntegral ν K C := by
  rw [kernelPairing_one_eq_row K hK hB _ ((integrable_const 1).indicator hC)]
  rw [rowIntegral, ← integral_indicator hC]
  exact integral_congr_ae (Eventually.of_forall (fun x => by
    by_cases hx : x ∈ C <;> simp [hx]))

/-- Exact signed energy accounting for the actual equalizing weight.
Only concrete zero blocks are used; no stationary equation is assigned. -/
theorem energy_weight (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 0)
    (hII : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0)
    (hPK : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ I ∪ J → K p.1 p.2 = 0)
    (r a z : ℝ) :
    kernelEnergy (μ := ν) K (weight P I J r a z) / 2 =
      kernelEnergy (μ := ν) K (fun _ => 1) / 2 - rowIntegral ν K P +
        (r / a - 1) * rowIntegral ν K I + (r / z - 1) * rowIntegral ν K J +
        (r / a - 1) * (r / z - 1) * crossIntegral ν K J I +
        (r / z - 1) ^ 2 * crossIntegral ν K J J / 2 := by
  let p := P.indicator (fun _ => (1 : ℝ))
  let i := I.indicator (fun _ => (1 : ℝ))
  let j := J.indicator (fun _ => (1 : ℝ))
  have hp : Integrable p ν := (integrable_const 1).indicator hP
  have hi : Integrable i ν := (integrable_const 1).indicator hI
  have hj : Integrable j ν := (integrable_const 1).indicator hJ
  have hsupp (C : Set Ω) : ∀ᵐ x ∂ν, x ∉ C → C.indicator (fun _ => (1 : ℝ)) x = 0 :=
    Eventually.of_forall (fun _ hx => indicator_of_notMem hx _)
  have hpp := MissingFlow.OneCenter.pairing_eq_const_of_supported K p p P P 0
    (hsupp P) (hsupp P) hPP
  have hii := MissingFlow.OneCenter.pairing_eq_const_of_supported K i i I I 0
    (hsupp I) (hsupp I) hII
  have hpi := MissingFlow.OneCenter.pairing_eq_const_of_supported K i p I P 0
    (hsupp I) (hsupp P) (hPK.mono (fun x hx h₁ h₂ => hx h₁ (Or.inl h₂)))
  have hpj := MissingFlow.OneCenter.pairing_eq_const_of_supported K j p J P 0
    (hsupp J) (hsupp P) (hPK.mono (fun x hx h₁ h₂ => hx h₁ (Or.inr h₂)))
  simp only [zero_mul] at hpp hii hpi hpj
  have hip : kernelPairing (μ := ν) K p i = 0 :=
    (kernelPairing_symm K hsym p i).trans hpi
  have hjp : kernelPairing (μ := ν) K p j = 0 :=
    (kernelPairing_symm K hsym p j).trans hpj
  let α := r / a - 1
  let β := r / z - 1
  let f := fun x => 1 + (-1) * p x
  let g := fun x => f x + α * i x
  have hf : Integrable f ν := (integrable_const 1).add (hp.const_mul (-1))
  have hg : Integrable g ν := hf.add (hi.const_mul α)
  have hw : weight P I J r a z = fun x => g x + β * j x := by
    funext x
    rw [weight_eq_indicators P I J hPI hPJ hIJ]
    dsimp [g, f, p, i, j, α, β]
    ring
  have hfE := energy_add_mul K hK hB hsym (fun _ => 1) p (integrable_const 1) hp (-1)
  have hgE := energy_add_mul K hK hB hsym f i hf hi α
  have hwE := energy_add_mul K hK hB hsym g j hg hj β
  have hfi := pairing_add_mul_left K hK hB (fun _ => 1) p i (integrable_const 1) hp hi (-1)
  have hfj := pairing_add_mul_left K hK hB (fun _ => 1) p j (integrable_const 1) hp hj (-1)
  have hgj := pairing_add_mul_left K hK hB f i j hf hi hj α
  change kernelEnergy (μ := ν) K p = 0 at hpp
  change kernelEnergy (μ := ν) K i = 0 at hii
  rw [hw, hwE, hgE, hfE, hgj, hfi, hfj, hpp, hii, hip, hjp,
    pairing_one_indicator K hK hB P hP, pairing_one_indicator K hK hB I hI,
    pairing_one_indicator K hK hB J hJ, pairing_indicator K J I hJ hI]
  rw [MissingFlow.OneCenter.energy_indicator K hJ]
  dsimp [α, β, crossIntegral]
  ring

/-- Internal old charge has the actual squared scaling of the entire J
under the child law. No current row is replaced by an old-law row. -/
theorem internal_under_law (K : Ω → Ω → ℝ)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) :
    (∫ p in J ×ˢ J, K p.1 p.2 ∂(law ν P I J).prod (law ν P I J)) =
      (halfMass ν P I J / ν.real J) ^ 2 * crossIntegral ν K J J := by
  let w := weight P I J (halfMass ν P I J) (ν.real I) (ν.real J)
  let j := J.indicator (fun _ => (1 : ℝ))
  have hw0 : ∀ᵐ x ∂ν, 0 ≤ w x :=
    Eventually.of_forall (weight_nonnegative P I J (halfMass_pos P I J ha hz).le ha.le hz.le)
  have he : (fun x => w x * j x) = fun x => (halfMass ν P I J / ν.real J) * j x := by
    funext x
    by_cases hx : x ∈ J
    · have hp : x ∉ P := fun hp => Set.disjoint_left.mp hPJ hp hx
      have hi : x ∉ I := fun hi => Set.disjoint_left.mp hIJ hi hx
      simp only [w, j, weight, hp, hi, hx, ↓reduceIte, indicator_of_mem hx, mul_one]
    · simp only [j, indicator_of_notMem hx, mul_zero]
  rw [← MissingFlow.OneCenter.energy_indicator K hJ]
  change kernelPairing (μ := weightedMeasure (μ := ν) w) K j j = _
  rw [kernelPairing_weightedMeasure w
    (integrable_weight P I J hP hI hJ _ _ _).aestronglyMeasurable.aemeasurable hw0 K j j, he]
  unfold kernelPairing
  have hf : (fun p : Ω × Ω => K p.1 p.2 *
      ((halfMass ν P I J / ν.real J) * j p.2) *
      ((halfMass ν P I J / ν.real J) * j p.1)) =
      fun p => (halfMass ν P I J / ν.real J) ^ 2 * (K p.1 p.2 * j p.2 * j p.1) := by
    funext p
    ring
  rw [hf, integral_const_mul]
  change (halfMass ν P I J / ν.real J) ^ 2 * kernelEnergy (μ := ν) K
    (J.indicator (fun _ => 1)) = _
  rw [MissingFlow.OneCenter.energy_indicator K hJ]
  rfl

/-- The literal signed child value before any original-row substitutions. -/
def physicalChildValue (ν : Measure Ω) (K : Ω → Ω → ℝ) (P I J : Set Ω) : ℝ :=
  kernelEnergy (μ := ν) K (weight P I J (halfMass ν P I J) (ν.real I) (ν.real J)) / 2 -
    (∫ p in J ×ˢ J, K p.1 p.2 ∂(law ν P I J).prod (law ν P I J)) / 2

/-- Exact current-law row accounting, including the entire old J-square
deletion. The coefficient is signed and is never replaced by a bound. -/
theorem physicalChildValue_expansion (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 0)
    (hII : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0)
    (hPK : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ I ∪ J → K p.1 p.2 = 0) :
    physicalChildValue ν K P I J =
      kernelEnergy (μ := ν) K (fun _ => 1) / 2 - rowIntegral ν K P +
        (halfMass ν P I J / ν.real I - 1) * rowIntegral ν K I +
        (halfMass ν P I J / ν.real J - 1) * rowIntegral ν K J +
        (halfMass ν P I J / ν.real I - 1) *
          (halfMass ν P I J / ν.real J - 1) * crossIntegral ν K J I -
        (ν.real I + ν.real P) * crossIntegral ν K J J / (2 * ν.real J) := by
  rw [physicalChildValue, energy_weight K hK hB hsym P I J hP hI hJ hPI hPJ hIJ
    hPP hII hPK, internal_under_law K P I J hP hI hJ hPJ hIJ ha hz]
  unfold halfMass
  field_simp [hz.ne']
  ring

/-- The shared cusp score follows from the literal current partial-endpoint
rows and the same hole identity. No child multiplier or independent budget
is introduced by these substitutions. -/
theorem cusp_score_of_rows (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (ν.prod ν))
    (hB : ∀ᵐ p ∂ν.prod ν, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂ν.prod ν, K p.1 p.2 = K p.2 p.1)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → K p.1 p.2 = 0)
    (hII : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → K p.1 p.2 = 0)
    (hPK : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ I ∪ J → K p.1 p.2 = 0)
    (a0 e ell gamma phi cI CJ Phi FJ qJ QO V Delta : ℝ)
    (hcurrent : kernelEnergy (μ := ν) K (fun _ => 1) / 2 =
      (1 - a0) * a0 ^ 2 + e + ell * Delta + V / 2)
    (hrowP : rowIntegral ν K P = ν.real P *
      (gamma + ell * (ν.real P + ν.real I + ν.real J) + phi))
    (hrowI : rowIntegral ν K I = ν.real I *
      (gamma + ell * (ν.real P + ν.real I) + phi - cI))
    (hrowJ : rowIntegral ν K J = ν.real J * (gamma + ell * ν.real P + phi) + ell * qJ - CJ)
    (hcross : crossIntegral ν K J I = ν.real I * (Phi - ell * ν.real J))
    (hinternal : crossIntegral ν K J J = FJ - ell * ((ν.real J) ^ 2 - qJ))
    (hhole : ell * Delta - ell * ((ν.real I) ^ 2 + qJ + (ν.real P) ^ 2 +
      2 * ν.real P * (ν.real I + ν.real J)) / 2 = ell * (QO - a0 ^ 2) / 2) :
    physicalChildValue ν K P I J - (halfMass ν P I J) ^ 2 =
      e + (2 - 2 * a0 - ell) * a0 ^ 2 / 2 + ell * QO / 2 + V / 2 +
        (ell - 1) * (ν.real P + ν.real I + ν.real J) ^ 2 / 4 -
        (halfMass ν P I J - ν.real I) * cI -
        ((halfMass ν P I J - ν.real J) / ν.real J) * CJ +
        ((halfMass ν P I J - ν.real I) * (halfMass ν P I J - ν.real J) / ν.real J) * Phi -
        (ν.real I + ν.real P) * FJ / (2 * ν.real J) := by
  rw [physicalChildValue_expansion K hK hB hsym P I J hP hI hJ hPI hPJ hIJ ha hz
    hPP hII hPK, hcurrent, hrowP, hrowI, hrowJ, hcross, hinternal]
  have hD : ell * Delta = ell * ((ν.real I) ^ 2 + qJ + (ν.real P) ^ 2 +
      2 * ν.real P * (ν.real I + ν.real J)) / 2 + ell * (QO - a0 ^ 2) / 2 := by
    linarith
  rw [hD]
  unfold halfMass
  field_simp [ha.ne', hz.ne']
  ring

variable {ι : Type*} [Countable ι] [StandardBorelSpace Ω] [NullSingletonClass ν]

local instance accountingOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- The actual full child, signed cusp score and same outside-square cost
bound are obtained together. Inputs are literal old graph blocks and
current partial-endpoint row identities; the child score and cost are not assumed. -/
theorem exists_child_with_cusp_score (W : Model Ω ν) (hW : FullFeasible W)
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (hAdj : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0)
    (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J → p.2 ∉ P →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (hblock : ∀ᵐ p ∂ν.prod ν, p.1 ∉ P → p.2 ∉ P → (p.1 ∉ J ∨ p.2 ∉ J) →
      A p.1 p.2 = outsideAdjacency q I J p.1 p.2)
    (hPP : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → A p.1 p.2 = false)
    (hPK : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ I ∪ J → A p.1 p.2 = false)
    (a0 e ell gamma phi cI CJ Phi FJ qJ V Delta : ℝ)
    (hcurrent : objective W = (1 - a0) * a0 ^ 2 + e + ell * Delta + V / 2)
    (hrowP : rowIntegral ν (chargeKernel W) P = ν.real P *
      (gamma + ell * (ν.real P + ν.real I + ν.real J) + phi))
    (hrowI : rowIntegral ν (chargeKernel W) I = ν.real I *
      (gamma + ell * (ν.real P + ν.real I) + phi - cI))
    (hrowJ : rowIntegral ν (chargeKernel W) J =
      ν.real J * (gamma + ell * ν.real P + phi) + ell * qJ - CJ)
    (hcross : crossIntegral ν (chargeKernel W) J I = ν.real I * (Phi - ell * ν.real J))
    (hinternal : crossIntegral ν (chargeKernel W) J J = FJ - ell * ((ν.real J) ^ 2 - qJ))
    (hhole : ell * Delta - ell * ((ν.real I) ^ 2 + qJ + (ν.real P) ^ 2 +
      2 * ν.real P * (ν.real I + ν.real J)) / 2 =
        ell * (outsideSquares ν q P I J - a0 ^ 2) / 2) :
    ∃ child : Model Ω (law ν P I J), FullFeasible child ∧
      objective child ≤ max ((halfMass ν P I J) ^ 2) (outsideSquares ν q P I J) ∧
      objective child - (halfMass ν P I J) ^ 2 =
        e + (2 - 2 * a0 - ell) * a0 ^ 2 / 2 + ell * outsideSquares ν q P I J / 2 + V / 2 +
          (ell - 1) * (ν.real P + ν.real I + ν.real J) ^ 2 / 4 -
          (halfMass ν P I J - ν.real I) * cI -
          ((halfMass ν P I J - ν.real J) / ν.real J) * CJ +
          ((halfMass ν P I J - ν.real I) * (halfMass ν P I J - ν.real J) / ν.real J) * Phi -
          (ν.real I + ν.real P) * FJ / (2 * ν.real J) := by
  have hzero : ∀ᵐ p ∂ν.prod ν, A p.1 p.2 = false → chargeKernel W p.1 p.2 = 0 := by
    filter_upwards [hAdj] with p hp hfalse
    have hlow := neg_three_adjacency_moment_le_charge W p
    have hhigh := charge_moment_le_adjacency W p
    rw [hfalse] at hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    rw [hp] at hlow hhigh
    change W.moment CappedColor.charge p = 0
    linarith
  have hPP' : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ P → chargeKernel W p.1 p.2 = 0 := by
    filter_upwards [hPP, hzero] with p hp hz hx hy
    exact hz (hp hx hy)
  have hPK' : ∀ᵐ p ∂ν.prod ν, p.1 ∈ P → p.2 ∈ I ∪ J → chargeKernel W p.1 p.2 = 0 := by
    filter_upwards [hPK, hzero] with p hp hz hx hy
    exact hz (hp hx hy)
  have hII' : ∀ᵐ p ∂ν.prod ν, p.1 ∈ I → p.2 ∈ I → chargeKernel W p.1 p.2 = 0 := by
    filter_upwards [hblock, hzero] with p hp hz hx hy
    have hxP : p.1 ∉ P := fun hxP => Set.disjoint_left.mp hPI hxP hx
    have hyP : p.2 ∉ P := fun hyP => Set.disjoint_left.mp hPI hyP hy
    have hxJ : p.1 ∉ J := fun hxJ => Set.disjoint_left.mp hIJ hx hxJ
    apply hz
    rw [hp hxP hyP (Or.inl hxJ)]
    simp only [outsideAdjacency, hx, hy, and_self, ↓reduceIte]
  obtain ⟨child, hchild, _, hvalue, hcost⟩ := exists_child_with_cost W hW A hA hAsym hAdj
    q hq P I J hP hI hJ hPI hPJ hIJ ha hz hjoin hblock
  refine ⟨child, hchild, hcost, ?_⟩
  have hvalue' : objective child = physicalChildValue ν (chargeKernel W) P I J := hvalue
  rw [hvalue']
  apply cusp_score_of_rows (chargeKernel W) (chargeKernel_measurable W) (chargeKernel_bound W)
    (chargeKernel_symm W) P I J hP hI hJ hPI hPJ hIJ ha hz hPP' hII' hPK'
    a0 e ell gamma phi cI CJ Phi FJ qJ (outsideSquares ν q P I J) V Delta
  · simpa only [kernelEnergy_one, chargeKernel, objective] using hcurrent
  · exact hrowP
  · exact hrowI
  · exact hrowJ
  · exact hcross
  · exact hinternal
  · exact hhole

end Erdos1017.CappedModel.WholeSourceChild
