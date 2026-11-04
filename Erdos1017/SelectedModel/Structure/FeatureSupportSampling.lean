module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Continuous tests at feature support points

Coordinate support points lie in the support of the finite independent product
law, so a continuous test valid almost everywhere on an open feature condition
holds at every support point satisfying it, which licenses repeated limiting
feature types from a fixed physical clique test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology RealInnerProductSpace

namespace Erdos1017.FiniteArity

/-- Coordinate support points belong to the support of the actual finite
independent product law. Every open product neighborhood has positive mass. -/
theorem mem_support_pi_of_coordinate_support
    {ι E : Type*} [Fintype ι] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (ν : ι → Measure E) [∀ i, SigmaFinite (ν i)]
    (w : ι → E) (hw : ∀ i, w i ∈ (ν i).support) :
    w ∈ (Measure.pi ν).support := by
  classical
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨O, hOU, hO, hwO⟩ := mem_nhds_iff.mp hU
  obtain ⟨s, hs, hsO⟩ := isOpen_pi_iff'.mp hO w hwO
  have hpos (i : ι) : 0 < ν i (s i) :=
    (Measure.mem_support_iff_forall (w i)).mp (hw i) (s i) ((hs i).1.mem_nhds (hs i).2)
  calc
    0 < ∏ i, ν i (s i) := pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => (hpos i).ne'))
    _ = Measure.pi ν (univ.pi s) := (Measure.pi_pi ν s).symm
    _ ≤ Measure.pi ν U := measure_mono (hsO.trans hOU)

/-- A continuous test valid almost everywhere on an open feature condition
holds at every support point satisfying that condition. -/
theorem continuous_test_le_on_support
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (ν : Measure E) (Q : E → ℝ) (hQ : Continuous Q) (O : Set E) (hO : IsOpen O)
    (b : ℝ) (htest : ∀ᵐ x ∂ν, x ∈ O → Q x ≤ b)
    (w : E) (hw : w ∈ ν.support) (hwO : w ∈ O) : Q w ≤ b := by
  by_contra hnot
  have hlt : b < Q w := lt_of_not_ge hnot
  let U := O ∩ {x | b < Q x}
  have hU : IsOpen U := hO.inter (isOpen_lt continuous_const hQ)
  have hpos : 0 < ν U :=
    (Measure.mem_support_iff_forall w).mp hw U (hU.mem_nhds ⟨hwO, hlt⟩)
  have hzero : ν U = 0 := compl_mem_ae_iff.mp (htest.mono (fun x hx hmem =>
    (not_lt_of_ge (hx hmem.1)) hmem.2))
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- Actual restrictions of independent physical sampling license a continuous
feature test at arbitrary support points. The premise is an ordinary physical
product-almost-everywhere test, not a test on the feature support. -/
theorem continuous_test_le_of_restricted_feature_support
    {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [TopologicalSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → E) (hF : Measurable F)
    (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (Q : (ι → E) → ℝ) (hQ : Continuous Q)
    (O : Set (ι → E)) (hO : IsOpen O) (b : ℝ)
    (htest : ∀ᵐ v ∂Measure.pi (fun _ : ι => μ),
      (∀ i, v i ∈ s i) → (fun i => F (v i)) ∈ O → Q (fun i => F (v i)) ≤ b)
    (w : ι → E) (hw : ∀ i, w i ∈ ((μ.restrict (s i)).map F).support)
    (hwO : w ∈ O) : Q w ≤ b := by
  let ρ := Measure.pi (fun i => μ.restrict (s i))
  have hrestricted : ∀ᵐ v ∂ρ,
      (fun i => F (v i)) ∈ O → Q (fun i => F (v i)) ≤ b := by
    have ht : ∀ᵐ v ∂(Measure.pi (fun _ : ι => μ)).restrict (univ.pi s),
        (fun i => F (v i)) ∈ O → Q (fun i => F (v i)) ≤ b := by
      apply (ae_restrict_iff' (MeasurableSet.univ_pi hs)).mpr
      filter_upwards [htest] with v hv hvs
      exact hv (fun i => hvs i (mem_univ i))
    simpa only [Measure.restrict_pi_pi] using ht
  have hmap : Measurable (fun v : ι → Ω => fun i => F (v i)) :=
    Measurable.of_eval (fun i => hF.comp (measurable_pi_apply i))
  have hpush : ∀ᵐ v ∂Measure.pi (fun i => (μ.restrict (s i)).map F),
      v ∈ O → Q v ≤ b := by
    rw [← Measure.pi_map_pi (fun _ => hF.aemeasurable)]
    exact (ae_map_iff hmap.aemeasurable
      (show MeasurableSet {v : ι → E | v ∈ O → Q v ≤ b} from by
        convert hO.measurableSet.compl.union
          (measurableSet_le hQ.measurable (measurable_const (a := b))) using 1
        ext v
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or])).mpr hrestricted
  exact continuous_test_le_on_support _ Q hQ O hO b hpush w
    (mem_support_pi_of_coordinate_support _ w hw) hwO

/-- A fixed physical clique test licenses repeated limiting feature types.
Every repeated type is approached inside an actual measurable clique cell;
single-use types need no clique-cell hypothesis. Distinct occupied types have
strictly positive shifted pairing. Physical sampling is
independent throughout; no repeated physical vertex is inserted. -/
theorem tuple_test_le_of_feature_support
    {Ω E κ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (F : Ω → E) (hF : Measurable F) (J : E →ₗᵢ[ℝ] E) (ℓ : ℝ)
    (n : ℕ) (label : Fin n → κ) (C : κ → Set Ω) (hC : ∀ k, MeasurableSet (C k))
    (hclique : ∀ i j, i ≠ j → label i = label j → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ C (label i) → p.2 ∈ C (label i) → A p.1 p.2 = true)
    (hstrict : ∀ᵐ p ∂μ.prod μ, 0 < ⟪J (F p.1), F p.2⟫ → A p.1 p.2 = true)
    (hcharge : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = true → Y p.1 p.2 = ⟪J (F p.1), F p.2⟫ - ℓ)
    (htest : FeasibleOrder μ A Y n) (w : κ → E)
    (hw : ∀ i, w (label i) ∈ ((μ.restrict (C (label i))).map F).support)
    (hpositive : ∀ i j, i ≠ j → label i ≠ label j →
      0 < ⟪J (w (label i)), w (label j)⟫) :
    tupleCharge (fun x y : E => ⟪J x, y⟫ - ℓ) (fun i => w (label i)) ≤ 1 := by
  classical
  let Q : (Fin n → E) → ℝ := tupleCharge (fun x y : E => ⟪J x, y⟫ - ℓ)
  let O : Set (Fin n → E) :=
    {v | ∀ i j, i ≠ j → label i ≠ label j → 0 < ⟪J (v i), v j⟫}
  have hQ : Continuous Q := by
    unfold Q tupleCharge pairCharge crossSum
    apply Continuous.div_const
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact continuous_const
    · simp only [hij, ite_false]
      exact ((J.continuous.comp (continuous_apply i)).inner (continuous_apply j)).sub
        continuous_const
  have hO : IsOpen O := by
    simp only [O, ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
      isOpen_iInter_of_finite (fun _ => isOpen_iInter_of_finite (fun _ =>
        isOpen_lt continuous_const ((J.continuous.comp (continuous_apply i)).inner
          (continuous_apply j))))))
  apply continuous_test_le_of_restricted_feature_support μ F hF
    (fun i => C (label i)) (fun i => hC (label i)) Q hQ O hO 1 _
    (fun i => w (label i)) hw hpositive
  have hpairs := ae_all_pairs μ n (fun p =>
    (0 < ⟪J (F p.1), F p.2⟫ → A p.1 p.2 = true) ∧
      (A p.1 p.2 = true → Y p.1 p.2 = ⟪J (F p.1), F p.2⟫ - ℓ))
    (hstrict.and hcharge)
  have hsides : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i j, i ≠ j → label i = label j →
        v i ∈ C (label i) → v j ∈ C (label i) → A (v i) (v j) = true := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro hij
    apply ae_all_iff.mpr
    intro heq
    exact (measurePreserving_pair μ i j hij).quasiMeasurePreserving.ae (hclique i j hij heq)
  filter_upwards [htest, hpairs, hsides] with v hv hp hs
  intro hvs hvO
  have hc : TupleClique A v := by
    intro i j hij
    by_cases heq : label i = label j
    · exact hs i j hij heq (hvs i) (heq ▸ hvs j)
    · exact (hp i j hij).1 (hvO i j hij heq)
  have heq : Q (fun i => F (v i)) = tupleCharge Y v := by
    unfold Q tupleCharge
    congr 1
    funext i j
    by_cases hij : i = j
    · simp only [hij, ite_true]
    · simp only [hij, ite_false]
      exact ((hp i j hij).2 (hc i j hij)).symm
  rw [heq]
  exact hv hc

end Erdos1017.FiniteArity
