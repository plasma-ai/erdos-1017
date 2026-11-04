module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassPatchStep
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassInternalTuran

/-!
# Untreated classes under a finite prefix

A finite prefix leaves every pair untouched whose first endpoint lies beyond the
cutoff, so an untreated class keeps its original conditional color kernel,
restricted clique tests and color-moment integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A prefix leaves any pair untouched when its first endpoint belongs to
a class beyond the prefix cutoff. -/
theorem prefixClassEdit_kernel_eq_of_first_label_gt
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N : ℕ)
    (p : Ω × Ω) (hfirst : N < (t p.1).1) :
    (prefixClassEdit W t ht m hm N).kernel p = W.kernel p := by
  rw [prefixClassEdit_kernel_ite]
  have hnot : ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧
      (t p.1).1 ≤ N) := by
    intro h
    omega
  exact ite_eq_right hnot

omit [IsProbabilityMeasure μ] in
/-- Every pair in one untreated class retains the original conditional
color kernel at the finite prefix. -/
theorem prefixClassEdit_kernel_eq_of_unreached
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N i : ℕ) (hNi : N < i)
    (p : Ω × Ω) (hp1 : (t p.1).1 = i) (_hp2 : (t p.2).1 = i) :
    (prefixClassEdit W t ht m hm N).kernel p = W.kernel p := by
  exact prefixClassEdit_kernel_eq_of_first_label_gt W t ht m hm N p
    (hp1.symm ▸ hNi)

omit [IsProbabilityMeasure μ] in
/-- Every restricted clique test of an untreated class is exactly the
original test, including the empty clique order. -/
theorem restrictedCliquePresence_prefixClassEdit_eq_of_unreached
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N i : ℕ) (hNi : N < i)
    (j : ℕ) :
    restrictedCliquePresence (prefixClassEdit W t ht m hm N)
        {x | (t x).1 = i} j =
      restrictedCliquePresence W {x | (t x).1 = i} j := by
  let s : Set Ω := {x | (t x).1 = i}
  have hs : MeasurableSet s := measurableSet_eq_fun ht.fst measurable_const
  have hpi : MeasurableSet (Set.univ.pi (fun _ : Fin j => s)) :=
    MeasurableSet.pi countable_univ (fun _ _ => hs)
  have hLaw (x : Fin j → Ω) (hx : x ∈ Set.univ.pi (fun _ : Fin j => s)) :
      cliqueLaw (prefixClassEdit W t ht m hm N) x = cliqueLaw W x := by
    unfold cliqueLaw DecoratedKernel.sampleLaw
    congr 1
    funext e
    apply prefixClassEdit_kernel_eq_of_unreached W t ht m hm N i hNi
    · exact Set.mem_pi.mp hx _ (Set.mem_univ _)
    · exact Set.mem_pi.mp hx _ (Set.mem_univ _)
  unfold restrictedCliquePresence
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hpi] with x hx
  rw [hLaw x hx]

omit [IsProbabilityMeasure μ] in
/-- Every real color-moment integral over an untreated class square is
exactly its original value at the finite prefix. -/
theorem integral_moment_prefixClassEdit_eq_of_unreached
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N i : ℕ) (hNi : N < i)
    (f : CappedColor → ℝ) :
    (∫ p in {x | (t x).1 = i} ×ˢ {x | (t x).1 = i},
      (prefixClassEdit W t ht m hm N).moment f p ∂μ.prod μ) =
      ∫ p in {x | (t x).1 = i} ×ˢ {x | (t x).1 = i},
        W.moment f p ∂μ.prod μ := by
  have hs : MeasurableSet {x : Ω | (t x).1 = i} :=
    measurableSet_eq_fun ht.fst measurable_const
  have hsq : MeasurableSet
      ({x | (t x).1 = i} ×ˢ {x | (t x).1 = i}) := hs.prod hs
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hsq] with p hp
  change (∫ c, f c ∂(prefixClassEdit W t ht m hm N).kernel p) =
    ∫ c, f c ∂W.kernel p
  rw [prefixClassEdit_kernel_eq_of_unreached W t ht m hm N i hNi p hp.1 hp.2]

end Erdos1017.CappedModel
