module

public import Erdos1017.Models.Capped.CappedPairEdits
public import Erdos1017.Models.Capped.CappedGrowingLimit

/-!
# Simultaneous edits of countably many classes

This module defines the replacement color `classReplacementColor`, the
simultaneous edit `countableClassEdit` of countably many disjoint labeled
classes, and its finite prefixes; every finite vertex tuple sees the final edit
in a large enough prefix, so feasibility of all prefixes gives feasibility of
the simultaneous edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The first label identifies a class, with zero reserved for points outside
the classes. The second label identifies a part within that class. -/
def truncatedClassLabels (t : Ω → ℕ × ℕ) (N : ℕ) (x : Ω) : ℕ × ℕ :=
  if (t x).1 ≤ N then t x else (0, 0)

theorem measurable_truncatedClassLabels (t : Ω → ℕ × ℕ) (ht : Measurable t) (N : ℕ) :
    Measurable (truncatedClassLabels t N) :=
  ht.ite (measurableSet_le ht.fst measurable_const) measurable_const

open scoped Classical in
/-- Within a positive class, replace the old color by the complete multipartite
color on its part labels. Retain every other old color. -/
def classReplacementColor (t : Ω → ℕ × ℕ) (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1)
    (z : ((Ω × Ω) × CappedColor)) : CappedColor :=
  if 0 < (t z.1.1).1 ∧ (t z.1.1).1 = (t z.1.2).1 then
    if (t z.1.1).2 = (t z.1.2).2 then CappedColor.absent else CappedColor.present m hm
  else z.2

theorem measurable_classReplacementColor (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) : Measurable (classReplacementColor t m hm) := by
  classical
  have hfirst : Measurable (fun z : ((Ω × Ω) × CappedColor) => t z.1.1) :=
    ht.comp (measurable_fst.comp measurable_fst)
  have hsecond : Measurable (fun z : ((Ω × Ω) × CappedColor) => t z.1.2) :=
    ht.comp (measurable_snd.comp measurable_fst)
  exact (measurable_const.ite (measurableSet_eq_fun hfirst.snd hsecond.snd)
    measurable_const).ite
      ((measurableSet_lt measurable_const hfirst.fst).inter
        (measurableSet_eq_fun hfirst.fst hsecond.fst)) measurable_snd

omit [MeasurableSpace Ω] in
theorem classReplacementColor_symm (t : Ω → ℕ × ℕ) (m : ℝ)
    (hm : m ∈ Set.Icc (-3 : ℝ) 1) (p : Ω × Ω) (c : CappedColor) :
    classReplacementColor t m hm (p.swap, c) = classReplacementColor t m hm (p, c) := by
  classical
  by_cases h : 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1
  · have hswap : 0 < (t p.2).1 ∧ (t p.2).1 = (t p.1).1 :=
      ⟨h.2 ▸ h.1, h.2.symm⟩
    simp only [classReplacementColor, Prod.fst_swap, Prod.snd_swap,
      ite_eq_left h, ite_eq_left hswap]
    exact if_congr eq_comm rfl rfl
  · have hswap : ¬(0 < (t p.2).1 ∧ (t p.2).1 = (t p.1).1) := by
      rintro ⟨ha, heq⟩
      exact h ⟨heq ▸ ha, heq.symm⟩
    simp only [classReplacementColor, Prod.fst_swap, Prod.snd_swap,
      ite_eq_right h, ite_eq_right hswap]

/-- A simultaneous edit of countably many disjoint labelled classes, on the
original probability space. This definition alone asserts no feasibility. -/
def countableClassEdit (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) : Model Ω μ :=
  W.edit (classReplacementColor t m hm) (measurable_classReplacementColor t ht m hm)
    (Filter.Eventually.of_forall fun p c => classReplacementColor_symm t m hm p c)

/-- The finite-prefix edit changes only classes whose positive labels are at
most N. All prefixes use the same carrier and the same old model. -/
def prefixClassEdit (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) (N : ℕ) : Model Ω μ :=
  countableClassEdit W (truncatedClassLabels t N) (measurable_truncatedClassLabels t ht N) m hm

theorem prefixClassEdit_kernel_eq (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1) (N : ℕ) (p : Ω × Ω)
    (hfirst : (t p.1).1 ≤ N) (hsecond : (t p.2).1 ≤ N) :
    (prefixClassEdit W t ht m hm N).kernel p = (countableClassEdit W t ht m hm).kernel p := by
  change W.editKernel (classReplacementColor (truncatedClassLabels t N) m hm) p =
    W.editKernel (classReplacementColor t m hm) p
  rw [DecoratedKernel.editKernel_apply _ _ (measurable_classReplacementColor
      (truncatedClassLabels t N) (measurable_truncatedClassLabels t ht N) m hm),
    DecoratedKernel.editKernel_apply _ _ (measurable_classReplacementColor t ht m hm)]
  apply congrArg (Measure.map · (W.kernel p))
  funext c
  simp only [classReplacementColor, truncatedClassLabels,
    ite_eq_left hfirst, ite_eq_left hsecond]

/-- Every finite vertex tuple sees the final edit already in a sufficiently
large prefix, with equality of its actual independent conditional color laws. -/
theorem cliqueLaw_prefixClassEdit_eq (W : Model Ω μ) (t : Ω → ℕ × ℕ)
    (ht : Measurable t) (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1)
    {n : ℕ} (x : Fin n → Ω) (N : ℕ) (hN : ∀ i, (t (x i)).1 ≤ N) :
    cliqueLaw (prefixClassEdit W t ht m hm N) x =
      cliqueLaw (countableClassEdit W t ht m hm) x := by
  unfold cliqueLaw DecoratedKernel.sampleLaw
  congr 1
  funext e
  exact prefixClassEdit_kernel_eq W t ht m hm N _ (hN e.val.1) (hN e.val.2)

/-- Feasibility of every finite prefix implies feasibility of the simultaneous
edit. The prefix bound may depend on the sampled vertex tuple. -/
theorem fullFeasible_countableClassEdit (W : Model Ω μ) (t : Ω → ℕ × ℕ)
    (ht : Measurable t) (m : ℝ) (hm : m ∈ Set.Icc (-3 : ℝ) 1)
    (hprefix : ∀ N, FullFeasible (prefixClassEdit W t ht m hm N)) :
    FullFeasible (countableClassEdit W t ht m hm) := by
  intro r n hn hnr
  have htests : ∀ N, ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ᵐ c ∂cliqueLaw (prefixClassEdit W t ht m hm N) x, violation c = 0 :=
    fun N => hprefix N r n hn hnr
  filter_upwards [ae_all_iff.mpr htests] with x hx
  let N := Finset.univ.sup (fun i : Fin n => (t (x i)).1)
  have hN (i : Fin n) : (t (x i)).1 ≤ N := by
    exact Finset.le_sup (f := fun j : Fin n => (t (x j)).1) (Finset.mem_univ i)
  rw [← cliqueLaw_prefixClassEdit_eq W t ht m hm x N hN]
  exact hx N

end Erdos1017.CappedModel
