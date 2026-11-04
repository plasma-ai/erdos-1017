module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassEditStructure
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassMeasurablePatch

/-!
# One prefix step as a single class patch

A finite prefix edits exactly the positive classes whose first label is at most
its cutoff, and editing the next positive class is one same-carrier patch of the
previous prefix when the finite labels encode the part index.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- A finite prefix edits exactly the positive common original classes
whose first label is at most its cutoff. -/
theorem prefixClassEdit_kernel_ite (W : Model Ω μ)
    (t : Ω → ℕ × ℕ) (ht : Measurable t) (m : ℝ)
    (hm : m ∈ Icc (-3 : ℝ) 1) (N : ℕ) (p : Ω × Ω) :
    (prefixClassEdit W t ht m hm N).kernel p =
      if 0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N then
        Measure.dirac (if (t p.1).2 = (t p.2).2 then CappedColor.absent
          else CappedColor.present m hm)
      else W.kernel p := by
  classical
  change (countableClassEdit W (truncatedClassLabels t N)
    (measurable_truncatedClassLabels t ht N) m hm).kernel p = _
  rw [countableClassEdit_kernel]
  by_cases hfirst : (t p.1).1 ≤ N
  · by_cases hsecond : (t p.2).1 ≤ N
    · simp [truncatedClassLabels, hfirst, hsecond]
    · have hne : (t p.1).1 ≠ (t p.2).1 := by omega
      have hcond : ¬(0 < (t p.1).1 ∧ (t p.1).1 = 0) := by omega
      simp [truncatedClassLabels, hfirst, hsecond, hne, hcond]
  · simp [truncatedClassLabels, hfirst]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- Editing the next positive class is exactly one same-carrier patch of
the previous finite prefix when its finite labels encode the part index. -/
theorem prefixClassEdit_succ_kernel_eq_patchZeroClass {k : ℕ}
    (W : Model Ω μ) (t : Ω → ℕ × ℕ) (ht : Measurable t)
    (m : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1) (N : ℕ)
    (L : Ω → Fin k) (hL : Measurable L)
    (hpart : ∀ x : Ω, (t x).1 = N + 1 → (L x).val = (t x).2)
    (p : Ω × Ω) :
    (prefixClassEdit W t ht m hm (N + 1)).kernel p =
      (patchZeroClass (prefixClassEdit W t ht m hm N)
        {x | (t x).1 = N + 1}
        (measurableSet_eq_fun ht.fst measurable_const) m hm L hL).kernel p := by
  classical
  rw [prefixClassEdit_kernel_ite, patchZeroClass_kernel,
    prefixClassEdit_kernel_ite]
  by_cases hnext : (t p.1).1 = N + 1 ∧ (t p.2).1 = N + 1
  · have hnew : 0 < (t p.1).1 ∧
        (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N + 1 := by
      omega
    have hold : ¬(0 < (t p.1).1 ∧
        (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N) := by
      omega
    have hlabel : (L p.1 = L p.2) ↔ (t p.1).2 = (t p.2).2 := by
      constructor
      · intro h
        rw [← hpart p.1 hnext.1, ← hpart p.2 hnext.2, h]
      · intro h
        apply Fin.ext
        rw [hpart p.1 hnext.1, hpart p.2 hnext.2, h]
    simp [hnext, hlabel]
  · have hiff :
        (0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N + 1) ↔
          (0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 ∧ (t p.1).1 ≤ N) := by
      omega
    simp [hnext, hiff]

end Erdos1017.CappedModel
