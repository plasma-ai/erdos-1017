module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopy

/-!
# Section laws for the independent atom copy

Splitting off one source point, or an old pair with fresh independent exterior
coordinates, preserves the sample law; countably many full old tests share one
product-almost-everywhere source-pair license, from which every
common-neighborhood root-copy test follows.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Splitting off one source point preserves the actual independent law. -/
theorem measurePreserving_cons (n : ℕ) :
    MeasurePreserving (fun p : Ω × (Fin n → Ω) => Fin.cons p.1 p.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  have hmp := MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0)
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', MeasurableEquiv.coe_mk, Equiv.coe_fn_mk] using hmp

/-- An old pair and fresh independent exterior coordinates give exactly
the ordinary old sample law. No joint physical parent law is used. -/
theorem measurePreserving_pairCons (n : ℕ) :
    MeasurePreserving
      (fun p : (Ω × Ω) × (Fin n → Ω) => Fin.cons p.1.1 (Fin.cons p.1.2 p.2))
      ((μ.prod μ).prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n + 2) => μ)) := by
  exact (measurePreserving_cons (μ := μ) (n + 1)).comp
    (((MeasurePreserving.id μ).prod (measurePreserving_cons (μ := μ) n)).comp
      (measurePreserving_prodAssoc μ μ (Measure.pi (fun _ : Fin n => μ))))

/-- Countably many full old tests have one common product-AE source-pair
license. Exceptional source points are never chosen independently of it. -/
theorem ae_all_pair_sections (P : ∀ n : ℕ, (Fin (n + 2) → Ω) → Prop)
    (hP : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin (n + 2) => μ), P n v) :
    ∀ᵐ p ∂μ.prod μ, ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      P n (Fin.cons p.1 (Fin.cons p.2 v)) := by
  rw [ae_all_iff]
  intro n
  exact Measure.ae_ae_of_ae_prod
    ((measurePreserving_pairCons (μ := μ) n).quasiMeasurePreserving.ae (hP n))

/-- Every actual common-neighborhood root-copy test follows from actual
full old tests and independence of the original root fiber. The source
pair and every exterior order share one product-AE license. -/
theorem ae_all_copy_root_tests
    (A : Ω → Ω → Bool) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (I : Set Ω)
    (hYsym : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = Y p.2 p.1)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hfull : ∀ n, FiniteArity.FeasibleOrder μ A Y n) :
    ∀ᵐ p ∂μ.prod μ, ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      A p.1 p.2 = true → 0 ≤ Y p.1 p.2 →
      FiniteArity.TupleClique A v →
      (∀ i, A p.1 (v i) = true ∧ A p.2 (v i) = true) →
      FiniteArity.tupleCharge (charge Y I p.1 p.2)
        (Fin.cons none (fun i => some (v i))) ≤ 1 := by
  have hpair : ∀ᵐ p ∂μ.prod μ,
      Y p.1 p.2 = Y p.2 p.1 ∧ (p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false) := by
    filter_upwards [hYsym, hI] with p hy hi
    exact ⟨hy, hi⟩
  have hsections := ae_all_pair_sections
    (fun n v => (FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) ∧
      (∀ i j, i ≠ j → Y (v i) (v j) = Y (v j) (v i) ∧
        (v i ∈ I → v j ∈ I → A (v i) (v j) = false)))
    (fun n => by
      filter_upwards [hfull (n + 2), FiniteArity.ae_all_pairs μ (n + 2) _ hpair]
        with v hv hp
      exact ⟨hv, hp⟩)
  filter_upwards [hsections] with p hp n
  filter_upwards [hp n] with v hv hxy hq hc hn
  have hclique : FiniteArity.TupleClique A (Fin.cons p.1 (Fin.cons p.2 v)) := by
    apply FiniteArity.TupleClique.cons p.1
    · exact hc.cons p.2 (fun i => (hn i).2) (fun i => (hsym _ _).trans (hn i).2)
    · intro i
      exact Fin.cases hxy (fun j => (hn j).1) i
    · intro i
      exact Fin.cases ((hsym _ _).trans hxy) (fun j => (hsym _ _).trans (hn j).1) i
  apply tupleCharge_copy_le_one Y I p.1 p.2 v
  · exact (hv.2 0 (0 : Fin (n + 1)).succ (Fin.succ_ne_zero _).symm).1.symm
  · intro i
    exact (hv.2 i.succ.succ 0 (by simp)).1
  · intro i
    exact (hv.2 i.succ.succ (0 : Fin (n + 1)).succ
      (fun he => Fin.succ_ne_zero i (Fin.succ_inj.mp he))).1
  · exact hq
  · intro i j hij
    rintro ⟨hi, hj⟩
    have hz := (hv.2 i.succ.succ j.succ.succ (by simpa using hij)).2 hi hj
    change A (v i) (v j) = false at hz
    rw [hc i j hij] at hz
    exact Bool.noConfusion hz
  · exact hv.1 hclique

end Erdos1017.IndependentAtomCopy
